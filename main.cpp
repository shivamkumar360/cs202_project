#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Tooling/CompilationDatabase.h"
#include "clang/Analysis/CFG.h"
#include "llvm/Support/raw_ostream.h"
#include <vector>
#include <string>
#include <memory>
#include <fstream>
#include <optional>
#include <map>
#include <set>

using namespace clang;
using namespace clang::tooling;
using namespace std;

string escapeDotString(std::string str) {
    string out;
    for (char c : str) {
        if (c == '\"') out += "\\\"";
        else if (c == '\n') out += "\\n";
        else out += c;
    }
    return out;
}

struct Definition {
    int id;
    string varName;
    const Stmt* stmt;
    bool isUninit; // this boolean value will be true if there is something like "int x;" means only declared

    Definition(int i, string name, const Stmt* s, bool uninit)
        {
            this->id=i;
            this->varname=name;
            this->stmt=s;
            this->isUninit=uninit;

        }
};

class RDAnalyzer {
    CFG* cfg;
    ASTContext* context;
    FunctionDecl* FD;
    std::vector<Definition> allDefs;
    std::map<unsigned, std::set<int>> IN, OUT, GEN, KILL;
    std::set<unsigned> buggyBlocks;

public:
    RDAnalyzer(CFG* cfg, ASTContext* context, FunctionDecl* fd) 
        {
            this->cfg=cfg;
            this->context=context;
            this->FD=fd;


        }

    void analyze() {
        collectDefinitions();
        computeGenKill();
        runWorklist();
        checkUninitializedVariables();
    }

    bool hasBug(unsigned bid) 
    { 
        return buggyBlocks.count(bid);
    }
    std::set<int> getInSet(unsigned bid) 
    { 
        return IN[bid]; 
    }
    std::set<int> getOutSet(unsigned bid)
    { 
        return OUT[bid]; 
    }

private:
    void collectDefinitions() {

        int nextId = 1;
        unsigned entryId = cfg->getEntry().getBlockID();
        
        // this loop is making  parameters considered as already initialised

        for (auto* param : FD->parameters()) 
        {
            allDefs.push_back(Definition(nextId++, param->getNameAsString(), nullptr, false));
            GEN[entryId].insert(nextId - 1);
        }

        for (auto* block : *cfg) 
        {
            for (auto& elem : *block) 
            {
                if (std::optional<CFGStmt> cs = elem.getAs<CFGStmt>())
                {
                    const Stmt* s = cs->getStmt();
                    if (const BinaryOperator* bo = dyn_cast<BinaryOperator>(s)) 
                    {
                        if (bo->isAssignmentOp())
                        {
                            if (const DeclRefExpr* dre = dyn_cast<DeclRefExpr>(bo->getLHS()))
                                allDefs.push_back(Definition(nextId++, dre->getNameInfo().getAsString(), s, false));
                        }
                    } 
                    else if (const DeclStmt* ds = dyn_cast<DeclStmt>(s)) 
                    {
                        for (auto* D : ds->decls()) 
                        {
                            if (auto* vd = dyn_cast<VarDecl>(D)) 
                            {
                                // Capture BOTH initialized and uninitialized declarations
                                allDefs.push_back(Definition(nextId++, vd->getNameAsString(), s, !vd->hasInit()));
                            }
                        }
                    }
                }
            }
        }
    }

    void computeGenKill() // compute kill definitions
    {
        for (auto* block : *cfg) 
        {
            unsigned bid = block->getBlockID();
            std::map<std::string, int> lastDefInBlock;
            for (auto& elem : *block)
            {
                if (std::optional<CFGStmt> cs = elem.getAs<CFGStmt>()) 
                {
                    for (auto& d : allDefs) 
                    {
                        if (d.stmt == cs->getStmt()) lastDefInBlock[d.varName] = d.id;
                    }
                }
            }
            for (auto const& [var, id] : lastDefInBlock) 
            {
                GEN[bid].insert(id);
                for (auto& other : allDefs) 
                {
                    if (other.varName == var && other.id != id) KILL[bid].insert(other.id);
                }
            }
        }
    }

    void runWorklist() // runworklist function
    {
        bool changed = true;
        while (changed) {
            changed = false;
            for (auto* block : *cfg) {
                unsigned bid = block->getBlockID();
                std::set<int> newIn;
                for (auto& pred : block->preds())
                    if (pred) newIn.insert(OUT[pred->getBlockID()].begin(), OUT[pred->getBlockID()].end());
                IN[bid] = newIn;

                std::set<int> oldOut = OUT[bid];
                std::set<int> diff;
                for (int id : IN[bid]) if (KILL[bid].find(id) == KILL[bid].end()) diff.insert(id);
                diff.insert(GEN[bid].begin(), GEN[bid].end());
                OUT[bid] = diff;
                if (OUT[bid] != oldOut) changed = true;
            }
        }
    }

    void checkUninitializedVariables() // checking uninitialised variables
    {
        for (auto* block : *cfg) {
            std::set<int> currentReached = IN[block->getBlockID()];
            for (auto& elem : *block) {
                if (std::optional<CFGStmt> cs = elem.getAs<CFGStmt>()) {
                    const Stmt* s = cs->getStmt();
                    
                    // Logic: Ignore LHS of assignments, check everything else


                    if (const BinaryOperator* bo = dyn_cast<BinaryOperator>(s)) {
                        if (bo->isAssignmentOp()) {
                            if (checkStmtInternal(bo->getRHS(), currentReached)) buggyBlocks.insert(block->getBlockID());
                        } else {
                            if (checkStmtInternal(s, currentReached)) buggyBlocks.insert(block->getBlockID());
                        }
                    } else {
                        if (checkStmtInternal(s, currentReached)) buggyBlocks.insert(block->getBlockID());
                    }

                    // update reached set line-by-line


                    for (auto& d : allDefs) {
                        if (d.stmt == s) {
                            std::set<int> nextReached;
                            for (int id : currentReached) {
                                bool killed = false;
                                for (auto& other : allDefs) 
                                    if (other.id == id && other.varName == d.varName) killed = true;
                                if (!killed) nextReached.insert(id);
                            }
                            nextReached.insert(d.id);
                            currentReached = nextReached;
                        }
                    }
                }
            }
        }
    }

    bool checkStmtInternal(const Stmt* s, const std::set<int>& reaching) {
        if (const DeclRefExpr* dre = dyn_cast<DeclRefExpr>(s)) {
            if (const VarDecl* vd = dyn_cast<VarDecl>(dre->getDecl())) {
                if (vd->hasGlobalStorage() || isa<FunctionDecl>(dre->getDecl())) return false;
                
                std::string name = vd->getNameAsString();
                bool foundSafeDef = false;
                bool foundUninitDef = false;

                for (int id : reaching) {
                    for (auto& d : allDefs) {
                        if (d.id == id && d.varName == name) {
                            if (d.isUninit) foundUninitDef = true;
                            else foundSafeDef = true;
                        }
                    }
                }
                // it's a bug if an uninitialized definition reaches OR if no definition reaches
                if (foundUninitDef || !foundSafeDef) return true;
            }
        }
        for (const Stmt* child : s->children()) if (child && checkStmtInternal(child, reaching)) return true;
        return false;
    }
};

class MyVisitor : public RecursiveASTVisitor<MyVisitor> {
    ASTContext *Context;
    std::ofstream &dotFile;
public:
    explicit MyVisitor(ASTContext *Context, std::ofstream &out) : Context(Context), dotFile(out) {}

    bool VisitFunctionDecl(FunctionDecl *Declaration) {
        if (Declaration->hasBody()) {
            std::string funcName = Declaration->getNameInfo().getAsString();
            std::unique_ptr<CFG> cfg = CFG::buildCFG(Declaration, Declaration->getBody(), Context, CFG::BuildOptions());
            if (cfg) {
                RDAnalyzer analyzer(cfg.get(), Context, Declaration);
                analyzer.analyze();

                dotFile << "  subgraph cluster_" << funcName << " {\n";
                dotFile << "    label = \"" << funcName << "()\";\n";
                dotFile << "    style=filled; color=lightgrey;\n";

                for (auto *Block : *cfg) {
                    int id = Block->getBlockID();
                    std::string nodeName = funcName + "_Node" + std::to_string(id);
                    std::string color = analyzer.hasBug(id) ? "red" : "white";
                    
                    dotFile << "    " << nodeName << " [label=\"Block " << id << "\\n";
                    if (analyzer.hasBug(id)) dotFile << "!!! POTENTIAL UNINIT BUG !!!\\n";
                    dotFile << "IN: { ";
                    for (int rdaId : analyzer.getInSet(id)) dotFile << "d" << rdaId << " ";
                    dotFile << "}\\n----------------\\n";
                    for (auto& elem : *Block) {
                        if (auto cs = elem.getAs<CFGStmt>()) {
                            std::string s; llvm::raw_string_ostream os(s);
                            cs->getStmt()->printPretty(os, nullptr, Context->getLangOpts());
                            dotFile << escapeDotString(s) << "\\n";
                        }
                    }
                    dotFile << "----------------\\nOUT: { ";
                    for (int rdaId : analyzer.getOutSet(id)) dotFile << "d" << rdaId << " ";
                    dotFile << "}\", style=filled, fillcolor=" << color << "];\n";

                    for (auto& succ : Block->succs())
                        if (succ) dotFile << "    " << nodeName << " -> " << funcName << "_Node" << succ->getBlockID() << ";\n";
                }
                dotFile << "  }\n";
            }
        }
        return true;
    }
};

class MyConsumer : public ASTConsumer {
public:
    void HandleTranslationUnit(ASTContext &Context) override {
        std::ofstream dotFile("program_cfg.dot");
        dotFile << "digraph ProgramCFG {\n  node [shape=box, fontname=\"Courier\"];\n";
        MyVisitor Visitor(&Context, dotFile);
        Visitor.TraverseDecl(Context.getTranslationUnitDecl());
        dotFile << "}\n";
    }
};



class MyAction : public ASTFrontendAction {
public:
    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override { return std::make_unique<MyConsumer>(); }
};

int main(int argc, const char **argv) {
    if (argc < 2) return 1;
    FixedCompilationDatabase Code(".", {"-xc", "-std=c11"});
    ClangTool Tool(Code, {argv[1]});
    return Tool.run(newFrontendActionFactory<MyAction>().get());
}

