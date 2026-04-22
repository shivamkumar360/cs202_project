cmake_minimum_required(VERSION 3.10)
project(CFGTool)

set(CMAKE_CXX_STANDARD 17)

# Find system dependencies
find_package(PkgConfig REQUIRED)
pkg_check_modules(ZSTD REQUIRED libzstd)

find_package(LLVM REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)

include_directories(${LLVM_INCLUDE_DIRS} ${CLANG_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})
add_definitions(${LLVM_DEFINITIONS})

add_executable(cfg-tool main.cpp)

# Use the overarching LLVM shared library to avoid "Option registered more than once"
target_link_libraries(cfg-tool
  PRIVATE
  clangTooling
  clangFrontend
  clangAnalysis
  clangAST
  clangSerialization
  clangBasic
  LLVM  # This links to the single libLLVM.so which prevents duplicate registration
  ${ZSTD_LIBRARIES}
)