int main() {
    int a = 10 + 20; // Folded: 30
    return a;

    int b = 50;      // This block should be gray (unreachable)
    return b;
}