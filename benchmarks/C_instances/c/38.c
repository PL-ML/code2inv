
int main() {
    int n;
    int c = 0;
    assume (n > 0);

    while (unknown()) {
        if(c == n) {
            c = 1;
        }
        else {
            c = c + 1;
        }
    }

    if(c == n) {
        assert( c >= 0);
        //assert( c <= n);
    }
}
