
int main() {
    int n,y;
    int x = 1;

    while (x <= n) {
        y = n - x;
        x = x +1;
    }

    if (n > 0) {
        assert (y >= 0);
        //assert (y <= n);
    }
}
