

int main() {
    int n, v1, v2, v3;
    int x = 1;
    int y;

    while (x <= n) {
        y = n - x;
        x = x +1;
    }

    if (n > 0) {
      //assert (y >= 0);
      assert (y < n);
    }
}
