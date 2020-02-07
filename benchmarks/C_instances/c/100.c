int main() {
  // variable declarations
  int n;
  int x;
  int y;
  // pre-conditions
  assume((n >= 0));
  (x = n);
  (y = 0);
  // loop body
  while ((x > 0)) {
    {
    (y  = (y + 1));
    (x  = (x - 1));
    }

  }
  // post-condition
assert( (y == n) );
}
