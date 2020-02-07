int main() {
  // variable declarations
  int n;
  int x;
  // pre-conditions
  (x = 0);
  assume((n >= 0));
  // loop body
  while ((x < n)) {
    {
    (x  = (x + 1));
    }

  }
  // post-condition
assert( (x == n) );
}
