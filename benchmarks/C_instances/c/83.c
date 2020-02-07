int main() {
  // variable declarations
  int x;
  int y;
  // pre-conditions
  (x = -5000);
  // loop body
  while ((x < 0)) {
    {
    (x  = (x + y));
    (y  = (y + 1));
    }

  }
  // post-condition
assert( (y > 0) );
}
