int main() {
  // variable declarations
  int x;
  // pre-conditions
  (x = 0);
  // loop body
  while ((x < 100)) {
    {
    (x  = (x + 1));
    }

  }
  // post-condition
assert( (x == 100) );
}
