int main() {
  // variable declarations
  int x;
  // pre-conditions
  (x = 10000);
  // loop body
  while ((x > 0)) {
    {
    (x  = (x - 1));
    }

  }
  // post-condition
assert( (x == 0) );
}
