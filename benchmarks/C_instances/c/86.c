int main() {
  // variable declarations
  int x;
  int y;
  int z1;
  int z2;
  int z3;
  // pre-conditions
  (x = -50);
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
