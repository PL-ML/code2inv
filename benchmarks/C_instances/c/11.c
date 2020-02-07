int main() {
  // variable declarations
  int x;
  int y;
  int z1;
  int z2;
  int z3;
  // pre-conditions
  assume((x >= 0));
  assume((x <= 10));
  assume((y <= 10));
  assume((y >= 0));
  // loop body
  while (unknown()) {
    {
    (x  = (x + 10));
    (y  = (y + 10));
    }

  }
  // post-condition
if ( (x == 20) )
assert( (y != 0) );

}
