int main() {
  // variable declarations
  int i;
  int x;
  int y;
  int z1;
  int z2;
  int z3;
  // pre-conditions
  (i = 0);
  assume((x >= 0));
  assume((y >= 0));
  assume((x >= y));
  // loop body
  while (unknown()) {
    if ( (i < y) )
    {
    (i  = (i + 1));
    }

  }
  // post-condition
if ( (i < y) )
assert( (i < x) );
}
