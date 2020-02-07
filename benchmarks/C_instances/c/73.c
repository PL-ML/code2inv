int main() {
  // variable declarations
  int c;
  int y;
  int z;
  // pre-conditions
  (c = 0);
  assume((y >= 0));
  assume((y >= 127));
  (z = (36 * y));
  // loop body
  while (unknown()) {
    if ( (c < 36) )
    {
    (z  = (z + 1));
    (c  = (c + 1));
    }

  }
  // post-condition
if ( (z < 0) )
if ( (z >= 4608) )
assert( (c >= 36) );

}
