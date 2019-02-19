int main() {
  // variable declarations
  int i;
  int j;
  int x;
  int y;
  // pre-conditions
  (i = x);
  (j = y);
  // loop body
  while ((x != 0)) {
    {
    (x  = (x - 1));
    (y  = (y - 1));
    }

  }
  // post-condition
if ( (y != 0) )
assert( (i != j) );

}
