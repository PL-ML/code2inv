int main() {
  // variable declarations
  int i;
  int x;
  int y;
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
