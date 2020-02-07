int main() {
  // variable declarations
  int n;
  int x;
  // pre-conditions
  (x = n);
  // loop body
  while ((x > 0)) {
    {
    (x  = (x - 1));
    }

  }
  // post-condition
if ( (n >= 0) )
assert( (x == 0) );

}
