int main() {
  // variable declarations
  int c;
  int n;
  int v1;
  int v2;
  int v3;
  // pre-conditions
  (c = 0);
  assume((n > 0));
  // loop body
  while (unknown()) {
    {
      if ( unknown() ) {
        if ( (c != n) )
        {
        (c  = (c + 1));
        }
      } else {
        if ( (c == n) )
        {
        (c  = 1);
        }
      }

    }

  }
  // post-condition
if ( (n > -1) )
assert( (c != n) );

}
