int main() {
  // variable declarations
  int lock;
  int v1;
  int v2;
  int v3;
  int x;
  int y;
  // pre-conditions
  (x = y);
  (lock = 1);
  // loop body
  while ((x != y)) {
    {
      if ( unknown() ) {
        {
        (lock  = 1);
        (x  = y);
        }
      } else {
        {
        (lock  = 0);
        (x  = y);
        (y  = (y + 1));
        }
      }

    }

  }
  // post-condition
assert( (lock == 1) );
}
