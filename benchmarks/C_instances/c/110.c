int main() {
  // variable declarations
  int i;
  int n;
  int sn;
  // pre-conditions
  (sn = 0);
  (i = 1);
  // loop body
  while ((i <= n)) {
    {
    (i  = (i + 1));
    (sn  = (sn + 1));
    }

  }
  // post-condition
if ( (sn != n) )
assert( (sn == 0) );

}
