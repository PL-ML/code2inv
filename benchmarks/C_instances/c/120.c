int main() {
  // variable declarations
  int i;
  int sn;
  // pre-conditions
  (sn = 0);
  (i = 1);
  // loop body
  while ((i <= 8)) {
    {
    (i  = (i + 1));
    (sn  = (sn + 1));
    }

  }
  // post-condition
if ( (sn != 8) )
assert( (sn == 0) );

}
