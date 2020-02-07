int main() {
  // variable declarations
  int i;
  int size;
  int sn;
  int v1;
  int v2;
  int v3;
  // pre-conditions
  (sn = 0);
  (i = 1);
  // loop body
  while ((i <= size)) {
    {
    (i  = (i + 1));
    (sn  = (sn + 1));
    }

  }
  // post-condition
if ( (sn != size) )
assert( (sn == 0) );

}
