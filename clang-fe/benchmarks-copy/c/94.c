int main() {
  // variable declarations
  int i;
  int j;
  int k;
  int n;
  // pre-conditions
  assume((k >= 0));
  assume((n >= 0));
  (i = 0);
  (j = 0);
  // loop body
  while ((i <= n)) {
    {
    (i  = (i + 1));
    (j  = (j + i));
    }

  }
  // post-condition
assert( ((i + (j + k)) > (2 * n)) );
}
