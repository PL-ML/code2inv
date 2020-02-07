int main()
{
  unsigned int n;
  assume(n >= 0);
  int x=n, y=0;
  while(x>0)
  {
    x--;
    y++;
  }
  assert(y==n);
}
