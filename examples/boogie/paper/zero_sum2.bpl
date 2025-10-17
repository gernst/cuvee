// ./Cuvee.sh examples/boogie/paper/zero_sum2.bpl -annotate:traces -vcgen:partial -split -simplify2
procedure zero_sum(a: [int]int, n: int)
  requires 1 < n;
{
  var sum: int := 0;

  var i: int := 0;
  while(i < n) {
    sum := sum + a[i];
    i := i + 1;
  }
  i := 0;
  while(i < n) {
    sum := sum - a[i];
    i := i + 1;
  }
  assert sum == 0;
}

