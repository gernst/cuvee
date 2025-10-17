// ./Cuvee.sh examples/boogie/paper/shift.bpl -annotate:traces -vcgen:partial -split -simplify2
procedure shift(n: int)
    returns (a: [int]int)
    requires 0 <= n;
    ensures forall k: int :: 0 <= k && k < n ==> a[k] == old(a[k + 1]);
{
    var i: int := 0;

    while(i < n) {
        a[i] := a[i + 1];
        i := i + 1;
    }
}
