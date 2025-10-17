// ./Cuvee.sh examples/boogie/paper/override.bpl -annotate:traces -vcgen:partial -split -simplify2
procedure override(n: int)
    returns (a: [int]int)
    requires 0 <= n;
    ensures forall k: int :: 0 <= k && k < n ==> a[k + 1] == old(a[k]);
{
    var i: int := 0;

    while(i < n) {
        a[i + 1] := a[i];
        i := i + 1;
    }
}
