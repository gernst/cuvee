// ./Cuvee.sh examples/boogie/paper/init3.bpl -annotate:traces -vcgen:partial -split -simplify2
procedure init(n: int)
    returns (a: [int]int)
    requires 0 <= n;
    ensures  forall j: int :: 0 <= j && j < n ==> a[j] == j;
{
    var i: int := 0;
    var j: int := 0;

    while(i < n) {
        a[i] := j;
        j := j + 1;
        i := i + 1;
    }
}
