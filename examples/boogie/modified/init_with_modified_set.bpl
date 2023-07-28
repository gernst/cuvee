procedure init(z: int, n: int)
    returns (a: [int]int)
    requires 0 <= n;
    // ensures  forall k: int :: 0 <= k && k < n ==> a[k] == z;
{
    var i: int := 0;

    var b: int;
    var c: int;

    var M: [int]bool;
    assume forall x: int :: M[x] == false;

    while(i < n)
        decreases n - i;
        invariant 0 <= i && i <= n;
        invariant forall x: int :: M[x] <==> exists i_: int :: x == i_ + c && 0 <= i_ && i_ < i;
        invariant forall x: int :: M[x]  ==> exists i_: int :: x == i_ + c && a[x] == (i_ + b);
    {
        a := a[i + c := (i + b)];
        M := M[i + c := true];
        i := i + 1;
    }
}
