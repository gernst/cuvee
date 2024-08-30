procedure init(n: int)
    returns (a: [int]int, b: [int]int)
    requires 0 <= n;
{
    var i: int := 0;
    while(i < n)
        decreases n - i;
        invariant 0 <= i && i <= n;
        invariant forall x: int, y: int ::
            ((0 <= x && x < i) 
                ==> (exists z: int :: a[x] == z)) &&
            ((0 <= y && y < i) 
                ==> (exists z: int :: b[y] == z));
    {
        var z: int;
        var p: bool;

        assume z >= 0;
        assume a[i] != b[i];

        if(p) { a[i] :=  z };
        if(p) { b[i] :=  z };

        a[i] := z;
        b[i+1] := z;
        a[i+1] := 0;
        
        i := i + 1;
    }

    assert forall i ...
        a[i] == b[i] ==> a[i] >= z
}
