method CommandCompleter(n: nat, m: nat, b: bool) {
    var R1 := 0;
    var R2 := 0;
    var i := 0;
    var k := 0;
    while i < n
        invariant i==k
        invariant i<=n
    {
        i := i + 1;
        k := k + 1;
    }
    assert k <= n; // Global invariant
    if (b) {
        R1 := R1 + k;
        assert R1 <= n; // Local invariant
    } else {
        var j := 0;
        while j < k
            invariant j >= R2
            invariant j <= k
        {
            if (b) {
                R2 := R2 + 1;
                assert j >= R2; // Local invariant
            }
            j := j+1;
        }
        assert j<=n; // Global invariant
    }
    assert R1 + R2 <= 2*n; // Bound
}