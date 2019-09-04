method ex01(n: nat, b: bool)
{
    var i := 0;
    var j := 0;
    var R := 0;
    while i<n
        invariant i<=n;
        invariant R<=i;
        // decreases n-i;
    {
        i := i+1;
        j := 0;
        while i<n && b
            invariant i<=n;
            invariant R<=i;
            // decreases n-i
        {
            i := i+1;
            j := j+1;
            R := R+1;
            assert R<=i; // Local invariant
        }
        // While Dafny fails to prove termination of this program (if the following block is uncommented), our approach does not need to prove termination
        /*if (j>0)
        {
            i := i-1;
        }*/
    }
    assert i<=n; // Global invariant
    assert R<=n; // Bound
}

