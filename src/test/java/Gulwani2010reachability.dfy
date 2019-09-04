method ex1(n: nat, b: bool)
  requires n>0
{
    var n_ := n;
    var i := 0;
    var R := 0;
    var j := 0;
    while i<n_
      invariant i>=0
      invariant n_>0
      decreases n-i
      invariant R+n_<=n+1
    {
        j := i+1;
        while j<n_
          invariant R+n_<=n+1
          invariant j>0
          invariant n_>0
          decreases n_-j
        {
            if(b)
            {
                R := R+1;
                j := j-1;
                n_ := n_-1;
                assert R+n_<=n+1; // Local invariant
            }
            j := j+1;
        }
        i := i+1;
    }
    assert n_>0; // Global invariant
    assert R<=n+1; // Bound
}



method ex2(n: nat, m: nat, b: bool)
  requires m>=0
  requires n>=0
{
    var R := 0;
    var n_ := n;
    var m_ := m;
    while n_>0 && m_>0
      invariant R+n_<=n
      invariant n_>=0
    {
        n_ := n_-1;
        m_ := m_-1;
        while b
          invariant R+n_<=n // Loop may not terminate!
        {
            n_ := n_-1;
            m_ := m_+1;
            R := R+1;
            assert R+n_<=n; // Local invariant
        }
    }
    assert n_>=0; // Global invariant
    assert R<=n; // Bound
}


method ex3(n: nat, b: bool) {
    var t := false;
    var R := 0;
    var n_ := n;
    while n_>0
        invariant R+n_<=n
        invariant n_>=0
    {
        t := b;
        while n_>0 && t==b
            invariant R+n_<=n
            invariant n_>=0
        {
            n_ := n_-1;
            R := R+1;
            assert R+n_<=n; // Local invariant
        }
    }
    assert n_>=0;// Global invariant
    assert R<=n; // Bound
}




method ex4(n: int, b: bool)
    requires n>=0
{
    var flag := true;
    var n_ := n;
    var R := 0;
    while flag
        invariant R+n_<=n // Loop may not terminate!
    {
        flag := false;
        while n_>0 && b
            invariant R+n_<=n
        {
            n_ := n_-1;
            flag :=true;
            R := R+1;
            assert R+n_<=n; // Local invariant
        }
    }
    assert n_>=0; // Global invariant
    assert R<=n; // Bound
}



method ex5(n: int, b1: bool, b2: bool)
  requires n>=0
{
    var i := 0;
    var n_ := n;
    var flag := false;
    var R := 0;
    while i<n
        invariant n_>=0
        invariant i>=0
        invariant R+n_<=n
    {
        flag := false;
        while (b1)
            invariant R+n_<=n // Loop may not terminate!
        {
            if (b2) {
                flag := true;
                n_ := n_-1;
                R := R+1;
                assert R+n_<=n;
            }
        }
        if (!flag) {
            i := i+1;
        }
    }
    assert i>=0; // Global invariant
    assert n_>=0; // Global invariant
    assert R<=n; // Bound
}



method ex6(n: int, x: int, z: int)
{
    var R1 := 0;
    var R2 := 0;
    var x_ := x;
    var z_ := z;
    while x_<n
    {
        if (z_>x_) {
            x_ := x_+1;
            R1 := R1+1;
            assert R1==x_-x;
        } else {
            z=z+1;
            R2=R2+1;
            assert R2==z_-z;
        }
    }
    assert R1+R2<=n-x+n-y; // Bound
}