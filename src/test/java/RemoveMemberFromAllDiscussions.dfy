method removeMemberFromAllDiscussions(n: nat)
{
    var R := 0;
    var i := 0;
    while i < n
        invariant R <= i
        invariant i <= n
    {
        i := i + 1;
        R := R + 1;
        assert R <= i; // Local invariant
    }
    assert i <= n; // Global invariant
    assert R <= n; // Bound
}