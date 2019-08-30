method AddFriends(friends: nat)
  requires friends >= 1
{
    var R1 := 0;
    var R2 := 0;
    var i := 0;
    var identities := 0;
    while i < friends
        invariant identities == i
        invariant i <= friends
    {
        identities := identities + 1;
        i := i + 1;
    }
    identities := identities - 1;
    R1 := R1 + identities;
    assert R1 <= friends; // Bound
    assert 0 <= identities <= friends; // Global invariant
    identities := 0;
    identities := identities + 1;
    i := 0;
    while i < friends
    {
        R2 := R2 - identities;
        assert R2 <= 0; // Local invariant
        i := i + 1;
    }
    assert R2 <= 0; // Bound
}