method replaceTagsBuilderHelper(len: nat, r1: nat, r2: nat, r3: nat)
    requires 0 < r3 <= r2
    requires r1 > 0
    requires r2 > 0
{
    var R1 := 0;
    var R2 := 0;
    var R3 := 0;
    var linePointer := 0;
    var startTagLocation := 0;
    var endTagLocation := 0;
    while endTagLocation < len
        // invariant startTagLocation <= endTagLocation // Local invariant
        invariant linePointer >= 0 // Global invariant
        invariant startTagLocation >= 0 // Global invariant
        invariant endTagLocation >= 0 // Global invariant
        invariant linePointer == endTagLocation // Local invariant
        invariant R1+R2 <= endTagLocation // Local invariant
    {
        startTagLocation := endTagLocation+r1;
        endTagLocation := startTagLocation+r2;
        // assert startTagLocation-linePointer==r1;
        if (endTagLocation < len) {
            R1 := R1+startTagLocation-linePointer;
            R2 := R2+r3;
            // assert r1+r3<=endTagLocation-linePointer;
            // assert R1+R2 <= endTagLocation;
            assert R1+R2 <= len; // Bound
        }
        linePointer := endTagLocation;
    }
    assert linePointer>=0; // Global invariant
    R3 := R3+len-linePointer;
    assert R3<=len; // Bound
}
