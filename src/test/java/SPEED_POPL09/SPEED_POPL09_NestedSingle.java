
class SPEED_POPL09_NestedSingle {
    void NestedSingle(int n, boolean b) {
        int x = 0;
        int R1 = 0;
        while (x < n) {
            while (x < n && b) {
                x = x + 1;
                R1 = R1 + 1;
            }
            x = x + 1;
        }
    }
}
//Bound: n

