
class SPEED_POPL09_NestedMultiple {
    void NestedMultiple(int x, int y, int n, int m, boolean b) {
        int x0 = x;
        int y0 = y;
        int R1 = 0;
        // int R2 = 0;
        while (x0 < n) {
            while (y0 < m && b) {
                y0 = y0 + 1;
                R1 = R1 + 1;
            }
            x0 = x0 + 1;
        }
    }
}
//Bound: 
