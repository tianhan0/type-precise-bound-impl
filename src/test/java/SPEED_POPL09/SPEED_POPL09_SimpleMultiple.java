class SPEED_POPL09_SimpleMultiple {
    void SimpleMultiple(int n, int m) {
        int x = 0;
        int y = 0;
        int R1 = 0;
        int R2 = 0;
        while (x < n) {
            if (y < m) {
                y = y + 1;
                R1 = R1 + 1;
            }
            else {
                x = x + 1;
                R2 = R2 + 1;
            }
        }
    }
}
//Bound: ?
//Remark: identical to Dis1.c

