package SPEED_POPL09;

class SPEED_POPL09_SimpleSingle2 {
    void SimpleSingle2(int n, int m) {
        boolean b = false;
        int R1 = 0;
        int R2 = 0;
        int x = 0;
        int y = 0;
        while (b) {
            if (x < n) {
                x = x + 1;
                y = y + 1;
                R1 = R1 + 1;
            } else if (y < m) {
                x = x + 1;
                y = y + 1;
                R2 = R2 + 1;
            } else break;
        }
    }
}
//Bound: n

