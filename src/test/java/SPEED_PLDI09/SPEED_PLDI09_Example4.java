package SPEED_PLDI09;

class SPEED_PLDI09_Example4 {
    int Example4(int m, int n, boolean b ) {
        int R1 = 0;
        int R2 = 0;
        if (0 < m && m < n) {
            int i = n;
            while (i > 0 && b) {
                if (i < m) {
                    i = i - 1;
                    R1 = R1 + 1;
                }
                else {
                    i = i - m;
                    R2 = R2 + 1;
                }
            }
        }
        return 0;
    }
}