package SPEED_PLDI09;

class SPEED_PLDI09_Example2 {
    int Example2(int n, int m, boolean b) {
        int R1 = 0;
        int R2 = 0;
        if (n > 0 && m > 0) {
            int v1 = n;
            int v2 = 0;
            while (v1 > 0 && b) {
                if (v2 < m) {
                    v2 = v2 + 1;
                    v1 = v1 - 1;
                    R1 = R1 + 1;
                } else {
                    v2 = 0;
                    R2 = R2 + 1;
                }
            }
        }
        return 0;
    }
}