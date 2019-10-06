package SPEED_PLDI09;

class SPEED_PLDI09_Example3 {
    int Example3(int n, int m, boolean b) {
        int R1 = 0;
        int R2 = 0;
        if (0 < m && m < n) {
            int i = 0;
            int j = 0;
            while (i < n && b) {
                if (j < m) {
                    j = j + 1;
                    R1 = R1 + 1;
                }
                else {
                    j = 0;
                    i = i + 1;
                    R2 = R2 + 1;
                }
            }
        }
        return 0;
    }
}