package SPEED_PLDI09;

class SPEED_PLDI09_Example6 {
    int Example6(int m, int n, boolean b) {
        int i = 0;
        int j = 0;
        int k = 0;
        int R1 = 0;
        int R2 = 0;
        while (i < n) {
            i = i + 1;
            if (b) {
                while (j < m) {
                    j = j + 1;
                    R1 = R1 + 1;
                }
            }
            else {
                while (k < m) {
                    k = k + 1;
                    R2 = R2 + 1;
                }
            }
        }
        return 0;
    }
}

//Bound: n + 2m

