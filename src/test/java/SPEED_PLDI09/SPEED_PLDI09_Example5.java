package SPEED_PLDI09;

class SPEED_PLDI09_Example5 {
    int Example5(int m, int n, int dir, int fwd) {
        int R1 = 0;
        int R2 = 0;
        if (0 < m && m < n) {
            int i = m;
            while (0 < i && i < n) {
                if (dir == fwd) {
                    i = i + 1;
                    R1 = R1 + 1;
                }
                else {
                    i = i - 1;
                    R2 = R2 + 1;
                }
            }
        }
        return 0;
    }
}

//Bound: max(m, n-m)

