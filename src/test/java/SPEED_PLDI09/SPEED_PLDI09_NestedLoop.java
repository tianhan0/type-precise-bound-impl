package SPEED_PLDI09;

class SPEED_PLDI09_NestedLoop {
    void nestedLoop(int n, int m, int N, boolean b) {
        int R1 = 0;
        if (0 <= n && 0 <= m && 0 <= N) {
            int i = 0;
            while (i < n && b) {
                int j = 0;
                while (j < m && b) {
                    j = j + 1;
                    int k = i;
                    while (k < N && b) {
                        k = k + 1;
                        R1 = R1 + 1;
                    }
                    i = k;
                }
                i = i + 1;
            }
        }
    }
}

//Bound: n + (m * n) + N

