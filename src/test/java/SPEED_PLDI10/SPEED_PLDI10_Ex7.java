package SPEED_PLDI10;

class SPEED_PLDI10_Ex7 {
    int foo(int n, int m) {
        int R1 = 0;
        int R2 = 0;
        if (0 < n && n < m) {
            int j = n + 1;
            while (j < n || j > n) {
                if (j > m) {
                    j = 0;
                    R1 = R1 + 1;
                }
                else {
                    j = j + 1;
                    R2 = R2 + 1;
                }
            }
        }
        return 0;
    }
}