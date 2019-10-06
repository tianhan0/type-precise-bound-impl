package SPEED_CAV09;

class SPEED_CAV09_ex2 {
    int foo(int n, int m) {
        int R1 = 0;
        int R2 = 0;
        int x = 0;
        int y = 0;
        while (x < n) {
            if (y < m) {
                y = y + 1;
                R1 = R1 + 1;
            }
            else {
                y = 0;
                x = x + 1;
                R2 = R2 + 1;
            }
        }
        return 1;
    }
}

//bound according to paper: n * (m+1)
