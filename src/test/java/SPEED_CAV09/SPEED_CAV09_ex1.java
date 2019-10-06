package SPEED_CAV09;

class SPEED_CAV09_ex1 {
    int foo(int m) {
        int R1 = 0;
        int R2 = 0;
        int x = 0;
        int y = 0;
        while (x < 100) {
            if (y < m) {
                y = y + 1;
                R1 = R1 + 1;
            }
            else {
                x = x + 1;
                R2 = R2 + 1;
            }
        }
        return 1;
    }
}

//Bound according to paper: 100 + max(0, m)
