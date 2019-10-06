package SPEED_CAV09;

class SPEED_CAV09_ex3 {
    int foo(int n, boolean b) {
        int x = 0;
        int R1 = 0;
        while (x < n && b) {
            int y = x;
            while (y < n && b) {
                y = y + 1;
                R1 = R1 + 1;
            }
            x = y + 1;
        }
        return 1;
    }
}

//bound according to paper: n
