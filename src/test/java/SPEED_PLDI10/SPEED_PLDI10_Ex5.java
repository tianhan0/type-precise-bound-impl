package SPEED_PLDI10;

class SPEED_PLDI10_Ex5 {
    void Ex5(int n, boolean b) {
        int i = 0;
        int n0 = n;
        int R1 = 0;
        while (i < n0) {
            boolean flag = false;
            while (b) {
                if (b) {
                    flag = true;
                    n0 = n0 - 1;
                }
                R1 = R1 + 1;
            }
            if (!flag) {
                i = i + 1;
            }
        }
    }
}

//Bound for outer loop: n
//Bound for inner loop: none
//Bound: none

