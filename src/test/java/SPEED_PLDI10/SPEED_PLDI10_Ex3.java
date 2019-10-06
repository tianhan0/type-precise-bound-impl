package SPEED_PLDI10;

class SPEED_PLDI10_Ex3 {
    void Ex3(int n, int A) {
        int n0 = n;
        int R1 = 0;
        while (n0 > 0) {
            int t = A;
            while (n0 > 0 && t == A) {
                n0 = n0 - 1;
                R1 = R1 + 1;
            }
        }
    }
}

//Bound: n

