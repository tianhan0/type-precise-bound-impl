

class SPEED_PLDI10_Ex1 {
    void Ex2(int n, int m) {
        int n0 = n;
        int m0 = m;
        boolean b = false;
        int R = 0;
        while (n0 > 0 && m0 > 0) {
            n0 = n0 - 1;
            m0 = m0 - 1;
            while (b) {
                n0 = n0 - 1;
                m0 = m0 + 1;
                R = R + 1;
            }
        }
    }
}

//Bound: n
