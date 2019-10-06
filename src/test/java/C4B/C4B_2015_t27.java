package C4B;

class C4B_2015_t27 {
    void start(int n, int y) {
        int R1 = 0;
        int y0 = y;
        int n0 = n;
        while (n0 < 0) {
            n0 = n0 + 1;
            y0 = y0 + 1000;
            while (y0 >= 100) {
                y0 = y0 - 100;
                R1 = R1 + 1;
            }
        }
    }
}

