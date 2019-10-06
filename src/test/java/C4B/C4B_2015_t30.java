package C4B;

class C4B_2015_t30 {
    void start(int x, int y) {
        int t;
        int R1 = 0;
        int x0 = x;
        int y0 = y;
        while (x0 > 0) {
            x0 = x0 - 1;
            t = x0;
            x0 = y0;
            y0 = t;
            R1 = R1 + 1;
        }
    }
}
