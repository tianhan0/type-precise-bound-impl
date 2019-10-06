package C4B;

class C4B_2015_t07 {
    void start(int x, int y) {
        int x0 = x;
        int y0 = y;
        int R1 = 0;
        int R2 = 0;
        int R3 = 0;
        while (x0 > 0) {
            x0 = x0 - 1;
            y0 = y0 + 2;
            R1 = R1 + 1;
        }
        while (y0 > 0) {
            y0 = y0 - 1;
            R2 = R2 + 1;
        }
        while (y0 > 0) {
            y0 = y0 - 1;
            R3 = R3 + 1;
        }
    }
}