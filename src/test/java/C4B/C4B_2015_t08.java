package C4B;

class C4B_2015_t08 {
    void start(int y, int z) {
        int y0 = y;
        int R1 = 0;
        int R2 = 0;
        while (z > y0) {
            y0 = y0 + 1;
            R1 = R1 + 1;
        }
        while (y0 > 2) {
            y0 = y0 - 3;
            R2 = R2 + 1;
        }
    }
}