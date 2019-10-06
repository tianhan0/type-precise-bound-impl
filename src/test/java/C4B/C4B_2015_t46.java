package C4B;//in contrast to original example all function calls are inlined

class C4B_2015_t46 {
    void start(int y) {
        int R1 = 0;
        int R2 = 0;
        int R3 = 0;
        int y0 = y;
        int x = 0;
        while (y0 > 0) {
            y0 = y0 - 1;
            x = x + 1;
            R1 = R1 + 1;
        }
        while (x > 0) {
            x = x - 1;
            y0 = y0 + 1;
            R2 = R2 + 1;
        }
        while (y > 0) {
            y0 = y0 - 1;
            x = x + 1;
            R3 = R3 + 1;
        }
    }
}

