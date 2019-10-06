package C4B;

class C4B_2015_t11 {
    void start(int x, int y, int n, int m) {
        int x0 = x;
        int y0 = y;
        int R1 = 0;
        int R2 = 0;
        while (n > x0) {
            if (m > y0) {
                y0 = y0 + 1;
                R1 = R1 + 1;
            }
            else {
                x0 = x0 + 1;
                R2 = R2 + 1;
            }
        }
    }
}