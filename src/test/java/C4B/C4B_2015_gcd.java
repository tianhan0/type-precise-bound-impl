package C4B;/* gcd by substractions */

class C4B_2015_gcd {
    void gcd(int x, int y) {
        int x0 = x;
        int y0 = y;
        int R1 = 0;
        int R2 = 0;
        while (x0 > 0 && y0 > 0) {
            if (x0 > y0) {
                x0 = x0 - y0;
                R1 = R1 + 1;
            }
            else {
                y0 = y0 - x0;
                R2 = R2 + 1;
            }
        }
    }
}