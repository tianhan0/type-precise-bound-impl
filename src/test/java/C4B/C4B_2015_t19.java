package C4B;

class C4B_2015_t19 {
    void start(int i, int k) {
        int i0 = i;
        int R1 = 0;
        int R2 = 0;
        while (i0 > 100) {
            i0 = i0 - 1;
            R1 = R1 + 1;
        }
        i0 = i0 + k + 50;
        while (i0 >= 0) {
            i0 = i0 - 1;
            R2 = R2 + 1;
        }
    }
}
