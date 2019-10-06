package C4B;

class C4B_2015_t16 {
    void start(int x, int y) {
        if (!(y >= 0))
            return;

        int R1 = 0;
        while (x > y) {
            x = x - (y + 1);
            int z = y;
            while (z > 0) {
                z = z - 1;
                R1 = R1 + 1;
            }
        }
    }
}