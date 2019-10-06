package SPEED_PLDI10;

class SPEED_PLDI10_Ex6 {
    void Ex6(int n, int x, int z) {
        int x0 = x;
        int z0 = z;
        int R1 = 0;
        int R2 = 0;
        while (x0 < n) {
            if (z0 > x0) {
                x0 = x0 + 1;
                R1 = R1 + 1;
            }
            else {
                z0 = z0 + 1;
                R2 = R2 + 1;
            }
        }
    }
}