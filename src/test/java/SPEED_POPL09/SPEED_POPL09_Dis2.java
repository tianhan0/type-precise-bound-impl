class SPEED_POPL09_Dis2 {
    void Dis2(int x, int z, int n) {
        int R1 = 0;
        int R2 = 0;
        int x0 = x;
        int z0 = z;
        while (x0 < n)
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
//Bound: Max(0, n - x0) + Max(0, n - z0)

