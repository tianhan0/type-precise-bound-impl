class SPEED_POPL09_Dis1 {
    void Dis1(int x0, int y0, int n, int m) {
        int R1 = 0;
        int R2 = 0;
        int x = x0;
        int y = y0;
        while (x < n) {
            if (y < m) {
                y = y + 1;
                R1 = R1 + 1;
            }
            else {
                x = x + 1;
                R2 = R2 + 1;
            }
        }
    }
}

//Bound Max(0, n − x0 ) + Max(0, m − y0 ) 
