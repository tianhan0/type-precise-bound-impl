
class SPEED_PLDI10_Ex1 {
    void Ex1(int n) {
        boolean b = false;
        int n0 = n;
        // int qqq = 0;
        int i = 0;
        int R = 0;
        while (i < n0) {
            int j = i + 1;
            while (j < n0) {
                if (b) {
                    j = j - 1;
                    // qqq = n - n0;
                    n0 = n0 - 1;
                    R = R + 1;
                    // R + qqq <= 0
                }
                j = j + 1;
            }
            i = i + 1;
        }
    }
}

//Bound: n^2
//Reachability Bound for ConsumeResource(): n

