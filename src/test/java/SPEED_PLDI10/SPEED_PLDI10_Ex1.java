package SPEED_PLDI10;

class SPEED_PLDI10_Ex1 {
    void Ex1(int n, boolean A) {
        int i = 0;
        int R = 0;
        int j = 0;
        while (i < n) {
            j = i + 1;
            while (j < n) {
                if (A) {
                    j = j - 1;
                    n = n - 1;
                    R = R + 1;
                    // {R+n≤n0+1}
                }
                j = j + 1;
            }
            i = i + 1;
        }
        // Global invariant: n>=0
        // Bound: R≤n0+1
    }
}

//Bound: n^2
//Reachability Bound for ConsumeResource(): n

