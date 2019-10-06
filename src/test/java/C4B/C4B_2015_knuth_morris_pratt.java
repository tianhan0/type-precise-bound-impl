package C4B;/* Knuth-Morris-Pratt string searching */

class C4B_2015_knuth_morris_pratt {
    int srch(int t, int n, int p, int m, int b) {
        int i = 0;
        int j = 0;
        int k = -1;

        int R1 = 0;
        int R2 = 0;
        while (i < n) {
            while (j >= 0 && t != p) {
                k = b;
                if (!(k > 0 && k <= j + 1))
                    return i;
                j = j - k;
                R1 = R1 + 1;
            }
            i = i + 1;
            j = j + 1;
            if (j == m)
                break;
            R2 = R2 + 1;
        }
        return i;
    }
}