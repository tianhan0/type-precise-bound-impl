abstract class BreakParagraphs {
    abstract boolean nonDetInt();
    abstract int rand();

    void breakParagraphs(int n) {
        int R1=0;
        int R2=0;
        int i=0;
        int m=0;
        while (i<n) {
            int r=rand();
            i=i+r;
            if (i<n) {
                if (nonDetInt()) {
                    m=m+r;
                } else {
                    R1=R1+m;
                    assert (i<=n);
                    // R1<=i, i<=n
                    m=0;
                }
            }
        }
        R2=R2+m;
        // R2<=m
        // Global invariant: m<=n
        // Bound: R1+R2<=2*n
    }
}