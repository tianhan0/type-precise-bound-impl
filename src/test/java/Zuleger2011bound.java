/**
 * @author Tianhan Lu
 */
abstract public class Zuleger2011bound {
    abstract boolean nonDet();
    abstract int nonDetInt();

    void Ex1(int n) {
        int i=0;
        int j;
        while(i<n) {
            i=i+1;
            j=0;
            while(i<n && nonDet()) {
                i=i+1;
                j=j+1;
                // {R≤i}
            }
            if (j>0) {
                i=i-1;
            }
        }
        // Global invariant: i<n
        // Bound: R<n
    }

    void bin_search_StepSize2(int r, int s) {
        int c=4;
        int n= nonDetInt();
        boolean f=false;
        int d=0;
        while (c!=1 && s<=255 && s>=0 && n!=r) {
            n = nonDetInt();
            if (f) {
                c=c/2;
            }
            if (n>r) {
                if (d==1 && !f) {
                    f=true;
                    c=c/2;
                }
                d=2;
                s=s+c;
            } else if (n<r) {
                if (d==2 && !f) {
                    f=true;
                    c=c/2;
                }
                d=1;
                s=s-c;
            }
        }
    }
}
