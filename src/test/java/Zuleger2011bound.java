/**
 * @author Tianhan Lu
 */
abstract public class Zuleger2011bound {
    abstract boolean nonDet();
    abstract int nonDetInt();

    void Ex1(int n, boolean b) {
        int i=0;
        int j;
        int R=0;
        while(i<n) {
            i=i+1;
            j=0;
            // boolean b = nonDet();
            while(i<n && b) {
                i=i+1;
                j=j+1;
                // b = nonDet();
                R=R+1;
                // {R≤i} {i<=n}
            }
            if (j>0) {
                i=i-1;
            }
        }
        assert (i <= n) : "global";
        assert (R <= n) : "bound";
    }

    /*void bin_search_StepSize2(int r, int s) {
        int c=4; // log2c=2
        int n= nonDetInt();
        boolean f=false;
        int d=0;
        while (c!=1 && s<=255 && s>=0 && n!=r) { // log2c!=0
            n = nonDetInt();
            if (f) {
                c=c/2; // log2c--;
            }
            if (n>r) {
                if (d==1 && !f) {
                    f=true;
                    c=c/2; // log2c--;
                }
                d=2;
                s=s+c;
            } else if (n<r) {
                if (d==2 && !f) {
                    f=true;
                    c=c/2; // log2c--;
                }
                d=1;
                s=s-c;
            }
        }
    }*/
}
