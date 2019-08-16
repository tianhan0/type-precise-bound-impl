import java.util.Random;

/**
 * @author Tianhan Lu
 */
public abstract class Gulwani2010reachability {
    abstract boolean nonDet();

    void Ex1(int n, boolean[] A) {
        int i=0;
        int R=0;
        int j=0;
        while (i<n) {
            j=i+1;
            while (j<n) {
                if(A[j]) {
                    R=R+1;
                    // {R+n≤n0+1}
                    j=j-1;
                    n=n-1;
                }
                j=j+1;
            }
            i=i+1;
        }
        // Global invariant: n>0
        // Bound: R≤n0+1
    }

    void Ex2(int n, int m) {
        int R=0;
        while (n>0 && m>0) {
            n=n-1;
            m=m-1;
            while (nonDet()) {
                n=n-1;
                m=m+1;
                R=R+1;
                // {R+n≤n0-2}
            }
        }
        // Global invariant: n>0
        // Bound: R≤n0
    }

    void Ex3(int n, boolean[] A) {
        boolean t=false;
        int R=0;
        while (n>0) {
            t=A[n];
            while (n>0 && t==A[n]) {
                n=n-1;
                R=R+1;
                // {R+n≤n0-1}
            }
        }
        // Global invariant: n>0
        // Bound: R<n0
    }

    void Ex4(int n) {
        boolean flag=true;
        int R=0;
        while(flag) {
            flag=false;
            while (n>0 && nonDet()) {
                n=n-1;
                flag=true;
                R=R+1;
                // {R+n<=n0}
            }
        }
        // Global invariant: n>0
        // Bound: R<n0
    }

    void Ex5(int n) {
        int i=0;
        boolean flag;
        int R=0;
        while (i<n) {
            flag=false;
            while (nonDet()) {
                if (nonDet()) {
                    flag=true;
                    n=n-1;
                    R=R+1;
                    // {R+n<=n0}
                }
            }
            if (!flag) {
                i=i+1;
            }
        }
        // Global invariant: i>0 && n>0
        // Bound: R<n0
    }

    void Ex6(int n, int x, int z) {
        int R1=0;
        int R2=0;
        while (x<n) {
            if (z>x) {
                x=x+1;
                R1=R1+1;
                // {R1=x-x0 ∧ z>x ∧ x<n}
            } else {
                z=z+1;
                R2=R2+1;
                // {R2=z-z0 ∧ z≤x ∧ x<n}
            }
        }
        // Global invariant: n=n0
        // Bound: R1+R2≤n0-x0+n0-z0
    }

    void Ex7(int n, int m) {
        assert(0<n && n<m);
        int j=n+1;
        int R1=0;
        int R2=0;
        while (j<n || j>n) {
            if (j>m) {
                j=0;
                R1=R1+1;
                // {}
            } else {
                j=j+1;
                R2=R2+1;
                // {}
            }
        }
        // Bound: R1+R2<
    }
}
