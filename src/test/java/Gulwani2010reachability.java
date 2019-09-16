/**
 * @author Tianhan Lu
 */
public abstract class Gulwani2010reachability {
    abstract boolean nonDet();

    void Ex1(int n, boolean A) {
        int i=0;
        int R=0;
        int j=0;
        while (i<n) {
            j=i+1;
            while (j<n) {
                if(A) {
                    j=j-1;
                    n=n-1;
                    R=R+1;
                    // {R+n≤n0+1}
                }
                j=j+1;
            }
            i=i+1;
        }
        // Global invariant: n>=0
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

    void Ex3(int n, boolean A) {
        boolean t=false;
        int R=0;
        while (n>0) {
            t=A;
            while (n>0 && t==A) {
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
        while (j<n || j>n) { // j!=n
            if (j>m) {
                j=0;
                R1=R1+1;
                // {R1=1}: Verification relies on the loop invariant of keeping executing line 125: Will not visit this location again
            } else {
                // j0, R20
                j=j+1;
                R2=R2+1;
                // {j-R2=j0-R20 and j0<=m and (j0>n or j0<n) and j<=m and (j>n or j<n)}
            }
        }
        // Global invariant: j>=0
        // Bound: R2<m
    }

    void Ex8() {
        int x=0;
        int y=0;
        while (nonDet()) {
            if (x!=50) {
                y++;
            } else {
                y--;
            }
            if (y<0) break;
            x=x+1;
        }
        // Bound: x=102
    }

    void Ex9() {
        int x=0;
        int y=50;
        while (x<100) {
            if (x<50) {
                x=x+1;
            } else {
                x=x+1;
                y=y+1; // Consider y as resource consumption
                // {y-x=50-x0 and 100>x0>=50 and 100>x>=50}
            }
        }
        // Bound: y<=100
    }

    void Ex10(int x, int y) {
        assert (x!=y);
        boolean lock=false;
        while (x!=y) {
            lock=true;
            x=y;
            if (nonDet()) {
                lock=false;
                y=y+1;
            }
        }
    }

    void Ex11(int N) {
        int x=0;
        int upd=0;
        int l;
        while (x<N) {
            if (nonDet()) {
                l=x;
                upd=1;
            }
            x=x+1;
        }
        // Bound: l<N
    }
}
