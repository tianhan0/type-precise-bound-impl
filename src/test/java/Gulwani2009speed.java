/**
 * @author Tianhan Lu
 */
abstract public class Gulwani2009speed {
    abstract boolean nonDet();

    void SimpleSingle(int n) {
        int R=0;
        int x=0;
        while (x<n) {
            if (nonDet()) {
                x=x+1;
                // R=R+1;
            } else {
                x=x+1;
                // R=R+1;
            }
            R=R+1;
        }
    }

    void SequentialSingle(int n) {
        int R1=0;
        int R2=0;
        int x=0;
        while (x<n && nonDet()) {
            x=x+1;
            R1=R1+1;
        }
        while (x<n) {
            x=x+1;
            R2=R2+1;
        }
    }

    void NestedSingle(int n) {
        int R=0;
        int x=0;
        while (x<n) {
            while (x<n && nonDet()) {
                x=x+1;
                // R=R+1;
            }
            R=R+1;
        }
        x=x+1;
    }

    void SimpleSingle2(int n, int m) {
        int R=0;
        int x=0;
        int y=0;
        while (nonDet()) {
            if (x<n) {
                x=x+1;
                y=y+1;
            } else if (y<m) {
                x=x+1;
                y=y+1;
            } else break;
            R=R+1;
        }
    }

    void SimpleMultiple(int n, int m) {
        int R1=0;
        int R2=0;
        int x=0;
        int y=0;
        while (x<n) {
            if (y<m) {
                y=y+1;
                R1=R1+1;
            } else {
                x=x+1;
                R2=R2+1;
            }
        }
    }

    void NestedMultiple(int x0 , int y0 , int n, int m) {
        int R1=0;
        int R2=0;
        int x=x0;
        int y=y0;
        while (x<n) {
            while (y<m && nonDet()) {
                y=y+1;
                R1=R1+1;
            }
            x=x+1;
            R2=R2+1;
        }
    }

    void SimpleMultipleDep(int n, int m) {
        int x=0;
        int y=0;
        while (x<n) {
            if (y<m) {
                y=y+1;
            } else {
                y=0;
                x=x+1;
            }
        }
        // Nonlinear bound
    }

    void NestedMultipleDep(int n, int m) {
        int x=0;
        int y;
        while (x<n) {
            y=0;
            x=x+1;
            while (y<m) {
                y=y+1;
            }
        }
        // Nonlinear bound
    }
}
