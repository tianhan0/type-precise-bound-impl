/**
 * @author Tianhan Lu
 */
abstract public class Gulwani2009speed {
    abstract boolean nonDet();

    void SimpleSingle(int n, boolean b) {
        int R = 0;
        int x = 0;
        while (x < n) {
            if (b) {
                x = x + 1;
                // R=R+1;
            } else {
                x = x + 1;
                // R=R+1;
            }
            R = R + 1;
        }
    }

    void SequentialSingle(int n, boolean b) {
        int R1 = 0;
        int R2 = 0;
        int x = 0;
        while (x < n && b) {
            x = x + 1;
            R1 = R1 + 1;
        }
        while (x < n) {
            x = x + 1;
            R2 = R2 + 1;
        }
    }

    void NestedSingle(int n, boolean b) {
        int R = 0;
        int x = 0;
        while (x < n) {
            while (x < n && b) {
                x = x + 1;
                // R=R+1;
            }
            R = R + 1;
        }
        x = x + 1;
    }

    void SimpleSingle2(int n, int m, boolean b) {
        int R1 = 0;
        int R2 = 0;
        int x = 0;
        int y = 0;
        while (b) {
            if (x < n) {
                x = x + 1;
                y = y + 1;
                R1 = R1 + 1;
            } else if (y < m) {
                x = x + 1;
                y = y + 1;
                R2 = R2 + 1;
            } else break;
        }
    }

    void SimpleMultiple(int n, int m) {
        int R1 = 0;
        int R2 = 0;
        int x = 0;
        int y = 0;
        while (x < n) {
            if (y < m) {
                y = y + 1;
                R1 = R1 + 1;
            } else {
                x = x + 1;
                R2 = R2 + 1;
            }
        }
    }

    void NestedMultiple(int x0, int y0, int n, int m, boolean b) {
        int R1 = 0;
        int R2 = 0;
        int x = x0;
        int y = y0;
        while (x < n) {
            while (y < m && b) {
                y = y + 1;
                R1 = R1 + 1;
            }
            x = x + 1;
            R2 = R2 + 1;
        }
    }

    void SimpleMultipleDep(int n, int m) {
        int x = 0;
        int y = 0;
        int R1 = 0;
        int R2 = 0;
        while (x < n) {
            if (y < m) {
                y = y + 1;
                R1 = R1 + 1;
            } else {
                y = 0;
                x = x + 1;
                R2 = R2 + 1;
            }
        }
        // Nonlinear bound
    }

    void NestedMultipleDep(int n, int m) {
        int x = 0;
        int y;
        int R = 0;
        while (x < n) {
            y = 0;
            x = x + 1;
            while (y < m) {
                y = y + 1;
                R = R + 1;
            }
        }
        // Nonlinear bound
    }
}
