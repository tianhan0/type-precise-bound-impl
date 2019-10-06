
class SPEED_POPL09_SequentialSingle {
    void SequentialSingle(int n, boolean b) {
        int x = 0;
        int R1 = 0;
        int R2 = 0;
        while (x < n && b) {
            x = x + 1;
            R1 = R1 + 1;
        }
        while (x < n) {
            x = x + 1;
            R2 = R2 + 1;
        }
    }
}

//Bound: n

