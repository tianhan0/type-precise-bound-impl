package SPEED_PLDI10;

class SPEED_PLDI10_Ex4 {
    int foo(int n, boolean b) {
        boolean flag = true;
        int R1 = 0;
        int n0 = n;
        while (flag) {
            flag = false;
            while (n0 > 0 && b) {
                n0 = n0 - 1;
                flag = true;
                R1 = R1 + 1;
            }
        }
        return 0;
    }
}

//Bound according to paper: n+1
//Remark: The Example does not terminate!

