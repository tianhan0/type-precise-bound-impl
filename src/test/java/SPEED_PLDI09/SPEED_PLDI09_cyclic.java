package SPEED_PLDI09;

class SPEED_PLDI09_cyclic {
    void cyclic(int id, int maxId, boolean b) {
        int R1 = 0;
        int R2 = 0;
        if (0 <= id && id <= maxId) {
            int tmp = id + 1;
            while (tmp != id && b) {
                if (tmp <= maxId) {
                    tmp = tmp + 1;
                    R1 = R1 + 1;
                }
                else {
                    tmp = 0;
                    R2 = R2 + 1;
                }
            }
        }
    }
}