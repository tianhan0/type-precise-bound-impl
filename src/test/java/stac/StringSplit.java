package stac;

/**
 * @author Tianhan Lu
 */
public class StringSplit {
    void main(int count, boolean b, int q) {
        int R1 = 0;
        int R2 = 0;
        int off = 0;
        int next = 0;
        next = q;
        while (next != -1 && b) {
            int tmp = next - off;
            off = next + 1;
            next = q;
            R1 = R1 + tmp;
        }
        R2 += count - off;
        off = count;
        assert (next <= count) : "global";
        assert (R1 <= count) : "bound";
    }
}
