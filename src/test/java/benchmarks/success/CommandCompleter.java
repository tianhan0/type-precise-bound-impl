package benchmarks.success;

/**
 * @author Tianhan Lu
 */
abstract public class CommandCompleter {
    abstract boolean nonDetInt();

    void complete(int n, int m) {
        int R1=0;
        int R2=0;
        int i=0;
        int k=0;
        boolean b = false;
        while (i<n) {
            i=i+1;
            k=k+1;
        }
        if (b) {
            assert (k < n) : "global"; // Need
            R1=R1+k;
        } else {
            int j=0;
            while (j<k) {
                if (b) {
                    R2=R2+1;
                }
                j=j+1;
            }
        }
    }
}
