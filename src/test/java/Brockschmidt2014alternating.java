/**
 * @author Tianhan Lu
 */
public class Brockschmidt2014alternating {
    void Ex1(int i) {
        int x=0;
        int R1=0;
        int R2=0;
        while (i>0) {
            i=i-1;
            x=x+i;
            R1=R1+1;
            // {R1+i=i0 ∧ x=(i0+i)(i0-i+1)/2}
        }
        while (x>0) {
            x=x-1;
            R2=R2+1;
            // {R2+x=x0-1}
        }
        // Global invariant: i≥0
        // Bound: R1+R2<=i0+(i0+1)*i0/2-1
    }
}
