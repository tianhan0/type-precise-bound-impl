/**
 * @author Tianhan Lu
 */
abstract public class Gulwani2009control {
    abstract boolean nonDet();

    void cyclic(int id, int maxId) {
        assert (0<=id && id<maxId);
        int tmp = id + 1;
        while (tmp!=id && nonDet()) {
            if (tmp <= maxId) {
                tmp = tmp + 1;
            } else {
                tmp = 0;
            }
        }
    }

    void NestedLoop(int n, int m, int N) {
        assert (0<=n && 0<=m && 0<=N);
        int i=0;
        int j;
        int k;
        int R=0;
        while (i<n && nonDet()) {
            j=0;
            while (j<m && nonDet()) {
                j=j+1;
                k=i;
                while (k<N && nonDet()) {
                    k=k+1;
                    R=R+1;
                    // {R=k}???
                }
                i=k;
            }
            i=i+1;
        }
        // Bound: N
    }

    void Ex2(int n, int m) {
        assert(n>0 && m>0);
        int v1=n;
        int v2=0;
        while (v1>0 && nonDet()) {
            if (v2<m) {
                v2=v2+1;
                v1=v1-1;
            } else {
                v2=0;
            }
        }
    }
}
