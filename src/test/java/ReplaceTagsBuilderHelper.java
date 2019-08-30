/**
 * @author Tianhan Lu
 */
abstract public class ReplaceTagsBuilderHelper {
    abstract int rand();

    void replaceTagsBuilderHelper(int len) {
        int R1 = 0;
        int R2 = 0;
        int linePointer = 0; // keep track of where we are on the text string
        int startTagLocation = 0;
        int endTagLocation = 0;
        while (endTagLocation<len) {
            startTagLocation = endTagLocation+rand();
            endTagLocation = startTagLocation+rand();
            R1 = R1+startTagLocation-linePointer;
            int val = rand();
            R2 = R2 + val;
            // R1+R2<=endTagLocation
            linePointer = endTagLocation;
        }
        R1 = R1+len-linePointer;
        // Global invariant: 0<rand()<?
    }
}
