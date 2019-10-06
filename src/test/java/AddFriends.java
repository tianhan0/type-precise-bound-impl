/**
 * @author Tianhan Lu
 */
public class AddFriends {
    void addFriends(int friends) {
        int R1 = 0;
        int R2 = 0;
        int i = 0;
        int identities = 0;
        while (i < friends) {
            identities = identities + 1;
            i = i + 1;
            // identities=i
        }
        identities = identities - 1;
        R1 = R1 + identities;
        identities = 0;
        identities = identities + 1;
        i = 0;
        while (i < friends) {
            i = i + 1;
            R2 = R2 + identities;
        }
    }
}
