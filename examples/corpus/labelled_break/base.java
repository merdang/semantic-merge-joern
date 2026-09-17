public class Main {
    public static void main(String[] args) {
        int total = 0;
        int tag = 1;
        int i = 0;
        int j = 0;
        outer:
        while (i < 3) {
            j = 0;
            while (j < 3) {
                total = total + 1;
                if (total > 4) {
                    break outer;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        System.out.println(total);
        System.out.println(tag);
    }
}
