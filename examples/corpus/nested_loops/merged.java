public class Main {
    public static void main(String[] args) {
        int total = 0;
        int tag = 5;
        int i = 0;
        int j = 0;
        while (i < 3) {
            j = 0;
            while (j < 2) {
                total = total + 2;
                j = j + 1;
            }
            i = i + 1;
        }
        System.out.println(total);
        System.out.println(tag);
    }
}
