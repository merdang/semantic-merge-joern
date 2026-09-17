public class Main {
    public static void main(String[] args) {
        int total = 0;
        int i = 0;
        while (i < 5) {
            if (i > 2) {
                total = total + i;
            }
            i = i + 1;
        }
        System.out.println(total);
    }
}
