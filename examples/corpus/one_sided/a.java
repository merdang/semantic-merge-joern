public class Main {
    public static void main(String[] args) {
        int a = 1;
        int b = 2;
        a = a + 1;
        b = b + 5;
        if (a > 10) {
            a = a + 2;
        }
        System.out.printf("a: %d, b: %d\n", a, b);
    }
}
