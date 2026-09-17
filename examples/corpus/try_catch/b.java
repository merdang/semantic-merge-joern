public class Main {
    public static void main(String[] args) {
        int v = 0;
        int tag = 6;
        try {
            v = 10 / 2;
        } catch (ArithmeticException e) {
            v = -1;
        }
        System.out.println(v);
        System.out.println(tag);
    }
}
