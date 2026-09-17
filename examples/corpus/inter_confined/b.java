public class Main {
    public static void main(String[] args) {
        int a = 1;
        int b = twice(a);
        int c = 3;
        System.out.println(b);
        System.out.println(c);
    }

    static int twice(int x) {
        return x * 2;
    }
}
