public class Main {
    public static void main(String[] args) {
        int a = twice(3);
        System.out.println(a);
        int b = twice(5);
        System.out.println(b);
    }

    static int twice(int x) {
        return x * 2;
    }
}
