public class Main {
    public static void main(String[] args) {
        int r1 = calc(2);
        int r2 = calc(2, 3);
        System.out.println(r1);
        System.out.println(r2);
    }

    static int calc(int x) {
        return x * 2;
    }

    static int calc(int x, int y) {
        return x + y;
    }
}
