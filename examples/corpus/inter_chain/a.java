public class Main {
    public static void main(String[] args) {
        System.out.println(outer(3));
    }

    static int outer(int x) {
        return inner(x) * 2;
    }

    static int inner(int x) {
        return x + 5;
    }
}
