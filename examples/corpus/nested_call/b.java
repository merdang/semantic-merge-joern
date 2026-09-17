public class Main {
    public static void main(String[] args) {
        int seed = 2;
        int tag = 7;
        int r = outer(inner(seed));
        System.out.println(r);
        System.out.println(tag);
    }

    static int inner(int x) {
        return x + 3;
    }

    static int outer(int x) {
        return x * 10;
    }
}
