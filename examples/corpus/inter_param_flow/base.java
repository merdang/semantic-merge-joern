public class Main {
    public static void main(String[] args) {
        int seed = 4;
        int r = compute(seed);
        System.out.println(r);
    }

    static int compute(int x) {
        int y = x + 1;
        return y;
    }
}
