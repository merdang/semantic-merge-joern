public class Main {
    public static void main(String[] args) {
        int n = 2;
        int tag = 1;
        int out = 0;
        if (twice(n) > 3) {
            out = 100;
        }
        System.out.println(out);
        System.out.println(tag);
    }

    static int twice(int x) {
        return x * 2;
    }
}
