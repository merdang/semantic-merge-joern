public class Main {
    public static void main(String[] args) {
        int p = 3;
        int tag = 1;
        int r = scale(p);
        System.out.println(r);
        System.out.println(tag);
    }

    static int scale(int x) {
        return x * 2;
    }
}
