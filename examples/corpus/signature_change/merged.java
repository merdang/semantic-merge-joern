public class Main {
    public static void main(String[] args) {
        int p = 3;
        int tag = 9;
        int r = scale(p, 4);
        System.out.println(r);
        System.out.println(tag);
    }
    static int scale(int x, int k) {
        return x * k;
    }
}
