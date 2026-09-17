public class Main {
    public static void main(String[] args) {
        int acc = 0;
        int tag = 4;
        int i = 0;
        while (i < 3) {
            acc = acc + twice(i);
            i = i + 1;
        }
        System.out.println(acc);
        System.out.println(tag);
    }

    static int twice(int x) {
        return x * 2;
    }
}
