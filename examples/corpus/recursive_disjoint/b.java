public class Main {
    public static void main(String[] args) {
        int total = countdown(3);
        System.out.println(total);
    }

    static int countdown(int n) {
        int shown = n * 100;
        int step = n;
        if (n <= 0) {
            return 0;
        }
        System.out.println(shown);
        return step + countdown(n - 1);
    }
}
