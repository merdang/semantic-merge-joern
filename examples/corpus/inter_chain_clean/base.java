public class Main {
    public static void main(String[] args) {
        System.out.println(topA(1));
        System.out.println(topB(1));
    }

    static int topA(int x) {
        return midA(x) * 2;
    }

    static int midA(int x) {
        return x + 1;
    }

    static int topB(int x) {
        return midB(x) * 3;
    }

    static int midB(int x) {
        return x + 10;
    }
}
