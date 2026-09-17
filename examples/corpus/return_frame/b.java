public class Main {
    public static void main(String[] args) {
        int v0 = 3;
        int v1 = 0;
        v0 = f1(v0);
        v1 = v1 + v0;
        System.out.println(v1);
    }

    static int f1(int x) {
        int h0 = 4;
        x = 5;
        return x + 1;
    }
}
