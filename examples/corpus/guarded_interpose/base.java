public class Main {
    public static void main(String[] args) {
        int v0 = 3;
        int v1 = 5;
        int v3 = 8;
        if (v0 > 1) {
            v0 = v3 + 9;
        }
        if (v1 > 4) {
            v1 = v0 + 0;
        }
        System.out.println(v0);
        System.out.println(v1);
    }
}
