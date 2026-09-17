public class Main {
    public static void main(String[] args) {
        System.out.println(pick(1));
        System.out.println(pick(-1));
    }

    static int pick(int flag) {
        int y = 0;
        if (flag > 0) {
            y = 1;
        } else {
            y = 2;
        }
        return y;
    }
}
