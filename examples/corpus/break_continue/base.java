public class Main {
    public static void main(String[] args) {
        int total = 0;
        int flag = 1;
        int i = 0;
        while (i < 8) {
            i = i + 1;
            if (i == 3) {
                continue;
            }
            if (i > 5) {
                break;
            }
            total = total + i;
        }
        System.out.println(total);
        System.out.println(flag);
    }
}
