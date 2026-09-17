public class Main {
    public static void main(String[] args) {
        int code = 2;
        int tag = 1;
        int out = 0;
        switch (code) {
            case 1:
                out = 10;
                break;
            case 2:
                out = 20;
                break;
            default:
                out = 30;
        }
        System.out.println(out);
        System.out.println(tag);
    }
}
