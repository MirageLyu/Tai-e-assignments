class Switch{
    int switch1(int x, int y){
        int a = 0;
        switch(x){
            case 1:
                a-=y;
                break;
            case 2:
                a+=y;
                break;
            case 3:
                a*=y;
                break;
            case 4:
                a/=y;
                break;
            default:
                a = a-1;
        }
        a = a+x;
        return a;
    }

    int switch2(int x, int y){
        int a = 0;
        switch(x){
            case 1:
                a-=y;
                break;
            case 2:
                a+=y;
            case 3:
                a*=y;
            case 4:
                a/=y;
                break;
            default:
                a = a-1;
        }
        a = a+x;
        return a;
    }
}