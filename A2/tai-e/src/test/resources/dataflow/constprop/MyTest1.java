class MyTest1 {
    public int x;
    public MyTest1(int x){
        this.x = x;
    }
    int getInt(int x , int y ){
        return x * y ;
    }
    void test(){
        int x = 1;
        int y = getInt(3,4);
        int z = y / 0;
    }

}
