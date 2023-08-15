class T20{
	public static void main(String[] args){
		try{
			T20A a1;
			T20A a2;
			T20A a3;
			a1 = new T20A();
			a1.foo();
			a2 = T20A.g;
			a3 = a2.f;
			synchronized(a3){
				System.out.println(a3);
			}
		}catch(Exception e){

		}
		
	}
}

class T20A{
	static T20A g;
	T20A f;
	public void foo(){
		T20A a1;
		T20A a2;
		T20A a3;
		a1 = new T20A();
		a3 = new T20A();
		a1.f = a3;
		T20A.g = a1;
		a2 = new T20A();
		synchronized(a2){
			System.out.println(a2);
		}

	}
}
class P1{
	
}