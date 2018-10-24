object primes {
	def isPrime(value: Int, divider: Int): Boolean = {		
		if(divider == value) {
			true
		} else {
			if(value % divider == 0 || value == 0 || value == 1) {
				false 
			} else {
				true && isPrime(value, divider + 1)
			}
		}
	}

	def computePrimes(value: Int, maxValue: Int, list: L.List): L.List = {		
			if(isPrime(value, 2)) {
				if(value == maxValue) {
					L.Cons(value, list)
				} else {
					computePrimes(value + 1, maxValue, L.Cons(value, list))
				}
			} else {
				if(value == maxValue) {
					L.Nil()
				} else {
					computePrimes(value + 1, maxValue, list)
				}
			}
		
	}

	Std.printString("Until what value do you want your List of primes to extend ?");
	val maxValue: Int = Std.readInt();
	val list: L.List = computePrimes(0, maxValue, L.Nil());
	Std.printString(L.toString(list))
}