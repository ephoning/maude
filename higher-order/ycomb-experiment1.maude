***
*** EPH 9/21/10
*** attempt at specification and application of the Y-combinator
***
*** THIS WORKS!
***
*** TODO: - attempt wrapping 'rew' application in 'red'
***       - parameterization (i.e., remove hard tie to 'Int')
***       - curried application
***
mod HOF-Y is
	sort FY .
	var F : FY .
	
	op __ : FY FY -> FY [assoc prec 17].  *** FY composition
	op Y : -> FY .
	
	rl [Y-application] : Y F => F (Y F) .
endm

mod TEST-HOF-Y is
	inc HOF-Y .
	inc INT .
	
	op __ : FY Int -> Int [prec 18] . *** application

	*** example: non-recursive definition of 'fac' (to be applied/rewritten using 'Y')
	op fac : -> FY .
	var F : FY .
	var I : Int .
	eq fac F I = if I == 0 then 1 else I * F (I - 1) fi .	


	op apply : -> Int .
	eq apply = Y fac 42 .
endm
	
	
	
*** rewriting example
***set trace on .
***set trace select off .
***rew Y fac 42 .
