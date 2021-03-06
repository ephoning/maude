***
*** EPH 9/23/10
*** attempt at specification and application of the Y-combinator
*** note: parameterized version of ycond-experiment1.m
***
*** THIS WORKS!
***
*** TODO: - merge with other ho-func (f)modules
***
mod HOF-Y is
	sort FY .
	var F : FY .
	
	op __ : FY FY -> FY [assoc prec 17].  *** FY composition
	op Y : -> FY .
	
	rl [Y-application] : Y F => F (Y F) .
endm

mod HOF-Y1{A :: TRIV, B :: TRIV} is
	inc HOF-Y .
	
	sort FY{A,B} .
	subsort FY{A,B} < FY . *** note: FY (the type used by 'Y') is the "generic supertype"
	
	op __ : FY{A,B} A$Elt -> B$Elt [prec 18] . *** application
	
endm

mod TEST-HOF-Y is
	inc INT .
	inc HOF-Y1{Int,Int} .
	
	*** example: non-recursive definition of 'fac' (to be applied/rewritten using 'Y')
	op fac : -> FY{Int,Int} .
	var F : FY .
	var I : Int .
	eq fac F I = if I == 0 then 1 else I * F (I - 1) fi .
	
	*** "currying" (curried application of 'Y')
	op yfac : -> FY{Int,Int} .
	eq yfac = Y fac .
endm
	

*** === uncomment to enable diagnostics ===	
***set trace on .
***set trace select off .
	
*** === rewriting examples ===
rew Y fac 42 .
rew yfac 42 .
