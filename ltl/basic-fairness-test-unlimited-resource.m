*** EPH sept 25 2012

*** a basic experiment to excercise the following satisfaction items:
*** 1- check liveness / is there opportunity for starvation?
*** 2- check liveness / 

*** all this in te using the following construct
*** - 2 clients that compete for the same limited resource

*** tests:
*** - is it possible that client 2 never gets access to the shared resource?
*** - is it always true that client 2 never gets resource access?
*** - eventually client2 gets resoruce access?
*** - is it always true that eventually client 2 gets resource access?


*** NOTE
*** - unlimited resource; i.e., clients can ongoingly pull from / access the resource


*** From the results (see below) it is clear that this style of modelling leads to an infinite state machine
*** - and hence stack overflow when testing certain satisfaction targets)
*** TODO:
***    investigate / study the equational abstraction approach to model transformation from infinite to finite
***    as documented in:
***    - ~/info/theory/linear-temporal-logic/MartiOlietEtAl05-ea.pdf
***    - ~/info/maude/maude-book.pdf chapter 12.4 Verifying Infiint-State Systems Through Abstractions
***    - ~/info/maude/maude-book.pdf chapter 13.4 Equational Abstractions
***    - ~/info/maude/maude-book.pdf chapter 15.3 A Deadlock-Freedom Transformation
***
*** further lit. to investigate:

***(
Jose ́ Meseguer, Miguel Palomino, and Narciso Mart́ı-Oliet. Notes on model checking and abstrac- tion in rewriting logic. http://maude.sip.ucm.es/∼miguelpt/bibliography, 2002.

Meseguer, J., Palomino, M., Mart ́ı-Oliet, N.: Equational abstractions. In: Baader, F. (ed.) CADE 2003. LNCS (LNAI), vol. 2741, pp. 2–16. Springer, Heidelberg (2003)

)

in model-checker.maude

mod RESOURCE-ACCESS is
    pr INT .

    sorts Resource Client Conf .
    subsorts Resource Client < Conf .

    op none : -> Conf [ctor] .
    op __ : Conf Conf -> Conf [ctor assoc comm id: none] .

    op rsrc : -> Resource [ctor] .

    ops c1 c2 : Int -> Client [ctor] .

    var N : Int .

    rl [c1-consumes] : c1(N) => c1(N + 1) . 
    rl [c2-consumes] : c2(N) => c2(N + 1) . 
endm

mod RESOURCE-ACCESS-PREDS is
    pr RESOURCE-ACCESS .
    including SATISFACTION .
    
    subsort Conf < State .

    var C : Conf .
    var N : Int .

    op c2-alive : -> Prop .
    ceq c2(N) C |= c2-alive = true if N > 0 . --- if c2 got access to the resource, it is considered alive
endm

mod RESOURCE-ACCESS-CHECK is
    pr RESOURCE-ACCESS-PREDS .
    inc MODEL-CHECKER .
    inc LTL-SIMPLIFIER .

    op initial : -> Conf .
    eq initial = c1(0) c2(0) .
endm

*** - is it possible that client 2 never gets access to the shared resource?
*** red modelCheck(initial, ~ [] c2-alive) .

*** - is it always true that client 2 never gets resource access?
*** red modelCheck(initial, [] ~ c2-alive) .


*** - eventually client2 gets resoruce access?
*** red modelCheck(initial, <> c2-alive) .


*** - is it always true that eventually client 2 gets resource access?
*** red modelCheck(initial, [] <> c2-alive) .

*** --- RESULTS ---
***(

Maude> red modelCheck(initial, ~ [] c2-alive) .
reduce in RESOURCE-ACCESS-CHECK : modelCheck(initial, ~ []c2-alive) .
rewrites: 12
result Bool: true
Maude> red modelCheck(initial, [] ~ c2-alive) .
reduce in RESOURCE-ACCESS-CHECK : modelCheck(initial, []~ c2-alive) .

Fatal error: stack overflow.
This can happen because you have an infinite computation, say a runaway
recursion, or model checking an infinite model. It can also happen because
...

Maude> red modelCheck(initial, <> c2-alive) .
reduce in RESOURCE-ACCESS-CHECK : modelCheck(initial, <> c2-alive) .

Fatal error: stack overflow.
This can happen because you have an infinite computation, say a runaway
recursion, or model checking an infinite model. It can also happen because
...

Maude> red modelCheck(initial, [] <> c2-alive) .
reduce in RESOURCE-ACCESS-CHECK : modelCheck(initial, []<> c2-alive) .

Fatal error: stack overflow.
This can happen because you have an infinite computation, say a runaway
recursion, or model checking an infinite model. It can also happen because
...

)