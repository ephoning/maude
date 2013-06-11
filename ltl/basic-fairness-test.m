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


*** 2 variants to explore:
*** - unlimited resource; i.e., clients can ongoingly pull from / access the resource
*** - limited resource; i.e., the resource can be accessed a limited number of times


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
    rl [c2-consumes] : c1(N) => c2(N + 1) . 
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
red modelCheck(initial, ~ [] c2-alive) .

*** - is it always true that client 2 never gets resource access?
*** red modelCheck(initial, [] ~ c2-alive) .  --- bug: stack overflow


*** - eventually client2 gets resoruce access?
*** red modelCheck(initial, <> c2-alive) .  --- bug: stack overflow


*** - is it always true that eventually client 2 gets resource access?
*** red modelCheck(initial, [] <> c2-alive) .  --- bug: stack overflow

