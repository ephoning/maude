in model-checker.maude

mod MUTEX is
    sorts Name Mode Proc Token Conf .
    subsorts Token Proc < Conf .
    op none : -> Conf [ctor] .
    op __ : Conf Conf -> Conf [ctor assoc comm id: none] .
    ops a b : -> Name [ctor] .
    ops wait critical : -> Mode [ctor] .
    op [_,_] : Name Mode -> Proc [ctor] .
    ops * $ : -> Token [ctor] .
    rl [a-enter] : $ [a, wait] => [a, critical] .
    rl [b-enter] : * [b, wait] => [b, critical] .
    rl [a-exit] : [a, critical] => [a, wait] * .
    rl [b-exit] : [b, critical] => [b, wait] $ .
endm

mod MUTEX-PREDS is 
    protecting MUTEX .
    including SATISFACTION .
    subsort Conf < State .
    op crit : Name -> Prop .
    op wait : Name -> Prop .
    var N : Name .
    var C : Conf .
    var P : Prop .
    eq [N, critical] C |= crit(N) = true .
    eq [N, wait] C |= wait(N) = true .
    eq C |= P = false [owise] .
endm

mod MUTEX-CHECK is
    protecting MUTEX-PREDS .
    including MODEL-CHECKER .
    including LTL-SIMPLIFIER .
    ops initial1 initial2 : -> Conf .
    eq initial1 = $ [a, wait] [b, wait] . 
    eq initial2 = * [a, wait] [b, wait] .
endm

*** red modelCheck(initial1, [] ~(crit(a) /\ crit(b))) .
*** red modelCheck(initial2, [] ~(crit(a) /\ crit(b))) .
*** red modelCheck(initial1, ([]<> wait(a)) -> ([]<> crit(a))) .

*** red modelCheck(initial1, [] wait(b)) .
