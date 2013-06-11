--- EPH sept 14 2012
---
--- attempt to perform model checking on a most basic state machine
--- consisting of 2 vertices, a and b, that pass a token around
---
--- some behaviors to check:
--- either a or b holds the token (not true)
--- both a and b can be not holding the token simultaneously (true)
--- it is never the case that both a and b are holding the token
---
in model-checker.maude

mod TOKENRING is
    sorts VLabel VState Vertex Token Conf .
    subsorts Token Vertex < Conf .
    op none : -> Conf [ctor] .
    op __ : Conf Conf -> Conf [ctor assoc comm id: none] .
    ops a b : -> VLabel [ctor] .
    ops empty * : -> VState [ctor] .
    op [_,_] : VLabel VState -> Vertex [ctor] .
    ops *-to-a *-to-b : -> Token [ctor] .
    rl [a-enter] : *-to-a [a, empty] => [a, *] .
    rl [b-enter] : *-to-b [b, empty] => [b, *] .
    rl [a-exit] : [a, *] => [a, empty] *-to-b .
    rl [b-exit] : [b, *] => [b, empty] *-to-a .
endm

--- note: the basic predicates in this example are most basic: they reflect 1-to-1 the 'state' of the vertices
mod TOKENRING-PREDS is 
    protecting TOKENRING .
    including SATISFACTION .
    subsort Conf < State .
    op empty : VLabel -> Prop .
    op holding-* : VLabel -> Prop .
    op token-in-flight : -> Prop .
    var VL : VLabel .
    var C : Conf .
    var P : Prop .

    eq [VL, empty] C |= empty(VL) = true .    --- in a config where a vertex is empty, the vertex-is-empty predicate is true
    eq [VL, *] C |= holding-*(VL) = true .    --- in a config where a vertex hold the token, the vertex-is-holding-token is true

    eq *-to-a C |= token-in-flight = true .
    eq *-to-b C |= token-in-flight = true .

    eq C |= P = false [owise] . --- catch-all (required?)
endm

mod TOKENRING-CHECK is
    protecting TOKENRING-PREDS .
    including MODEL-CHECKER .
    including LTL-SIMPLIFIER .

    --- start state: a holds token
    op init-a-holding-* : -> Conf .
    eq init-a-holding-* = [a, *] [b, empty] .

    --- state state: b just released token
    op init-b-released-* : -> Conf .
    eq init-b-released-* = [a, empty] [b, empty] *-to-a .
endm


***(

--- either a or b holds the token (not expected to be true)
*** red modelCheck(init-a-holding-*, [] holding-*(a) \/ holding-*(b)) .

Maude> red modelCheck(init-a-holding-*, [] holding-*(a) \/ holding-*(b)) .
reduce in TOKENRING-CHECK : modelCheck(init-a-holding-*, holding-*(b) \/ []holding-*(a)) .
rewrites: 23
result ModelCheckResult: 
    counterexample({[a,*] [b,empty],'a-exit}, 
                   {*-to-b [a,empty] [b,empty],'b-enter}    <- start of 2nd transition list shows details on counterexample:
                   {[a,empty] [b,*],'b-exit}                   it shows the vertices in which both a and b are empty =>
                   {*-to-a [a,empty] [b,empty],'a-enter}       it is NOT the case that either a or b hold the token
                   {[a,*] [b,empty],'a-exit})                  (thus our check failed, as expected)


--- both a and b can be not holding the token simultaneously (true)
*** red modelCheck(init-a-holding-*, [] ~(holding-*(a) /\ holding-*(b))) .

Maude> red modelCheck(init-a-holding-*, [] ~(holding-*(a) /\ holding-*(b))) .
reduce in TOKENRING-CHECK : modelCheck(init-a-holding-*, []~ (holding-*(a) /\ holding-*(b))) .
rewrites: 22
result Bool: true

    as expected, it is shown that it is never the case that both a and b are holding the token

--- a token is not in flight AND held by either a or b
*** red modelCheck(init-a-holding-*, [] ~(token-in-flight /\ (holding-*(a) \/ holding-*(b)))) .

Maude> red modelCheck(init-a-holding-*, [] ~(token-in-flight /\ (holding-*(a) \/ holding-*(b)))) .
reduce in TOKENRING-CHECK : modelCheck(init-a-holding-*, []~ (token-in-flight /\ (holding-*(a) \/ holding-*(b)))) .
rewrites: 38
result Bool: true

   true, as exptected
)

     