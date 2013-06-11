--- EPH sept 14 2012
---
--- attempt to perform model checking on a most basic state machine
--- consisting of 2 vertices, a and b, that pass a token around
---
--- different from test1.m:
---  added 'state' items to Conf to see if we can "break" the notion of a
---  cycle when caclulating a counterexample by forcing the Conf into an 'inactive'
---  state which avoids further rule application
---
---
---
--- some behaviors to check:
--- either a or b holds the token (not true)
--- both a and b can be not holding the token simultaneously (true)
--- it is never the case that both a and b are holding the token
---
in model-checker.maude

mod TOKENRING is
    sorts VLabel VState Vertex Token RunState Conf .
    subsorts Token Vertex RunState < Conf .
    op none : -> Conf [ctor] .
    op __ : Conf Conf -> Conf [ctor assoc comm id: none] .
    ops a b : -> VLabel [ctor] .
    ops active inactive : -> RunState .
    ops empty * : -> VState [ctor] .
    op [_,_] : VLabel VState -> Vertex [ctor] .
    ops *-to-a *-to-b : -> Token [ctor] .
    rl [a-enter] : *-to-a [a, empty] active => [a, *] active .
    rl [b-enter] : *-to-b [b, empty] active => [b, *] active .
    rl [a-exit] : [a, *] active => [a, empty] *-to-b active .
    rl [b-exit] : [b, *] active => [b, empty] *-to-a inactive .   ---- forcing inactive state
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
    eq init-a-holding-* = [a, *] [b, empty] active .
endm


--- either a or b holds the token (not expected to be true)
*** red modelCheck(init-a-holding-*, [] holding-*(a) \/ holding-*(b)) .

***(

Maude> red modelCheck(init-a-holding-*, [] holding-*(a) \/ holding-*(b)) .
reduce in TOKENRING-CHECK : modelCheck(init-a-holding-*, holding-*(b) \/ []holding-*(a)) .
rewrites: 22
result ModelCheckResult: counterexample({active [a,*] [b,empty],'a-exit}
                                        {active *-to-b [a,empty] [b,empty],'b-enter}
                                        {active [a,empty] [b,*],'b-exit}, 

                                        {inactive *-to-a [a,empty] [b,empty],deadlock})

)

