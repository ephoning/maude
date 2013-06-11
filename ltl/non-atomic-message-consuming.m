*** EPH sept 18 2012

*** a more elaborate example of a state machine that tries to explore
*** the pitfalls of non-atomic behaviors
*** it models a simple queuing application:
*** - a single producer that queues messages
*** - 2 (competing) consumers that take messages off the queue
*** - a consumer first queries the queue to see how many messages are queued
***   in a 2nd operation, it tries to dequeue as many messages as the query result indicated
***   note the opportunity for:
***   - the producer to queue more messages in between - this is benign, as the remaining queued messages
***     can be consumed at a later time
***   - the other consumer to deqeue messages, causing the first consumer to attempt to dequeue more messages
***     than remain on the queue - this we regard as an error

in model-checker.maude

mod NON-A-MESSAGING is
    pr INT .

    sorts Producer Consumer Queue Conf .
    subsorts Producer Consumer Queue < Conf .
    sort CState . --- consumer state

    op none : -> Conf [ctor] .
    op __ : Conf Conf -> Conf [ctor assoc comm id: none] .

***    op p : -> Producer [ctor] . --- producer does not need representation in the configuration right now...
    ops c1 c2 : CState -> Consumer [ctor] .
    op q : Int -> Queue [ctor] .

    op idle : -> CState .
    op consume : Int -> CState .

    vars M N : Int .

    rl [produce] : q(M) => q(M + 1) .
    crl [poll-c1] : q(M) c1(idle) => q(M) c1(consume(M)) if M > 0 .
    rl [consume-c1] : q(M) c1(consume(N)) => q(M - N) c1(idle) .
    crl [poll-c2] : q(M) c2(idle) => q(M) c2(consume(M)) if M > 0 .
    rl [consume-c2] : q(M) c2(consume(N)) => q(M - N) c2(idle) .

endm

mod NON-A-MESSAGING-PREDS is 
    protecting NON-A-MESSAGING .
    including SATISFACTION .
    subsort Conf < State . --- note: 'State' sort is provided by prelude.maude

    var C : Conf .
    var M : Int .

    op q-error : -> Prop .
    ceq q(M) C |= q-error = true if M < 0 . --- it is a 'queue error' when its msg count is less than 0

endm

mod NON-A-MESSAGING-CHECK is
    protecting NON-A-MESSAGING-PREDS .
    including MODEL-CHECKER .
    including LTL-SIMPLIFIER .

    --- start state: queue empty, all consumers idle
    op init-q-empty-all-cs-idle : -> Conf .
    eq init-q-empty-all-cs-idle =  c1(idle) c2(idle) q(0) .

    --- start state: queue has 3 messages, c1 is about to consume 1 of them, c2 is idle
    op init-q-has-3-c1-takes-1 : -> Conf .
    eq init-q-has-3-c1-takes-1 =  c1(consume(1)) c2(idle) q(3) .

endm


***(

--- no consumer ever tries to consume more messages than currently queued (not true!, as c1 and c2 compete when polling and consuming messages non-atomically)

Maude> red modelCheck(init-q-empty-all-cs-idle, [] ~ q-error) .
reduce in NON-A-MESSAGING-CHECK : modelCheck(init-q-empty-all-cs-idle, []~ q-error) .
rewrites: 61
result ModelCheckResult: counterexample(

    {c1(idle) c2(idle) q(0),'produce} 
    {c1(idle) c2(idle) q(1),'poll-c1}                ---
    {c1(consume(1)) c2(idle) q(1),'poll-c2}          --- both consumers polled
    {c1(consume(1)) c2(consume(1)) q(1),'consume-c1} ---
    {c1(idle) c2(consume(1)) q(0),'consume-c2},      --- and both tried to consume the single message that was produced

    {c1(idle) c2(idle) q(-1),'produce}  --- the q-error state resulted from both consumers polling and both trying to consume the same queued message set
    {c1(idle) c2(idle) q(0),'produce}
    {c1(idle) c2(idle) q(1),'poll-c1}
    {c1(consume(1)) c2(idle) q(1),'poll-c2}
    {c1(consume(1)) c2(consume(1)) q(1),'consume-c1}
    {c1(idle) c2(consume(1)) q(0),'produce}
    {c1(idle) c2(consume(1)) q(1),'produce}
    {c1(idle) c2(consume(1)) q(2),'poll-c1}
    {c1(consume(2)) c2(consume(1)) q(2),'consume-c2}
    {c1(consume(2)) c2(idle) q(1),'poll-c2}
    {c1(consume(2)) c2(consume(1)) q(1),'consume-c1}
    {c1(idle) c2(consume(1)) q(-1),'consume-c2}
    {c1(idle) c2(idle) q(-2),'produce})


Maude> red modelCheck(init-q-has-3-c1-takes-1, [] ~ q-error) .
reduce in NON-A-MESSAGING-CHECK : modelCheck(init-q-has-3-c1-takes-1, []~ q-error) .
rewrites: 70
result ModelCheckResult: counterexample(
    {c1(consume(1)) c2(idle) q(3),'consume-c1}
    {c1(idle) c2(idle) q(2),'poll-c1}
    {c1(consume(2)) c2(idle) q(2),'consume-c1}
    {c1(idle) c2(idle) q(0),'produce}               --- c1 has consumed all messages
    {c1(idle) c2(idle) q(1),'poll-c1}
    {c1(consume(1)) c2(idle) q(1),'poll-c2}
    {c1(consume(1)) c2(consume(1)) q(1),'consume-c1}
    {c1(idle) c2(consume(1)) q(0),'consume-c2},     

    {c1(idle) c2(idle) q(-1),'produce}              --- and again both consumers polled and tried to consume the same queued message set => q-error
    {c1(idle) c2(idle) q(0),'produce}
    {c1(idle) c2(idle) q(1),'poll-c1}
    {c1(consume(1)) c2(idle) q(1),'poll-c2}
    {c1(consume(1)) c2(consume(1)) q(1),'consume-c1}
    {c1(idle) c2(consume(1)) q(0),'produce}
    {c1(idle) c2(consume(1)) q(1),'produce}
    {c1(idle) c2(consume(1)) q(2),'poll-c1}
    {c1(consume(2)) c2(consume(1)) q(2),'consume-c2}
    {c1(consume(2)) c2(idle) q(1),'poll-c2}
    {c1(consume(2)) c2(consume(1)) q(1),'consume-c1}
    {c1(idle) c2(consume(1)) q(-1),'consume-c2}
    {c1(idle) c2(idle) q(-2),'produce})



)

