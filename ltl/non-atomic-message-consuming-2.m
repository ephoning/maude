*** EPH sept 21 2012

*** a more elaborate example of a state machine that tries to explore
*** another messaging mechanism:
*** - 1 pool (infinite) pool of messages
*** - 2 independent consumers competing for access to the message pool

*** experiments to conduct:
*** - can 1 consumer starve the other?:    mc [] <> 'consumer 1 gets a message'
*** - ...


in model-checker.maude

mod MESSAGING is
endm

mod MESSAGING-PREDS is 
endm

mod MESSAGING-CHECK is
endm

