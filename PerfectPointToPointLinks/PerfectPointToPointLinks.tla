----------------------------- MODULE PerfectPointToPointLinks -----------------------------
EXTENDS Naturals, FiniteSets, TLAPS
    
CONSTANTS
    Procs,
    Messages

ASSUME 
    /\ Procs # {}
    /\ Messages # {}

VARIABLES
    pl_sent,
    pl_delivered

vars == << pl_sent, pl_delivered >>

----------------------------------------------------------------------------

\* Perfect point-to-point link
PL_Rich_Message == [sdr : Procs, rcv : Procs, msg : Messages]
PL_Sent == PL_Rich_Message
PL_Delivered == PL_Rich_Message

\* Send message m from p to q
pl_send(p, q, m) == 
    /\ p \in Procs
    /\ q \in Procs
    /\ LET rm == [sdr |-> p, rcv |-> q, msg |-> m]
        IN
        /\ rm \notin pl_sent
        /\ pl_sent' = pl_sent \union {rm}
        /\ UNCHANGED pl_delivered

\* Deliver message m from p to q
pl_deliver(p, q, m) == 
    /\ p \in Procs
    /\ q \in Procs
    /\ LET rm == [sdr |-> p, rcv |-> q, msg |-> m]
        IN
        /\ rm \in pl_sent
        /\ rm \notin pl_delivered
        /\ pl_delivered' = pl_delivered \union {rm}
        /\ UNCHANGED pl_sent

pl_init ==
    /\ pl_sent = {}
    /\ pl_delivered = {}

----------------------------------------------------------------------------

PL_Init ==
    /\ pl_init

PL_Next ==
    \E p \in Procs, q \in Procs, m \in Messages :
            \/ pl_send(p, q, m) 
            \/ pl_deliver(p, q, m)

PL_Spec == PL_Init /\ [][PL_Next]_vars /\ WF_vars(PL_Next)

----------------------------------------------------------------------------

PL_Inv_TypeInv ==
    /\ pl_sent \subseteq PL_Sent
    /\ pl_delivered \subseteq PL_Delivered

PL_Prop_ReliableDelivery == []<>(pl_sent \subseteq pl_delivered /\ pl_delivered \subseteq pl_sent)

\* PL2: No duplication: No message is delivered by a process more than once.
PL_Prop_NoDuplication ==
    []\A p \in Procs, q \in Procs, m \in Messages :
        [sdr |-> p, rcv |-> q, msg |-> m] \in pl_delivered => ~ENABLED pl_deliver(p, q, m)

\* PL3: No creation: If some process q delivers a message m with sender p, then m
\* was previously sent to q by process p
PL_Prop_NoCreation == [](pl_delivered \subseteq pl_sent)
\*PL_Prop_NoCreation == (pl_delivered \subseteq pl_sent)
\* PL_Prop_NoCreation ==
\*     []\A p \in Procs, q \in Procs, m \in Messages :
\*         ENABLED pl_deliver(p, q, m) => [sdr |-> p, rcv |-> q, msg |-> m] \in pl_sent

----------------------------------------------------------------------------

THEOREM THM_PL_INIT_INV == PL_Init => PL_Inv_TypeInv
PROOF
<1>1 PL_Init => PL_Inv_TypeInv
    BY DEF PL_Init, pl_init, PL_Inv_TypeInv
<1> QED
    BY <1>1

THEOREM THM_PL_NEXT_INV == PL_Next /\ PL_Inv_TypeInv => PL_Inv_TypeInv'
PROOF
<1>1 PL_Next /\ PL_Inv_TypeInv => PL_Inv_TypeInv'
    <2>1 SUFFICES ASSUME PL_Next, PL_Inv_TypeInv
        PROVE PL_Inv_TypeInv'
        BY DEF PL_Next, PL_Inv_TypeInv
    <2>2 PICK p \in Procs, q \in Procs, m \in Messages : pl_send(p, q, m) \/ pl_deliver(p, q, m)
        BY <2>1 DEF PL_Next
    <2>3 CASE pl_send(p, q, m)
        <3>1 (pl_delivered \subseteq PL_Delivered)'
            BY PL_Inv_TypeInv, pl_send(p, q, m) DEF PL_Inv_TypeInv, pl_send
        <3>2 (pl_sent' \subseteq PL_Sent)
            <4>1 pl_sent \subseteq PL_Sent
                BY PL_Inv_TypeInv DEF PL_Inv_TypeInv
            <4>2 {[sdr |-> p, rcv |-> q, msg |-> m]} \subseteq PL_Sent
                BY DEF PL_Sent, PL_Rich_Message
            <4>3 pl_sent \cup {[sdr |-> p, rcv |-> q, msg |-> m]} \subseteq PL_Sent
                BY <4>1, <4>2
            <4>4 QED
                BY pl_send(p,q,m), <4>3 DEF pl_send
        <3>4 PL_Inv_TypeInv'
            BY <3>1, <3>2 DEF PL_Inv_TypeInv
        <3>5 QED
            BY <3>4, <2>1
    <2>4 CASE pl_deliver(p, q, m)
        <3>1 (pl_delivered \subseteq PL_Delivered)'
            <4>1 pl_delivered \subseteq PL_Delivered
                BY PL_Inv_TypeInv DEF PL_Inv_TypeInv
            <4>2 {[sdr |-> p, rcv |-> q, msg |-> m]} \subseteq PL_Delivered
                BY DEF PL_Delivered, PL_Rich_Message
            <4>3 pl_delivered \cup {[sdr |-> p, rcv |-> q, msg |-> m]} \subseteq PL_Delivered
                BY <4>1, <4>2
            <4>4 QED
                BY pl_deliver(p,q,m), <4>3 DEF pl_deliver
        <3>2 (pl_sent \subseteq PL_Sent)'
            BY PL_Inv_TypeInv, pl_deliver(p, q, m) DEF PL_Inv_TypeInv, pl_deliver
        <3>4 PL_Inv_TypeInv'
            BY <3>1, <3>2 DEF PL_Inv_TypeInv
        <3>5 QED
            BY <3>4, <2>1
    <2>5 QED
        BY <2>2, <2>3, <2>4 
<1> QED
    BY <1>1

THEOREM THM_PL_NEXT_STUTTER_INV == [PL_Next]_vars /\ PL_Inv_TypeInv => PL_Inv_TypeInv'
PROOF
<1>1 PL_Next /\ PL_Inv_TypeInv => PL_Inv_TypeInv'
    BY THM_PL_NEXT_INV
<1>2 PL_Inv_TypeInv /\ UNCHANGED vars => PL_Inv_TypeInv'
    BY DEF PL_Inv_TypeInv, vars
<1>3 QED
    BY <1>1, <1>2

THEOREM PL_Spec => []PL_Inv_TypeInv
PROOF
<1>1 PL_Init => PL_Inv_TypeInv
    BY THM_PL_INIT_INV
<1>2 PL_Inv_TypeInv /\ [PL_Next]_vars => PL_Inv_TypeInv'
    BY THM_PL_NEXT_STUTTER_INV
<1>3 QED
    BY <1>1, <1>2, PTL DEF PL_Spec

----------------------------------------------------------------------------

THEOREM THM_PL_Prop_NoCreation == PL_Spec => [](pl_delivered \subseteq pl_sent)
PROOF
<1>1 PL_Init => pl_delivered \subseteq pl_sent
    BY DEF PL_Init, pl_init
<1>2 PL_Next /\ pl_delivered \subseteq pl_sent => (pl_delivered \subseteq pl_sent)'
    <2>1 SUFFICES
        ASSUME PL_Next, pl_delivered \subseteq pl_sent
        PROVE (pl_delivered \subseteq pl_sent)'
        BY DEF PL_Next
    <2>2 PICK p \in Procs, q \in Procs, m \in Messages : pl_send(p, q, m) \/ pl_deliver(p, q, m)
        BY <2>1 DEF PL_Next
    <2>. QED
        BY <2>1 DEF PL_Next, pl_send, pl_deliver
<1>3 pl_delivered \subseteq pl_sent /\ UNCHANGED vars => (pl_delivered \subseteq pl_sent)'
    BY DEF vars
<1>4 [PL_Next]_vars /\ pl_delivered \subseteq pl_sent => (pl_delivered \subseteq pl_sent)'
    BY <1>2, <1>3
<1>5 QED
    BY <1>1, <1>4, PTL DEF PL_Spec
    
----------------------------------------------------------------------------


\*BUGGY ERROR
\*THEOREM THM_PL_Prop_NoDuplication ==
\*    PL_Spec => []\A p \in Procs, q \in Procs, m \in Messages :
\*        [sdr |-> p, rcv |-> q, msg |-> m] \in pl_delivered => ~ENABLED pl_deliver(p, q, m)
\*PROOF
\*<1>1 Inv == \A p \in Procs, q \in Procs, m \in Messages : [sdr |-> p, rcv |-> q, msg |-> m] \in pl_delivered => ~ENABLED pl_deliver(p, q, m)
\*<1>2 USE DEF Inv, PL_Init, pl_init, PL_Next
\*<1>3 PL_Init => Inv
\*    OBVIOUS
\*\* Causes a bug
\*\*<1>4 PL_Next /\ Inv => Inv'
\*\*    OBVIOUS
\*<1>4 PL_Next /\ Inv => Inv'
\*    BY DEF PL_Next
\*<1>. QED

\*THEOREM THM_PL_Prop_NoDuplication ==
\*    PL_Spec => []\A p \in Procs, q \in Procs, m \in Messages :
\*        [sdr |-> p, rcv |-> q, msg |-> m] \in pl_delivered => ~ENABLED pl_deliver(p, q, m)
\*PROOF
\*<1>1 Inv == \A p \in Procs, q \in Procs, m \in Messages : [sdr |-> p, rcv |-> q, msg |-> m] \in pl_delivered => ~ENABLED pl_deliver(p, q, m)
\*<1>2 Invp == (\A p \in Procs, q \in Procs, m \in Messages : [sdr |-> p, rcv |-> q, msg |-> m] \in pl_delivered' => (~ENABLED pl_deliver(p, q, m))')
\*<1>3 USE DEF Inv, PL_Init, pl_init, PL_Next
\*<1>4 PL_Init => Inv
\*    OBVIOUS
\*\* Causes a bug
\*\*<1>4 PL_Next /\ Inv => Inv'
\*\*    OBVIOUS
\*<1>5 PL_Next /\ Inv => Invp
\*    BY SMT
\*<1>. QED

THEOREM AUX_1 == \A p \in Procs, q \in Procs, m \in Messages : 
        [sdr |-> p, rcv |-> q, msg |-> m] \in pl_delivered 
        =>
        ~ENABLED pl_deliver(p, q, m)
OMITTED

\*THEOREM THM_PL_Prop_NoDuplication ==
\*    PL_Spec => [](\A p \in Procs, q \in Procs, m \in Messages :
\*        [sdr |-> p, rcv |-> q, msg |-> m] \in pl_delivered => ~ENABLED pl_deliver(p, q, m))
\*BY AUX_1, PTL

enabled_pl_deliver(p, q, m) == 
    /\ p \in Procs
    /\ q \in Procs
    /\ LET rm == [sdr |-> p, rcv |-> q, msg |-> m]
        IN
        /\ rm \in pl_sent
        /\ rm \notin pl_delivered

THEOREM THM_PL_Prop_NoDuplication == PL_Spec => [] \A p \in Procs, q \in Procs, m \in Messages :
        [sdr |-> p, rcv |-> q, msg |-> m] \in pl_delivered => ~enabled_pl_deliver(p, q, m)
PROOF
<1>1 \A p \in Procs, q \in Procs, m \in Messages :
    ~[sdr |-> p, rcv |-> q, msg |-> m] \notin pl_delivered =>
        ~enabled_pl_deliver(p, q, m)
    BY DEF enabled_pl_deliver
<1>2 \A p \in Procs, q \in Procs, m \in Messages :
        [sdr |-> p, rcv |-> q, msg |-> m] \in pl_delivered =>  ~[sdr |-> p, rcv |-> q, msg |-> m] \notin pl_delivered
    OBVIOUS
<1>3 \A p \in Procs, q \in Procs, m \in Messages :
        [sdr |-> p, rcv |-> q, msg |-> m] \in pl_delivered =>  ~enabled_pl_deliver(p, q, m)
    BY <1>1, <1>2
<1>4 []\A p \in Procs, q \in Procs, m \in Messages :
        [sdr |-> p, rcv |-> q, msg |-> m] \in pl_delivered =>  ~enabled_pl_deliver(p, q, m)
    BY <1>3, PTL
<1>5 PL_Spec => []\A p \in Procs, q \in Procs, m \in Messages :
        [sdr |-> p, rcv |-> q, msg |-> m] \in pl_delivered =>  ~enabled_pl_deliver(p, q, m)
    BY <1>4
<1>. QED
   BY <1>5


----------------------------------------------------------------------------

\* PL1: Reliable delivery: If a correct process p sends a message m to a correct
\*      process q, then q eventually delivers m.
THEOREM THM_PL_Reliable_Delivery ==
    PL_Spec => \A p \in Procs, q \in Procs, m \in Messages : 
            LET rm == [sdr |-> p, rcv |-> q, msg |-> m]
            IN
                rm \in pl_sent => <>(rm \in pl_delivered)
PROOF
\* We start the proof by introducing the assumptions
\* and some useful definitions
<1>1 SUFFICES ASSUME PL_Spec PROVE \A p \in Procs, q \in Procs, m \in Messages : 
    LET rm == [sdr |-> p, rcv |-> q, msg |-> m]
    IN
    rm \in pl_sent => <>(rm \in pl_delivered)
    PROOF OBVIOUS
<1>2 TAKE p \in Procs, q \in Procs, m \in Messages
<1>3 DEFINE rm == [sdr |-> p, rcv |-> q, msg |-> m]

<1>4 \A A : [](A \/ ~A)
    PROOF OBVIOUS

\* It is always the case that pl_deliver either it is enabled or not enabled
<1>5 [](enabled_pl_deliver(p, q, m) \/ ~enabled_pl_deliver(p, q, m))
    PROOF BY <1>4, PTL
 
\* Thus, we can trivially also show this using <1>5
<1>6 rm \in pl_sent => [](enabled_pl_deliver(p, q, m) \/ ~enabled_pl_deliver(p, q, m))
    PROOF BY <1>5

\* By the weak fairness condition in PL_Spec, it cannot 
\* be the case that enabled_pl_deliver remains forever enabled 
<1>55 rm \in pl_sent => ~[]enabled_pl_deliver(p, q, m)
    PROOF OMITTED

\* This is a standard temporal tautology
<1>66 ASSUME NEW A PROVE
     /\ [](A \/ ~A) 
     /\ ~[]A
     => <>~A
    PROOF OMITTED

\* We can show the following by first combinging <1>4 and <1>5, 
\* followed by applying the temporal tautology <1>6
<1>7 rm \in pl_sent => <>~enabled_pl_deliver(p, q, m)

\* By inspecting enaled_pl_deliver, we can show the following
<1>8 /\ ~enabled_pl_deliver(p, q, m) 
     /\ p \in Procs 
     /\ q \in Procs 
     /\ rm \in pl_sent =>
          rm \in pl_delivered

\* Step <1>8 can be simplified, as we have that p and q are already
\* assumed to be Procs. Thus the following will hold.
<1>9 ~enabled_pl_deliver(p, q, m) /\ rm \in pl_sent => rm \in pl_delivered
    BY <1>8

\* We can show that once rm is sent, it remains sent, this is a stable property
<1>11 rm \in pl_sent => []( rm \in pl_sent )
    PROOF OMITTED

<1>T ASSUME NEW A, NEW B PROVE
    (A => B)
    =>
    (<>A => <>B)
    OMITTED

\* Follows from the temporal tautology that A => B implies <>A => <>B
<1>10 <>( ~enabled_pl_deliver(p, q, m) /\ rm \in pl_sent ) => <>( rm \in pl_delivered )
    OMITTED
    
<1>12 <>( ~enabled_pl_deliver(p, q, m) ) /\ []( rm \in pl_sent ) =>
        <>( ~enabled_pl_deliver(p, q, m) /\ rm \in pl_sent )
    BY PTL

<1>13 (rm \in pl_sent) => (
    ([]( rm \in pl_sent )) => 
        (<>( ~enabled_pl_deliver(p, q, m) ) => <>( rm \in pl_delivered ))
    )
    BY <1>12, <1>10

<1>14 (rm \in pl_sent) => <>( rm \in pl_delivered )
    BY <1>11, <1>7, <1>13

<1>. QED
    BY <1>14


        
\*THEOREM AXIOM_ENABLED == ENABLED TRUE
\*OMITTED
\*
\*THEOREM ASSUME NEW A PROVE (A => ENABLED A)
\*PROOF
\*<1>1 SUFFICES 
\*        ASSUME A
\*        PROVE ENABLED A
\*    OBVIOUS
\*<1>2 A = TRUE
\*    BY <1>1
\*<1>3 (ENABLED A) = (ENABLED TRUE)
\*    BY <1>2, PTL
\*<1>4 SUFFICES ASSUME A = TRUE PROVE ENABLED TRUE
\*    BY AXIOM_ENABLED, PTL, <1>2 
\*\*<1>3 ENABLED A
\*\*    BY AXIOM_ENABLED, <1>2
\*<1> QED

\*THEOREM ASSUME NEW ACTION TRUE PROVE (ENABLED TRUE) BY ExpandENABLED




=============================================================================


