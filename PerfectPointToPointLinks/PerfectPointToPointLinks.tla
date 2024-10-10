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

\* Perfect point-to-point link data types
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

----------------------------------------------------------------------------

PL_Init ==
    /\ pl_sent = {}
    /\ pl_delivered = {}

PL_Next ==
    \E p \in Procs, q \in Procs, m \in Messages :
            \/ pl_send(p, q, m) 
            \/ pl_deliver(p, q, m)

\* Besides Init and Next, we also include a weak fairness requirement on the Next step formula,
\* this will help in checking the liveness properties, as it will force a delivery action
\* to occur if it is forever enabled.
PL_Spec == PL_Init /\ [][PL_Next]_vars /\ WF_vars(PL_Next)

----------------------------------------------------------------------------
\* Model checking
\* We check the following properties using the TLA+ model checker

\* A type invariant on the execution for the variables.
PL_Inv_TypeInv ==
    /\ pl_sent \subseteq PL_Sent
    /\ pl_delivered \subseteq PL_Delivered

\* PL1: Reliable delivery: If a correct process p sends a message m to a correct
\*      process q, then q eventually delivers m.
\* Here, we model this property simply by that always eventually the sent and delivered
\* sets have to contain the same messages (when there are no failures).
PL_Prop_ReliableDelivery == []<>(pl_sent \subseteq pl_delivered /\ pl_delivered \subseteq pl_sent)

\* PL2: No duplication: No message is delivered by a process more than once.
PL_Prop_NoDuplication ==
    []\A p \in Procs, q \in Procs, m \in Messages :
        [sdr |-> p, rcv |-> q, msg |-> m] \in pl_delivered => ~ENABLED pl_deliver(p, q, m)

\* PL3: No creation: If some process q delivers a message m with sender p, then m
\*      was previously sent to q by process p
PL_Prop_NoCreation == [](pl_delivered \subseteq pl_sent)

----------------------------------------------------------------------------
\* TLAPS Proof System
\* We also tried to prove these properties using the TLAPS proof system.
\* The proofs occur in the same order

\* First, we provide a proof for the type invariant.

THEOREM THM_PL_INIT_INV == PL_Init => PL_Inv_TypeInv
PROOF
<1>1 PL_Init => PL_Inv_TypeInv
    BY DEF PL_Init, PL_Inv_TypeInv
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

\* PL1: Reliable delivery: If a correct process p sends a message m to a correct
\*      process q, then q eventually delivers m.

\* To my knowledge there is currently no way to prove things using the
\* "ENABLED" keyword
THEOREM ENABLED TRUE
PROOF OBVIOUS

THEOREM \A A : A => ENABLED A
PROOF OBVIOUS

\* Let's define ENABLED manually instead
enabled_pl_deliver(p, q, m) == 
    /\ p \in Procs
    /\ q \in Procs
    /\ LET rm == [sdr |-> p, rcv |-> q, msg |-> m]
        IN
        /\ rm \in pl_sent
        /\ rm \notin pl_delivered 

THEOREM THM_PL_Reliable_Delivery ==
    PL_Spec => \A p \in Procs, q \in Procs, m \in Messages : 
            LET rm == [sdr |-> p, rcv |-> q, msg |-> m]
            IN
                rm \in pl_sent => <>( rm \in pl_delivered )
PROOF
<1>1 SUFFICES ASSUME PL_Spec PROVE \A p \in Procs, q \in Procs, m \in Messages : 
    LET rm == [sdr |-> p, rcv |-> q, msg |-> m]
    IN
    rm \in pl_sent => <>(rm \in pl_delivered)
    PROOF OBVIOUS
<1>2 TAKE p \in Procs, q \in Procs, m \in Messages
<1>3 DEFINE rm == [sdr |-> p, rcv |-> q, msg |-> m]
<1>4 \A A : [](A \/ ~A)
    PROOF OBVIOUS
<1>5 [](enabled_pl_deliver(p, q, m) \/ ~enabled_pl_deliver(p, q, m))
    PROOF BY <1>4, PTL
<1>6 rm \in pl_sent => [](enabled_pl_deliver(p, q, m) \/ ~enabled_pl_deliver(p, q, m))
    PROOF BY <1>5

\* By the weak fairness condition in PL_Spec, it cannot 
\* be the case that enabled_pl_deliver remains forever enabled 
<1>7 rm \in pl_sent => ~[]enabled_pl_deliver(p, q, m)
    PROOF OMITTED

<1>8 \A A : ~[]A => <>(~A)
    PROOF OBVIOUS
<1>9 rm \in pl_sent => <>~enabled_pl_deliver(p, q, m)
    PROOF BY <1>6, <1>7, <1>8, PTL
<1>10 /\ ~enabled_pl_deliver(p, q, m) 
     /\ p \in Procs 
     /\ q \in Procs 
     /\ rm \in pl_sent =>
          rm \in pl_delivered
    PROOF BY DEF enabled_pl_deliver
<1>11 (~enabled_pl_deliver(p, q, m) /\ rm \in pl_sent) => rm \in pl_delivered
    BY <1>10
<1>12 rm \in pl_sent => []( rm \in pl_sent )
    PROOF OMITTED \* Should be easy to prove as a stable property 
<1>13 \A A, B : (A => B) => (<>(A) => <>(B))
    PROOF OBVIOUS
<1>14 <>( ~enabled_pl_deliver(p, q, m) /\ rm \in pl_sent ) => <>( rm \in pl_delivered )
    PROOF OMITTED \* Should be obvious from <1>11 and <1>13
<1>15 <>( ~enabled_pl_deliver(p, q, m) ) /\ []( rm \in pl_sent ) =>
        <>( ~enabled_pl_deliver(p, q, m) /\ rm \in pl_sent )
    BY PTL
<1>16 (rm \in pl_sent) => (
    ([]( rm \in pl_sent )) => 
        (<>( ~enabled_pl_deliver(p, q, m) ) => <>( rm \in pl_delivered ))
    )
    BY <1>15, <1>14
<1>17 (rm \in pl_sent) => <>( rm \in pl_delivered )
    BY <1>12, <1>9, <1>16
<1>18 QED
    BY <1>17

----------------------------------------------------------------------------

\* PL2: No duplication: No message is delivered by a process more than once.

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

\*PL3: No creation: If some process q delivers a message m with sender p, then m
\*     was previously sent to q by process p.

THEOREM THM_PL_Prop_NoCreation == PL_Spec => [](pl_delivered \subseteq pl_sent)
PROOF
<1>1 PL_Init => pl_delivered \subseteq pl_sent
    BY DEF PL_Init
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
    
=============================================================================

