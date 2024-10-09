------------------------ MODULE BestEffortBroadcast ------------------------

EXTENDS 
    Naturals,
    FiniteSets

CONSTANTS
    Procs,
    Messages,
    Correct

ASSUME
    /\ Procs # {}
    /\ Messages # {}
    /\ Correct \in SUBSET Procs

BC_Message == [sdr : Procs, msg : Messages]

----------------------------------------------------------------------------

\* Let's import the perfect point-to-point links spec
\* See the PerfectPointToPointLink module for more details

\* > "I have observed that many new users want to write TLA+ specs so they
\* > can be reused.  I have one word of advice for those users: Don't."
\* > https://groups.google.com/g/tlaplus/c/BHBNTkJ2QFE/m/meTQs4pHBwAJ

VARIABLES
    pl_sent,
    pl_delivered

pl_vars == << pl_sent, pl_delivered >>

PL_Rich_Message == [sdr : Procs, rcv : Procs, msg : BC_Message]
PL_Sent == PL_Rich_Message
PL_Delivered == PL_Rich_Message

pl_bcast_send(p, qs, m) == 
    /\ p \in Procs
    /\ qs \subseteq Procs
    /\ LET rms == {[sdr |-> p, rcv |-> q, msg |-> m] : q \in qs }
            IN
            /\ \A rm \in rms : rm \notin pl_sent
            /\ pl_sent' = pl_sent \union rms
            /\ UNCHANGED pl_delivered

pl_send(p, q, m) == 
    /\ p \in Procs
    /\ q \in Procs
    /\ LET rm == [sdr |-> p, rcv |-> q, msg |-> m]
        IN
        /\ rm \notin pl_sent
        /\ pl_sent' = pl_sent \union {rm}
        /\ UNCHANGED pl_delivered

pl_deliver(p, q, m) == 
    /\ p \in Procs
    /\ q \in Procs
    /\ LET rm == [sdr |-> p, rcv |-> q, msg |-> m]
        IN
        /\ rm \in pl_sent
        /\ rm \notin pl_delivered
        /\ pl_delivered' = pl_delivered \union {rm}
        /\ UNCHANGED pl_sent

PL_Init ==
    /\ pl_sent = {}
    /\ pl_delivered = {}

----------------------------------------------------------------------------

\* Back to the best-effort broadcast module

vars == << pl_vars >>

----------------------------------------------------------------------------

\* broadcast message m from process p
beb_broadcast(p, m) ==
    LET qs == Procs IN
    LET bc_msg == [sdr |-> p, msg |-> m]
        IN
        pl_bcast_send(p, qs, bc_msg)

\* deliver a broadcast message m to process p from process q
beb_deliver(p, q, m) == 
    LET bc_msg == [sdr |-> q, msg |-> m]
        IN
        pl_deliver(q, p, m)

Init == 
    /\ PL_Init

Next == \E p \in Procs, q \in Procs, m \in Messages : 
    \/ beb_broadcast(p, m)
    \/ beb_deliver(p, q, m)

Spec ==
    /\ Init
    /\ [][Next]_vars

----------------------------------------------------------------------------

\* Let's check some properties with TLC

TypeInv ==
    /\ pl_sent \subseteq PL_Sent
    /\ pl_delivered \subseteq PL_Delivered

=============================================================================
\* Modification History
\* Last modified Wed Oct 09 11:12:20 CEST 2024 by jonasspenger
\* Created Wed Oct 09 10:21:00 CEST 2024 by jonasspenger

