# DARE TLAPlus Project

## How to run
The best way to use these files is via the TLA+ Toolbox, as I have not found a way to reliably run this from the command line or from VS Code.

To trigger TLAPS, the TLA+ Proof System, use the keyboard command `COMMAND-G-G`.
Using TLAPS may require some further installations.

The models should be available once loaded.

## Project scope

The project consists of three parts.

### Perfect Point-to-Point Links
First, we have a TLA+ specification for Perfect Point-to-Point Links. 
This is a simple communication abstraction, for seding and receiving messages between processes.
It consists of the following.
* The specification can be found in `PerfectPointToPointLinks.tla`.
* A TLA+ spec of Module 2.3: Interface and properties of perfect point-to-point [1]
* Definitions of the properties of the module
* A model which checks the properties for 2 processes which each send 2 messages to each other (including themselves), i.e. 4 messages in total
* TLAPS proofs for the properties. The proofs are almost complete, there are still some small things which need to be proven

### Broadcast
* We limit the total number of messages sent in the system to a number, not to a number per process.

## References
> [1] Cachin, Christian, Rachid Guerraoui, and Luís Rodrigues. Introduction to reliable and secure distributed programming. Springer Science & Business Media, 2011.


<!-- TLC threw an unexpected exception.

This was probably caused by an error in the spec or model.

See the User Output or TLC Console for clues to what happened.

The exception was a java.lang.RuntimeException

: TLC encountered a non-enumerable quantifier bound

Nat.

line 108, col 18 to line 108, col 20 of module FIFOBroadcast

Show error trace
The error occurred when TLC was evaluating the nested

expressions at the following positions:

0. 
Line 107, column 5 to line 113, column 59 in FIFOBroadcast

1. 
Line 107, column 8 to line 107, column 25 in FIFOBroadcast

2. 
Line 108, column 8 to line 111, column 89 in FIFOBroadcast

 -->