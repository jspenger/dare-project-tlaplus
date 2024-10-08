# DARE TLAPlus Project

## How to run
The best way to use these files is via the TLA+ Toolbox, as I have not found a way to reliably run this from the command line or from VS Code.

To trigger TLAPS, the TLA+ Proof System, use the keyboard command `COMMAND-G-G`.
Using TLAPS may require some further installations.

The models should be available once loaded.

## Project scope

The project consists of three parts.

First, we have a TLA+ specification for Perfect Point-to-Point Links. 
This is a simple communication abstraction, for seding and receiving messages between processes.
It consists of the following.
* The specification can be found in `PerfectPointToPointLinks.tla`.
* A TLA+ spec of Module 2.3: Interface and properties of perfect point-to-point [1]
* Definitions of the properties of the module
* A model which checks the properties for 2 processes which each send 2 messages to each other (including themselves), i.e. 4 messages in total
* TLAPS proofs for the properties. The proofs are almost complete, there are still some small things which need to be proven

## References
> [1] Cachin, Christian, Rachid Guerraoui, and Luís Rodrigues. Introduction to reliable and secure distributed programming. Springer Science & Business Media, 2011.
