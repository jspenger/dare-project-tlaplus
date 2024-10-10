# DARE TLAPlus Project

## How to run
The most reliable way to run the TLA+ models is to use the TLA+ Toolbox.
The models should be available once loaded.
To trigger TLAPS to check the proofs, use the keyboard command `COMMAND-G-G`.
Using TLAPS may require some further installation.

## Project scope

The project consists of three parts.

### Perfect Point-to-Point Links
First, the project has a TLA+ specification for Perfect Point-to-Point Links. 
This is a simple communication abstraction, for sending and receiving messages between processes.
It consists of the following.
* The specification can be found in `PerfectPointToPointLinks.tla`.
* A TLA+ spec of Module 2.3: Interface and properties of perfect point-to-point [1]
* Definitions of the properties of the module
* A model which checks the properties.
* TLAPS proofs for the properties. The proofs are almost complete, there are still some small things which need to be proven

The model has the following parameters, terminating in circa 34 seconds:
```
Procs = {1, 2}
Messages = {1, 2, 3}
```

### Best-Effort Broadcast
Second, there is a TLA+ specification for a Best-Effort Broadcast.
It is a simple module which implements a broadcast abstraction using the perfect links.
Conceptually, it has two operations: broadcasting a message to all other processes, and delivering a message to a process.
It consists of the following.
* The specification can be found in `BestEffortBroadcast.tla`
* A TLA+ spec of Module 3.1 / Algorithm 3.1: Interface and properties of best-effort broadcast [1]
* Definitions of the properties of the module
* A model which checks the properties four properties: TypeInv; BEB1-3

The model has the following parameters, terminating in circa 10 seconds:
```
Procs = {1, 2, 3}
Messages = {1, 2, 3, 4}
Correct = {1, 2}
```

Messages corresponds to the total number of broadcast messages in the model, e.g. one process may broadcast 3 messages, or all processes broadcast 1 message each, etc.

### FIFO-Order Broadcast
Lastly, there is a TLA+ specification for a FIFO-Order Broadcast.
It extends and modifies the Best-Effort Broadcast to enforce a FIFO-ordered delivery of messages.
* The specification can be found in `FIFOBroadcast.tla`
* A TLA+ spec for a best-effort broadcast with an additional FIFO property
* Definitions of the properties of the module
* A model which checks the properties five properties: TypeInv; BEB1-3; FIFO order
* An almost complete TLAPS proof for the "NoDuplication" property.

The model has the following parameters, terminating in circa 10 seconds:
```
Procs = {1, 2, 3}
Messages = {1, 2, 3}
Correct = {1, 2}
```

Due to the increased bookkeeping and state, the model checking is slower, so we opted for fewer messages, so that it terminates within a comfortable time frame.

## References
> [1] Cachin, Christian, Rachid Guerraoui, and Luís Rodrigues. Introduction to reliable and secure distributed programming. Springer Science & Business Media, 2011.
