# The technical and cultural design of Rok.

## project values

- **Correctness**: this project should be a flexible toolkit capable of verifying and compiling any software for any architecture or environment. It should make it as easy as possible to model the abstractions presented by any hardware or software environment with full and complete fidelity.
- **Clarity**: this project should be accessible to as many people as possible. It doesn't matter how powerful a tool is if no one can understand it. An unclear explanation is often worse than none. Speak plainly enough non-experts can understand. If a topic has prerequisites, point readers toward them.
- **Practicality**: a tool must be usable, both in terms of the demands it makes and its design. This tool is intended to be used by busy people building real things with real stakes.
- **Performance**: often those programs which absolutely must be fast are also those which absolutely must be correct. Infrastructural software is constantly depended on, and must deliver results as quickly as possible.

These values inherently reinforce one another. As we gain more ability to guarantee correctness, we can make programs faster and solve more useful and practical problems. As our tools become faster, they become more usable. As we improve clarity, more people gather to help improve the project, making it even better in every way.

secondary values, simplicity before consistency before completeness.


discuss what's been done so far, and what needs to be done from here


# progress and roadmap

## phase 0, fully specifying real computation, but abstractly (flint)

termination verification condition generator based on strongly connected components

reasoning about intentionally infinite programs, what does it mean for an infinite program to be "correct"? productive looping, any infinite program can always be modeled as a single infinite loop with a possible state switch describing what inner function to perform, and that inner function must terminate normally

integrating with iris, can this direct full fidelity approach fit with iris' design?

defining everything as literal bit arrays instead of some proxy

splittable effects
non-deterministic reads
termination
known code execution

abstraction over concrete machines

## phase 1, bootstrapping the rok compiler (spark)

specifying calculus of constructions in coq (reusing coqcoqcorrect)

defining an abstract assembly language program that implements the proof checking kernel

building parser/renderer that can translate that assembly language program (and maybe it's higher-level forms?) into some usable machine code program, possibly reusing something like llvm but also possibly just going directly into x86?


this is really as far as the core project will likely have to go, once something is usable it will hopefully be much easier to attract outside contributions

## phase 2, build standard library and educational materials (hearth)

figure out initial interop story with other proof assistants (interop with programs is baked into the inherent interop of assembly language, you just have to define calling/memory conventions etc on a case-by-case basis)

in this phase we aim at releasing a stable first version

## phase 3, build ergonomic tools (torch)

unified check/build/run tool
package management
syntax highlighting/language server

## phase 4, build the whole ecosystem! (many torches!)
