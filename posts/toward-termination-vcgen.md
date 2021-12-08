we want to do this rather than simply think at a higher level of abstraction for two reasons:

- we want the power and flexibility to prove termination of more exotic programs that can't be represented with simple functions (goto statements, algebraic effects, jumping to dynamic code, etc)
- we need a foundation of reasoning *upon which to build those higher levels of abstraction!* the whole point of magmide is that we're extending our formal understanding as far down as we possibly can, so that we can combine upwards with confidence we haven't merely assumed something without cause.



in order to prove an assembly language program terminates, we have to present two things:

- some well-founded relation that we can somehow convert a machine state into (the relation could be directly over machine states)
- a proof that the assembly step relation will, for our particular program, always make "progress" in the well-founded relation, by moving with each instruction into a machine state that is "less than" the previous one with regard to the relation

A natural way to do this is by doing the following:

- chop up our program into labeled blocks, much like the "basic blocks" of llvm (although we don't have to be as perfectly strict as those)
- create a directed graph of the program with these labeled blocks as nodes, and possible jumps as edges
- define a block that is intended to be the "starting" block of execution, and create an artificial "start" node representing any position which could in a well-formed way jump to our program, and create an edge from the start block to our real start block (an environment could choose to load our program and jump to some arbitrary instruction, but it makes sense to just require as a precondition of correct execution that a predefined starting instruction is used instead) (we likely want to simply declare some instruction as the defined starting point, and package this instruction together with the program to define the program as a broader "executable", or even just rearrange the program so that the desired starting instruction is always the very first one)
- include an artificial "stop" node and create edges to it from all blocks that stop execution
- find all the strongly connected components of the graph with an algorithm such as tarjan's. with the DAG of components, topographically order them according to their maximum distance from stop. this maximum distance number forms the first and highest index of our lexicographic ordering
- now for each component we have to find a well-founded ordering. if each component is truly strongly connected (isn't just a non-recursive single node), then the programmer will likely have to provide a well-founded ordering, but we can go a little farther.

in each component, we can do a similar exercise:

- find the nodes that are actually jumped to from nodes outside the component, and create a new artificial "start" node that points to them
- find the nodes that have jumps exiting the component, and create a new artificial "stop" node they point to
- go through and find a maximum distance from stop for each node. this number won't necessarily create a topographical order, but it does create topographic *classes* we can use
- go through each topographic class, and find out if the class itself has any strongly connected subdivisions. if there are any subdivisions within the class then we can create a topographic ordering within the class
- every strongly connected component within a class needs to have a well-founded ordering provided by the programmer, and a proof that that ordering is decremented by the time execution leaves the class component

*cleverly*, we only have to flag an edge for justification within the same distance class (that isn't a self-edge) if the distance class isn't itself strongly connected.
also, it will *probably* be a better and more pleasant or correct experience if self-recursive nodes just get their own separate well-founded ordering and each individual recursive edge needs to be justified along that ordering. *MAYBE??* I guess if the work done by self-edges is related to the total progress of the whole component then they can just somehow incorporate the structures being progressed by self-edges into the structure being progressed by the component.


what we're trying to do is fill in all the "obvious" portions. we want to only make them provide an *interesting* ordering that somehow relates to the semantics of their program, and then only make them justify steps in the program that really do truly need to respect that ordering. any tedious book-keeping we can do for them we should try to do


things to watch out for:

- "trapped jumps", any kind of jump that refers to the label of itself. it can be proven that if a program ever is in a state such that an instruction jumps to itself, the program will be permanently stuck on that instruction, and will never make any kind of useful progress in any well-founded relation. the machine state will never change, since even the program counter will remain the same








lexicographic orderings have "higher priority" indices

a program is a list of labeled sections
we can go over that list and produce a directed graph of all instructions that go from one labeled section to another:
- obviously branching instructions that go to a label count, even ones that go to the same labeled section since that's a recursive branch
- any possibly sequential instructions at the *end* of a section go to the *next* section, so they also count

from this graph, we can produce a list of strongly connected components, and the network of strongly connected components forms a DAG
this DAG from the single starting instruction to all possible exit nodes (nodes that include an exit instruction) is well-founded, since we're decreasing the current maximum distance from an exit node. this forms the first and highest priority index in our total lexicographic order
the case of non-recursive single-node components is trivial, since these aren't really strongly connected, and always first move sequentially through the section before always progressing along the DAG

with this, we can prove termination if we're given a progress type/relation/function/proof for each component
to narrow the instructions who need to be justified, we can look at each strongly connected component, and topographically order the nodes according to their maximum distance from an exit node (any node that exits the component)
when they're ordered like this, we can imagine them as a DAG again by "severing" the "backwards" edges, ones that go toward a topographically lower node
then we can supply a lexicographical ordering for this component by just push *their* decreasing type on the front of the same ordering we would produce for a *real* DAG. their supplied progress type will have the highest priority, since it represents the entire chunk of work the component is trying to do, and the rest of the ordering just handles all the boring book-keeping as we go along through this "severed" DAG.
we give to them obligations that the "backwards" or recursive edges (or Steps) do in fact make progress.
it will probably be necessary for sanity's sake to simply require a proof that the progress indicator gets decreased *sometime* before any backward edge

or we need an even higher version of Steps, one that encodes program progression across section nodes rather than individual instructions. probably the final version requires us to prove that if a progression relation across section nodes is well-founded, then the underlying step progression is as well

```v
  forall (T: Type) (progress: T -> T -> Prop) (convert: MachineState -> T), well_founded progress
  forall cur next, Step cur next -> Within cur component -> Within next component -> progress (convert next) (convert cur)
```

so if we exit the segment, we've made progress
within the segment we can just say we're making sequential progress?




probably to prove a jump to dynamic code will terminate or just behave properly, we need to have the programmer provide a list of resumption locations in the current graph (which could be the exit location!) and prove the code they're jumping to will in fact only exit itself by going to those known places
they also need to prove that somehow the unknown code has been itself checked for well-formedness and absence of unfulfilled proof obligations to justify jumping to it and still keeping clean trackable effects
jumping to unchecked code violates *all* registered trackable effects, since the unchecked code could do literally anything it wants.
