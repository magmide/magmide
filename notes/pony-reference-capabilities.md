http://jtfmumm.com/blog/2016/03/06/safely-sharing-data-pony-reference-capabilities/


`iso`: writeable/readable, only one reference exists (this one). can be used to read or write locally. can be converted to anything, including giving it up to pass to another actor
`val`: readable, only immutable aliases exist, so can be shared for reading with anyone.
`tag`: neither, the address of an actor, can be shared anywhere, but can't be read or written.
`ref`: writeable/readable but only locally, an unknown number of mutable local aliases exist, so this is just like a typical alias. since we don't know how many aliases exist, we can only possibly share this thing if we somehow destroy those other aliases.
`trn`: a local reference we can write/read, but can only create readable references from. this allows us to eventually convert this type to a `val`.
`box`: readable locally, we don't know how many other people are looking at this thing

the subtyping (or "can be substituted for") relation

```
               --> ref --
              /          \
iso --> trn --            --> box --> tag
              \          /
               --> val --
```


1) A mutable reference capability denies neither read nor write permissions. This category includes `iso`, `ref`, and `trn`.

2) An immutable reference capability denies write permissions but not read permissions. This category includes `val` and `box`.

3) An opaque reference capability denies both read and write permissions. The only example is `tag`.



https://tutorial.ponylang.io/reference-capabilities/reference-capabilities.html#isolated-data-may-be-complex

```
Isolated data may be complex
An isolated piece of data may be a single byte. But it can also be a large data structure with multiple references between the various objects in that structure. What matters for the data to be isolated is that there is only a single reference to that structure as a whole. We talk about the isolation boundary of a data structure. For the structure to be isolated:

There must only be a single reference outside the boundary that points to an object inside.
There can be any number of references inside the boundary, but none of them must point to an object outside.



Isolated, written iso. This is for references to isolated data structures. If you have an iso variable then you know that there are no other variables that can access that data. So you can change it however you like and give it to another actor.

Value, written val. This is for references to immutable data structures. If you have a val variable then you know that no-one can change the data. So you can read it and share it with other actors.

Reference, written ref. This is for references to mutable data structures that are not isolated, in other words, “normal” data. If you have a ref variable then you can read and write the data however you like and you can have multiple variables that can access the same data. But you can’t share it with other actors.

Box. This is for references to data that is read-only to you. That data might be immutable and shared with other actors or there may be other variables using it in your actor that can change the data. Either way, the box variable can be used to safely read the data. This may sound a little pointless, but it allows you to write code that can work for both val and ref variables, as long as it doesn’t write to the object.

Transition, written trn. This is used for data structures that you want to write to, while also holding read-only (box) variables for them. You can also convert the trn variable to a val variable later if you wish, which stops anyone from changing the data and allows it be shared with other actors.

Tag. This is for references used only for identification. You cannot read or write data using a tag variable. But you can store and compare tags to check object identity and share tag variables with other actors.

Note that if you have a variable referring to an actor then you can send messages to that actor regardless of what reference capability that variable has.
```



so reference capabilities have these qualities:
readable/writeable *to you*
readable/writeable *to others*
writeable *locally*
shareable *locally*
shareable *globally*


https://tutorial.ponylang.io/reference-capabilities/guarantees.html


`iso`: others/local read/write unique
`trn`: others/local write unique, others read unique
`ref`: others read/write unique

`val`: others/local immutable
`box`: others immutable

`tag`: opaque

|                       | Deny global read/write   | Deny global write | None denied      |
|-----------------------|--------------------------|-------------------|------------------|
| Deny local read/write | `iso` (sendable)         |                   |                  |
| Deny local write      | `trn`                    | `val` (sendable)  |                  |
| None denied           | `ref`                    | `box`             | `tag` (sendable) |
|                       | (Mutable)                | (Immutable)       | (Opaque)         |

Sendable capabilities. If we want to send references to a different actor, we must make sure that the global and local aliases make the same guarantees. It’d be unsafe to send a trn to another actor, since we could possibly hold box references locally. Only iso, val, and tag have the same global and local restrictions – all of which are in the main diagonal of the matrix.
