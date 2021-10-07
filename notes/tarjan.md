so as we're going through the depth first search, we store: a stack of visited but not yet assigned vertices, pushed onto the stack in the order they are visited; a set of finalized components; the current serial number; and a "function" (map?) of vertices to serial numbers.

two mutually recursive functions, they call then `dfs1` and `dsf`, but those are awful names, I'll renamed once I fully understand them

- `dfs` takes a set of roots and an initial environment, returns a pair of an integer and the modified environment. if the roots is empty the integer is `infinity` (what they should have done is just used `option` or something here). Otherwise the returned integer is the minimum of the results of the calls to `dfs1` on non-visited vertices in r and of the serial numbers of the already visited ones.
- `dfs1`

the main function creates the initial environment with an empty stack, empty set of components, serial number 0, and an empty map assigning numbers to vertices


```
let rec dfs1 vertex e =
  let n0 = e.cur in
  let (n1, e1) = dfs (successors vertex) (add_stack_incr vertex e) in
  if n1 < n0
    then (n1, e1)
    else
      let (s2, s3) = split x e1.stack in
      (+∞, {stack = s3; sccs = add (elements s2) e1.sccs; cur = e1.cur; num = set_infty s2 e1.num})

with dfs r e =
  if is_empty r
    then (+∞, e)
    else
      let x = choose r in
      let r’ = remove x r in
      let (n1, e1) = if e.num[x] != -1
        then (e.num[x], e)
        else dfs1 x e in
      let (n2, e2) = dfs r’ e1 in (min n1 n2, e2)

let tarjan () =
  let e = {stack = []; sccs = empty; cur = 0; num = const (-1)} in
  let (_, e’) = dfs vertices e in e’.sccs

let add_stack_incr x e =
  let n = e.cur in
  {stack = x :: e.stack; sccs = e.sccs; cur = n+1; num = e.num[x ← n]}

let rec set_infty s f = match s with
  | [] → f
  | x :: s’ → (set_infty s’ f)[x ← +∞] end

let rec split x s = match s with
  | [] → ([], [])
  | y :: s’ → if x = y
    then ([x], s’)
    else
      let (s1’, s2) = split x s’ in
      (y :: s1’, s2) end
```

looks like I need to check out their better version
https://www-sop.inria.fr/marelle/Tarjan/
https://math-comp.github.io/mcb/

Łukasz Czajka and Cezary Kaliszyk. Hammer for coq: Automation for dependent
type theory. J. Autom. Reasoning, 61(1-4):423–453, 2018.
