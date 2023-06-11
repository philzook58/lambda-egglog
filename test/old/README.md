

- sqlite
- Term ordering should be in order of definitions.

- destructive rules / symbols. non memoized? Is this ok?
- auto2


Zipperposition notes:
resolution example

src
saturate is main loop
refers to Env

`define` as a force on lexiographic ordering?

So an egraph holds an infintie class


tasks:
- js_of_ocaml
- string function


Rust
- look at that dedukti kernel



How to insert a term without rewriting anything.
Operatonally useful. It's often how ematching starts
Use defined skolem symbol perhaps.
exists x. x = foo a

Use forall x y, form of rules.
It's better anyway in some respects.

Use signature

https://github.com/matryoshka-project/matryoshka-project.github.io/blob/master/matryoshka2019/slides/bentkamp-superposition-with-lambdas.pdf
\x. x > \x. b ??
It's the same question as X < b because we can substitute.
re lambda terms ground terms?
Do I actually want beta as definitional, probably not.
I just want alpha, maybe eta
\x y. x > \x y. y ? 
I do want to perform moves that decrase the distance between the binder and it's var.
\x. x > \x. b   Almost cntradictorly, I want to first orderize. Constant can be considered to be outermost lambda bound. I can't have b ---> x. That could make x escape a scope it makes sense. I can't even really have b --> x at all.
C[b] --> C[x] is ok if C allows x.
C[x] --> C[b] is always ok (requiriting less scope), never going to make sense? x is this unknown thing is shouldn't be equal to a global constant. That is just bizarre. This breaks alpha in some sense?
0 * x -->  0 has to go this way.
0 --> 0 * x may work in some scopes


How many N scope is a separate egraph?
0-scope = normal egraph
1-scope
But why do we even need to track the scope? What difference does it make? It keeps congruence separated? Blocks something?
\x. 0 * x -> \x. 0
0 * x is a 1-scope term and 0 is a 0-scope term. (scope is the max of the arguments. lam decreases scope by 1.)
bvar(n) has scope n.
0 * x -> 0_1 not 0_0
\x. 0_1 = \x. 0_0 somehow.
is 0_0 = 0_1 ? for some purpoes maybe, for others not.
Vec<Vec<int>> scope and then id union find.


THe closed term restriction. Maybe that's ok because we can smuggle stuff down
a(x,y) skolemization vs eta expansion.
\x. e1 + e2 == \x  (\y e1) x) + (\y e2) x)

We don't _really_ need names though, db indices is good. and skolem weakening might be what is the highest scope we need. Actually, I guess that's an approximation. skolem weakening lists which binders we touch. But I don't even know that the difference hurts us.

Open de bruijn, but if we don't cover beta, locally nameless is less important?

Even then, rules that manipulate scope need to traverse down the thing. Maintain a shift table? Which is equivalent to having a shift function. hmm.

scope is like a tag on everything. scope_tag(x, 1)
or is it subtly different.


Ok.
Sexp -> untyped
Zf -> 

ematching for real.

Is this actually getting me anything? Well it got me startd.


```ocaml
type term = 
| Const of string
| App of term * term (* Apply term * term  ?? *)

let rec size = function
| Const _ -> 1
| Apply (a,args) -> List.fold size (size a) args

let ground_kbo t1 t2 =
    let s1 = size t1 in
    let s2 = size t2 in
    if Int.equal s1 s2 then
        match t1, t2
        | Const x1, Const x2 -> String.compare x1 x2
        | Const x1, App (f,args) -> LT
        | App (f,args), Const x1 -> GT
        | App (f1,args1), App (f2,args2) -> lex (ground_kbo f1 f2) (fun () -> ground_kbo args1 args2)
    else Int.compare s2 s2
(* 
type memo_term =
 | Const of string
 | Apply of {size : int; head : memo_term, memo_term term array}
and data = 
  {size : int; id : int; hash : int; feature : int array ; sym : memo_term }
*)
```


- ematching
- kbo as analysis.



Skolemization for relational ematching / eid separation
put into normal form where skolems are smaller than all real terms

f(x,y,z) -> sk
sk1 -> sk2


superpoition modulo linear arithemtic 
modulo theory https://d-nb.info/1053679971/34 thesis
shostak congruence closure

