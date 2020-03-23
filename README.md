# A calculus of constructions in Lean

This implements a simple type theory in Lean.
It contains expressions with de-bruijn variables, fresh variable generation,
some parser combinators and a type checker with nice error reporting on failures
and proofs of correctness on success.

If you intend to use this contact me with questions or ask me to add some comments.
Lectures will start again in a few weeks, so I might not have time to work on this
anymore soon. Still, there are some things that could be done here:

 - This presents a solid foundation for exploring the category of types.
   Thanks to the type-checker, it is enough to write terms and get their
   judgements for free.
   The main problem here is that type checking is currently way too slow
   when evaluated using `#reduce`. Maybe this will get better with more
   optimization.

 - This could be the starting point for a small programming language in Lean.
   It should be relatively simple to get a prototype done; but pretty hard to
   actually implement a nice programming language since many "easy" extensions
   (native numbers, special product/row/.. types) require proofs here.

 - This could also be a starting point for writing a Lean type checker in Lean,
   but that would be an undertaking for which I don't have time at the moment.