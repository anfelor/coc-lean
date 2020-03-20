# A calculus of constructions in Lean

This implements a simple type theory in Lean.
It contains expression with de-bruijn variables, fresh variable generation
and a (at the moment noncomputable) type checker.

If you intend to use this contact me with questions or ask me to add some comments.

## Roadmap

 - Judgement should be in Prop to make the type checker computable in the presence
   of axioms about judgements but it is unclear how this works with type error reporting.
 - I really want to have some category instances for Judgement. Some definitions for this
   have been provided but this ultimately depends on a computable type checker.
 - I want to try and turn this into a small Haskell-like programming language with
   a parser for simple function definitions and data types.
 - Maybe everything will be easier once Lean 4 lands?
