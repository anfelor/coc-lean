import data.finset

/-! This file implements terms of a pure type system -/

@[derive decidable_eq]
inductive PTSSort : Type | star | box
open PTSSort

instance ptssort_has_repr : has_repr PTSSort :=
  { repr := λ s, match s with star := "*" | box := "□" end }

inductive Exp : Type
| free : string → Exp
| bound : nat → Exp
| sort : PTSSort → Exp
| app : Exp → Exp → Exp
| lam : string → Exp → Exp → Exp
| pi : string → Exp → Exp → Exp

/-- A pretty printing of formulae. It doesn't try to interpolate
  de-bruijn variables, which means that (Π x, 0) is the identity
  function and (Π x, x) is the constant function for the free variable x. -/
def exp_repr : Exp → string
| (Exp.free x) := x
| (Exp.bound n) := repr n
| (Exp.sort s) := repr s
| (Exp.app a b) := exp_repr a ++ " (" ++ exp_repr b ++ ")"
| (Exp.lam x a b) := "λ(" ++ x ++ " : " ++ exp_repr a ++ ") → " ++ exp_repr b
| (Exp.pi x a b) := "Π(" ++ x ++ " : " ++ exp_repr a ++ ") → " ++ exp_repr b

instance exp_has_repr : has_repr Exp :=
  { repr := exp_repr }

 -- apply_instance fails below, so we restate the lemma here.
def decidable_and {p q : Prop} [decidable p] [decidable q] : decidable (p ∧ q) :=
  infer_instance

instance exp_decidable_eq : decidable_eq Exp :=
λ a b, begin
  induction a generalizing b,
    cases b, repeat { simp, from decidable.false },
      simp, from string.has_decidable_eq a b, 
    cases b, repeat { simp, from decidable.false },
      simp, from nat.decidable_eq a b,
    cases b, repeat { simp, from decidable.false },
      simp, let d : decidable_eq PTSSort := infer_instance,
      from d a b,
    cases b, repeat { simp, from decidable.false },
      simp, letI h1 := a_ih_a b_a, letI h2 := a_ih_a_1 b_a_1,
      from @decidable_and _ _ h1 h2,
    repeat { cases b, repeat { simp, from decidable.false },
      simp, letI h1 := a_ih_a b_a_1, letI h2 := a_ih_a_1 b_a_2,
      letI h3 := string.has_decidable_eq a_a b_a,
      apply_instance, }
end

@[simp] def abstract_help (x : string) : Exp → nat → Exp
| e@(Exp.free y) n := if x = y then Exp.bound n else e
| e@(Exp.bound _) n := e
| e@(Exp.sort _) n := e
| (Exp.app f e) n := Exp.app (abstract_help f n) (abstract_help e n)
| (Exp.lam y t e) n := Exp.lam y (abstract_help t n) (abstract_help e (n+1))
| (Exp.pi y t e) n := Exp.pi y (abstract_help t n) (abstract_help e (n+1))

/-- Turn the free variable x into a fresh de-bruijn index.
    Given an expression e, we can turn it into a function with:
    Exp.lam x _ (abstract x e) -/
def abstract (x : string) (e : Exp) : Exp :=
  abstract_help x e 0

@[simp] def instantiate_help (x : Exp) : Exp → nat → Exp
| e@(Exp.free _) n := e
| e@(Exp.bound b) n := if b = n then x else e
| e@(Exp.sort _) n := e
| (Exp.app f e) n := Exp.app (instantiate_help f n) (instantiate_help e n)
| (Exp.lam y t e) n := Exp.lam y (instantiate_help t n) (instantiate_help e (n + 1))
| (Exp.pi y t e) n := Exp.pi y (instantiate_help t n) (instantiate_help e (n + 1))

/-- Instantiate the top-most de-bruijn index with x.
    Given a expression (Exp.lam x _ e), we can use A for x
    by instantiate A e. -/
def instantiate (x : Exp) (e : Exp) : Exp :=
  instantiate_help x e 0

/-- Substitute the free variable x by r in e. -/
def substitute (x : string) (r : Exp) (e : Exp) : Exp :=
  instantiate r (abstract x e)

/-- The free variables in an expression -/
def free_vars : Π (e : Exp), finset string
| (Exp.free x) := finset.singleton x
| (Exp.app a b) := free_vars a ∪ free_vars b
| (Exp.lam _ a b) := free_vars a ∪ free_vars b
| (Exp.pi _ a b) := free_vars a ∪ free_vars b
| (Exp.bound _) := ∅
| (Exp.sort _) := ∅

/-- The bound variables -/
def bound_vars : Π (e : Exp), finset string
| (Exp.app a b) := free_vars a ∪ free_vars b
| (Exp.lam x a b) := insert x (free_vars a ∪ free_vars b)
| (Exp.pi x a b) := insert x (free_vars a ∪ free_vars b)
| _ := ∅ 
