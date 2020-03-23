import category_theory.category
import tactic.norm_num
import data.finset
import data.pfun

import Terms
import FreshNames

/-! This file implements beta-reduction and the judgements of a 
    calculus of constructions. -/

open PTSSort

--| The terms we introduced are general enough to be able to represent the 
-- untyped lambda calculus, therefore we can't give a provably terminating
-- beta reduction without using the judgements below. 
-- But even then the proof is too involved to be placed here.
-- We therefore proceed in two steps:
-- First we form the equivalence class of terms that
-- can be beta-reduced into each other (suggested by Mario Carneiro).
-- This is the reflexive symmetric transitive closure of head_reduce anywhere in a term.
-- Second we define a non-provably-terminating beta-reduction that gives
-- us a proof object of where the beta-reduction has to take place.
inductive BetaOpt | Red | Eq
open BetaOpt

@[reducible]
def beta_merge : BetaOpt → BetaOpt → BetaOpt
| Red Red := Red
| Red Eq := Eq
| Eq Red := Eq
| Eq Eq := Eq

inductive Beta : BetaOpt → Exp → Exp → Type
| refl : Π (r A), Beta r A A
| symm : Π {A B r}, Beta r A B → Beta Eq B A
| trans : Π {A B C} (r s t) (h : t = beta_merge r s), 
    Beta r A B → Beta s B C → Beta t A C
| head_reduce : Π (r A), Beta r A (head_reduce A)
| app : Π {A B C D} (r s t) (h : t = beta_merge r s), 
    Beta r A B → Beta s C D → 
    Beta t (Exp.app A C) (Exp.app B D)
| lam : Π (x : string) {A B C D} (r s t) (h : t = beta_merge r s),
    Beta r A B → Beta s C D → 
    Beta t (Exp.lam x A C) (Exp.lam x B D)
| pi : Π (x : string) {A B C D} (r s t) (h : t = beta_merge r s),
    Beta r A B → Beta s C D → 
    Beta t (Exp.pi x A C) (Exp.pi x B D)

inductive beta_reduce_rel : Exp → Exp → Prop
| app_lam {a b x c d} :
  head_reduce a = Exp.lam x c d →
  beta_reduce_rel (head_reduce (Exp.app a b)) (Exp.app a b)
| app_not_lam_1 {a b} :
  ¬ (∃ x c d, head_reduce a = Exp.lam x c d) → beta_reduce_rel a (Exp.app a b)
| app_not_lam_2 {a b} :
  ¬ (∃ x c d, head_reduce a = Exp.lam x c d) → beta_reduce_rel b (Exp.app a b)
| lam_1 {x a b} : beta_reduce_rel a (Exp.lam x a b)
| lam_2 {x a b} : beta_reduce_rel b (Exp.lam x a b)
| pi_1 {x a b} : beta_reduce_rel a (Exp.pi x a b)
| pi_2 {x a b} : beta_reduce_rel b (Exp.pi x a b)

-- | Beta-reduction to a value/irreducible term.
def beta_reduce (e : Exp) : roption (Σ z, Beta Red e z) :=
begin
  refine ⟨acc beta_reduce_rel e, λ h, acc.rec_on h (λ e _ IH, _)⟩,
  cases e,
  iterate 3 {exact ⟨_, Beta.refl Red _⟩},
  case Exp.app : a b {
    cases hw : head_reduce a,
    case Exp.lam : _ c d {
      obtain ⟨z3, beta3⟩ := IH _ (beta_reduce_rel.app_lam hw),
      exact ⟨z3, Beta.trans Red Red Red (eq.refl _) (Beta.head_reduce Red _) beta3⟩ },
    all_goals {
      have : ¬ (∃ x c d, head_reduce a = Exp.lam x c d),
      { rintro ⟨x,c,d,hn⟩, cases hw.symm.trans hn },
      obtain ⟨z1, beta1⟩ := IH _ (beta_reduce_rel.app_not_lam_1 this),
      obtain ⟨z2, beta2⟩ := IH _ (beta_reduce_rel.app_not_lam_2 this),
      exact ⟨Exp.app z1 z2, Beta.app Red Red Red (eq.refl _) beta1 beta2⟩ } },
  case Exp.lam : x a b {
    obtain ⟨z1, beta1⟩ := IH _ beta_reduce_rel.lam_1,
    obtain ⟨z2, beta2⟩ := IH _ beta_reduce_rel.lam_2,
    exact ⟨Exp.lam x z1 z2, Beta.lam x Red Red Red (eq.refl _) beta1 beta2⟩ },
  case Exp.pi : x a b {
    obtain ⟨z1, beta1⟩ := IH _ beta_reduce_rel.pi_1,
    obtain ⟨z2, beta2⟩ := IH _ beta_reduce_rel.pi_2,
    exact ⟨Exp.pi x z1 z2, Beta.pi x Red Red Red (eq.refl _) beta1 beta2⟩ },
end

inductive Context : Type
| empty : Context
| cons : Π (x : string) (A : Exp) (g : Context), Context

def context_domain : Context → finset string
| Context.empty := ∅
| (Context.cons x _ g) := insert x (context_domain g)

inductive Rule : PTSSort → PTSSort → Type
| vdv : Rule star star
| tdt : Rule box box
| vdt : Rule box star
| tdv : Rule star box

-- | Valid judgements in the CoC. 
-- A judgement carries a context, a value and its type.
-- Unlike in the standard presentation we allow to set the variable
-- x' here. That is okay, since the standard presentation only 
-- considers terms up to alpha-equivalence. It is necessary,
-- since we can model shadowed variables this way.
inductive Judgement : Context → Exp → Exp → Prop
| starInBox : Judgement (Context.empty) (Exp.sort star) (Exp.sort box)
| start {g A s} (x : string) (noShadowing : x ∉ context_domain g) : Judgement g A (Exp.sort s) 
  → Judgement (Context.cons x A g) (Exp.free x) A
| weaken {g M B A s} (x : string) (noShadowing : x ∉ context_domain g)
  : Judgement g M A → Judgement g B (Exp.sort s)
  → Judgement (Context.cons x B g) M A
| product {g A B x s1 s2} (x' : string) (r : Rule s1 s2)
  : Judgement g A (Exp.sort s1)
  → Judgement (Context.cons x A g) B (Exp.sort s2)
  → Judgement g (Exp.pi x' A (abstract x B)) (Exp.sort s2)
| app {M N A B g x}
  : Judgement g M (Exp.pi x A B) → Judgement g N A
  → Judgement g (Exp.app M N) (instantiate N B)
| abs {g A B M x s} (x' : string)
  : Judgement (Context.cons x A g) M B 
  → Judgement g (Exp.pi x A (abstract x B)) (Exp.sort s)
  → Judgement g (Exp.lam x' A (abstract x M)) (Exp.pi x' A (abstract x B))
| conv {g A B M s}
  : (Beta Eq A B) → Judgement g B (Exp.sort s) → Judgement g M A
  → Judgement g M B

inductive ContextWF : Context → Prop
| empty : ContextWF Context.empty
| cons : Π {x A g s} (h : ContextWF g) (noShadowing : x ∉ context_domain g), 
  Judgement g A (Exp.sort s) → ContextWF (Context.cons x A g)

def judgement_context_wf {g A B} : Judgement g A B → ContextWF g :=
begin
  intro, induction a,
    exact ContextWF.empty,
    exact ContextWF.cons a_ih a_noShadowing a_a,
    exact ContextWF.cons a_ih_a a_noShadowing a_a_1,
    repeat {exact a_ih_a, },
    exact a_ih_a_1,
end

-- See for example "Strong Normalization for the Calculus of Constructions"
-- by Chris Casinghino, 2010 ([snforcc])
axiom beta_reduce_terminates {g e t} : Judgement g e t → (beta_reduce e).dom 