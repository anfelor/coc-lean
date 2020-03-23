import Terms
import CoC

open PTSSort
open BetaOpt

/-! The type checker. -/

/- 
  Since Judgements are in Prop, we have to jump through some hoops
  to write nearly trivial functions. But Judgements belong to Prop
  not least because the type checker would be noncomputable if they
  were in type due to some hard to prove statements.
-/

inductive TypeError : Type
| TypeMismatch : Exp → Exp → TypeError
| UnboundIndex : nat → TypeError
| UnboundVar : string → TypeError
| BoxInTerm : TypeError
| WhileChecking : Exp → TypeError → TypeError
| ExpectedFunctionButGot : Exp → TypeError
| ExpectedSortButGot : Exp → TypeError
open TypeError

def type_error_repr : TypeError -> string
| (TypeMismatch e1 e2) := "Type mismatch between: " ++ repr e1 ++ " and " ++ repr e2
| (UnboundIndex n) := "Unbound index: " ++ repr n
| (UnboundVar s) := "Unbound var: " ++ repr s
| (BoxInTerm) := "Box in term."
| (WhileChecking e t) := "While checking " ++ repr e ++ " encountered\n" ++ type_error_repr t
| (ExpectedFunctionButGot e) := "Expected function but got: " ++ repr e
| (ExpectedSortButGot e) := "Expected sort but got: " ++ repr e

instance type_error_has_repr : has_repr TypeError :=
  { repr := type_error_repr }

/-- The type checker monad -/
def TC := except TypeError
open except
instance tc_has_bind : has_bind TC := { bind := λ _ _, except.bind }

instance tc_has_repr {a} {h : has_repr a} : has_repr (TC a) :=
  { repr := λ t, match t with
      | error t := repr t
      | ok a := repr a
      end }

instance type_psigma_has_repr {g e} : has_repr (Σ' t : Exp, Judgement g e t) :=
  { repr := λ s, repr s.fst }

/- This instance is necessary for #eval -/
instance type_tc_has_repr {g e} : has_repr (TC (Σ' t : Exp, Judgement g e t)) :=
  { repr := (@tc_has_repr _ type_psigma_has_repr).repr }

/-- Lookup a variable in a well-formed context. -/
def lookup (x : string) : Π (g : Context) (h : ContextWF g), 
  TC (Σ' t, Judgement g (Exp.free x) t)
| (Context.empty) h := error (UnboundVar x)
| (Context.cons y e g') h := 
  match string.has_decidable_eq x y with
  | (is_true p) := ok ⟨e, begin simp [p], cases h, 
      exact Judgement.start y h_noShadowing h_a, end⟩
  | (is_false p) := lookup g' (by { cases h, assumption }) >>= (begin 
        intro a, apply ok, cases a, apply psigma.mk, cases h, 
        exact Judgement.weaken y h_noShadowing a_snd h_a,
      end)
  end

def find_rule : Π (s t : PTSSort), Rule s t
| star star := Rule.vdv
| star box := Rule.tdv
| box star := Rule.vdt
| box box := Rule.tdt

inductive Classification (g : Context) (t : Exp) : Type
| kind : t = Exp.sort box → Classification
| term : Judgement g t (Exp.sort star) → Classification
| constructor : Judgement g t (Exp.sort box) → Classification

-- | See Theorem 3.2 and 3.3 in [snforcc].
-- The classification lemma will be challenging since Classification is in
-- type and not in Prop. See typing_pi_find_sort below.
axiom preservation {g e t} : Judgement g e t → Judgement g (head_reduce e) t
axiom classification : Π {g e t}, Judgement g e t → Classification g t
axiom beta_preserves_type : Π {g e t z}, 
  Beta Red t z → Judgement g e t → Judgement g e z

def beta_reduce_terminates_type {g e t} : Judgement g e t → (beta_reduce t).dom :=
begin
  intro j, cases classification j, simp [a, beta_reduce],
  refine acc.intro t _, intro y, rw [a], intro b, cases b,
  repeat { exact beta_reduce_terminates a },
end

inductive ContextLT : Context -> Context -> Prop
| empty {g} : ContextLT (Context.empty) g
| cons1 {x a g h} : ContextLT g h -> ContextLT g (Context.cons x a h)
| cons2 {x a g h} : ContextLT g h -> ContextLT (Context.cons x a g) (Context.cons x a h)

def context_lt_refl : Π g, ContextLT g g
| Context.empty := ContextLT.empty
| (Context.cons x a g) := ContextLT.cons2 (context_lt_refl g)

def context_lt_cons {x a} : Π g, ContextLT g (Context.cons x a g)
  := λ g, ContextLT.cons1 (context_lt_refl g)

def preserves_type {g e t} 
  : Judgement g e t → Judgement g e (head_reduce t) :=
begin
  intro j, cases classification j, rw [a, head_reduce], rw [a] at j, exact j,
  exact Judgement.conv (Beta.head_reduce Eq t) (preservation a) j,
  exact Judgement.conv (Beta.head_reduce Eq t) (preservation a) j,
end

-- The grammar for expressions of type box is
-- t := A | * | x -> t for A a variable and x an arbitrary expression.
lemma typing_pi_find_sort : Π a (g : Context) (h : ContextWF g), 
  Σ' s, ∀ p, ∀ h_g, ContextLT h_g g -> Judgement h_g a (Exp.sort p) -> p = s
   := sorry

lemma typing_pi : Π {g x a b t}, Judgement g (Exp.pi x a b) t → Σ' s, Judgement g a (Exp.sort s) :=
begin
  intros g x a b t,
  generalize e : Exp.pi x a b = y, intro h,
  let z := typing_pi_find_sort a g (judgement_context_wf h),
  apply psigma.mk z.fst,
  induction h generalizing e; cases e,
  { apply Judgement.weaken,
    exact h_noShadowing, have z2 := h_ih_a (eq.refl _), 
    exact eq.mp (by rw [z.snd _ h_g (context_lt_cons _) z2]) z2, 
    exact h_a_1, }, 
  { exact eq.mp (by rw [z.snd h_s1 h_g (context_lt_refl h_g) h_a]) h_a }, 
  { from h_ih_a_1 (eq.refl _) },
end

lemma beta_reduce_terminates_head_reduce_pi {g e t x a b} : Judgement g e t
  → head_reduce t = Exp.pi x a b → (beta_reduce a).dom := begin
  intros j h, cases classification j, 
    simp [a_1, head_reduce] at h, from false.elim h,
    iterate 2 { have h2 := preservation a_1, rw [h] at h2,
    cases typing_pi h2, from beta_reduce_terminates snd, }
end

inductive typecheck_rel : (Σ' (e : Exp) (g : Context), ContextWF g) 
  → (Σ' (e : Exp) (g : Context), ContextWF g) → Prop
| app_1 {g h a b} : typecheck_rel ⟨a, g, h⟩ ⟨Exp.app a b, g, h⟩
| app_2 {g h a b} : typecheck_rel ⟨b, g, h⟩ ⟨Exp.app a b, g, h⟩
| lam_1 {g h x a b} : typecheck_rel ⟨a, g, h⟩ ⟨Exp.lam x a b, g, h⟩
| lam_2 {g h x a t s hns} {h1 : Judgement g a (Exp.sort s)} : typecheck_rel
  ⟨instantiate (Exp.free (fresh (context_domain g ∪ free_vars t) x)) t
  , Context.cons (fresh (context_domain g ∪ free_vars t) x) a g, ContextWF.cons h hns h1⟩
  ⟨Exp.lam x a t, g, h⟩
| check_pi {g h x a t b} 
  (h1 : Judgement (Context.cons (fresh (context_domain g ∪ free_vars t) x) a g) 
    (instantiate (Exp.free (fresh (context_domain g ∪ free_vars t) x)) t) b) 
  : typecheck_rel
  ⟨Exp.pi (fresh (context_domain g ∪ free_vars t) x) a (abstract (fresh (context_domain g ∪ free_vars t) x) b), g, h⟩ 
  ⟨Exp.lam x a t, g, h⟩
| pi_1 {g h x a b} : typecheck_rel ⟨a, g, h⟩ ⟨Exp.pi x a b, g, h⟩
| pi_2 {g h x a t s hns} {h1 : Judgement g a (Exp.sort s)} : typecheck_rel
  ⟨instantiate (Exp.free (fresh (context_domain g ∪ free_vars t) x)) t
  , Context.cons (fresh (context_domain g ∪ free_vars t) x) a g, ContextWF.cons h hns h1⟩
  ⟨Exp.pi x a t, g, h⟩

set_option eqn_compiler.zeta true
def typecheck_recur : Π (e : Exp) (g : Context) (h : ContextWF g), 
 (Π y, typecheck_rel y ⟨e, g, h⟩ → TC (Σ' t, Judgement y.2.1 y.1 t))
 → TC (Σ' t, Judgement g e t)
| (Exp.free x) g h IH := lookup x g h
| (Exp.bound x) g h IH := error (UnboundIndex x)
| (Exp.sort s) g h IH := match s with
  | star := ok ⟨Exp.sort box, ContextWF.rec_on h (Judgement.starInBox)
    (λ x _ _ _ _ hns a h, Judgement.weaken x hns h a)⟩
  | box := error BoxInTerm
  end
| (Exp.app f a) g h IH :=
  IH ⟨f, g, h⟩ (typecheck_rel.app_1) >>= λ ⟨e, je⟩,
  IH ⟨a, g, h⟩ (typecheck_rel.app_2) >>= λ ⟨A, jA⟩,
    let ⟨z1, beta1⟩ := (beta_reduce A).get (beta_reduce_terminates_type jA)
    in begin
    cases h : (head_reduce e),
    case Exp.pi : x A' B begin
      rename h_1 h,
      let zb := (beta_reduce A').get (beta_reduce_terminates_head_reduce_pi je h),
      cases exp_decidable_eq z1 zb.1,
        exact error (ExpectedFunctionButGot e),
        let h2 : Σ' s, Judgement g (Exp.pi x A' B) (Exp.sort s) := begin
          cases classification (preserves_type je),
          simp [a_1, head_reduce] at h, from false.elim h,
          repeat { rw [h] at a_1 }, exact ⟨star, a_1⟩, exact ⟨box, a_1⟩,
        end,
        let h4 : Σ' s, Judgement g A' (Exp.sort s) := begin
          cases classification (preserves_type je),
          simp [a_1, head_reduce] at h, from false.elim h,
          repeat { rw [h] at a_1, from typing_pi a_1, },
        end,
        apply ok, fapply psigma.mk, exact (instantiate a B), apply Judgement.app,
          apply Judgement.conv, apply eq.mp (by simp [h]) (Beta.head_reduce Eq e),
          from h2.snd, from je, apply Judgement.conv, 
          from (Beta.trans Red Eq Eq (eq.refl _) beta1 (eq.mp (by simp[h_1]) (Beta.symm zb.2))),
          from h4.2, from jA,
      end,
    repeat { exact error (ExpectedFunctionButGot (head_reduce e)) }
    end
| (Exp.lam x a t) g h IH :=
  IH ⟨a, g, h⟩ (typecheck_rel.lam_1) >>= λ⟨s, ja⟩, 
  match (beta_reduce s).get (beta_reduce_terminates_type ja), ja with
  | ⟨Exp.sort s, bs⟩, ja := let x' := fresh (context_domain g ∪ free_vars t) x in
    IH ⟨(instantiate (Exp.free x') t), (Context.cons x' a g),
      (ContextWF.cons h (iff.elim_left finset.not_mem_union (fresh_not_mem)).1 
      (beta_preserves_type bs ja))⟩ (typecheck_rel.lam_2)
    >>= λ⟨b, jb⟩, 
    IH ⟨(Exp.pi x' a (abstract x' b)), g, h⟩ (typecheck_rel.check_pi jb) >>= 
      λ⟨p, jp⟩, match (beta_reduce p).get (beta_reduce_terminates_type jp), jp with
        | ⟨Exp.sort _, bp⟩, jp := 
          let h : Judgement g (Exp.lam x a t) (Exp.pi x a (abstract x' b))
            := eq.mp (by simp [fresh_avoids_capture (finset.subset_union_right _ _)]) 
              (Judgement.abs x jb (beta_preserves_type bp jp))
          in ok ⟨Exp.pi x a (abstract x' b), h⟩
        | _, _ := error (ExpectedSortButGot p)
        end
  | ⟨e, _⟩, _ := error (ExpectedSortButGot e)
  end
| (Exp.pi x a b) g h IH :=
  IH ⟨a, g, h⟩ (typecheck_rel.pi_1) >>= λ⟨s, js⟩, 
  match (beta_reduce s).get (beta_reduce_terminates_type js), js with
  | ⟨Exp.sort s, bs⟩, js := let x' := fresh (context_domain g ∪ free_vars b) x in
    IH ⟨(instantiate (Exp.free x') b), (Context.cons x' a g), 
      (ContextWF.cons h (iff.elim_left finset.not_mem_union (fresh_not_mem)).1 
      (beta_preserves_type bs js))⟩ (typecheck_rel.pi_2)
    >>= λ⟨t, jt⟩, match (beta_reduce t).get (beta_reduce_terminates_type jt), jt with
    | ⟨Exp.sort t, bt⟩, jt := 
      let h : Judgement g (Exp.pi x a b) (Exp.sort t) 
        := eq.mp (by simp [fresh_avoids_capture (finset.subset_union_right _ _)])
          (Judgement.product x (find_rule s t) (beta_preserves_type bs js) 
          (beta_preserves_type bt jt))
      in ok ⟨Exp.sort t, h⟩
    | ⟨e, _⟩, _ := error (ExpectedSortButGot e)
    end
  | ⟨e, _⟩, _ := error (ExpectedSortButGot e)
  end
set_option eqn_compiler.zeta false

def typecheck_roption (e : Exp) (g : Context) (h : ContextWF g) : roption (TC (Σ' t, Judgement g e t)) :=
begin
  refine ⟨acc typecheck_rel ⟨e,g,h⟩, λ h2, @acc.rec_on (Σ' (e : Exp) (g : Context), ContextWF g) _ 
  (λ y, TC (Σ' t, Judgement y.2.1 y.1 t)) _ h2 (λ ⟨e1,g1,h1⟩ ih IH, 
  typecheck_recur e1 g1 h1 IH)⟩,
end

def typecheck_terminates (e : Exp) (g : Context) (h : ContextWF g) : (typecheck_roption e g h).dom
  := sorry

def typecheck (e : Exp) (g : Context) (h : ContextWF g) : TC (Σ' t, Judgement g e t) :=
  (typecheck_roption e g h).get (typecheck_terminates e g h)