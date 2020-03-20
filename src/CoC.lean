import init.category.except
import category_theory.category
import tactic.norm_num
import data.finset
import init.logic
import init.data.nat.lemmas
import logic.embedding
import data.pfun

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
      simp, let d : decidable_eq PTSSort := by apply_instance,
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

def abstract (x : string) (e : Exp) : Exp :=
  abstract_help x e 0

@[simp] def instantiate_help (x : Exp) : Exp → nat → Exp
| e@(Exp.free _) n := e
| e@(Exp.bound b) n := if b = n then x else e
| e@(Exp.sort _) n := e
| (Exp.app f e) n := Exp.app (instantiate_help f n) (instantiate_help e n)
| (Exp.lam y t e) n := Exp.lam y (instantiate_help t n) (instantiate_help e (n + 1))
| (Exp.pi y t e) n := Exp.pi y (instantiate_help t n) (instantiate_help e (n + 1))

def instantiate (x : Exp) (e : Exp) : Exp :=
  instantiate_help x e 0

def substitute (x : string) (r : Exp) (e : Exp) : Exp :=
  instantiate r (abstract x e)

def free_vars : Π (e : Exp), finset string
| (Exp.free x) := finset.singleton x
| (Exp.app a b) := free_vars a ∪ free_vars b
| (Exp.lam _ a b) := free_vars a ∪ free_vars b
| (Exp.pi _ a b) := free_vars a ∪ free_vars b
| (Exp.bound _) := ∅
| (Exp.sort _) := ∅

def bound_vars : Π (e : Exp), finset string
| (Exp.app a b) := free_vars a ∪ free_vars b
| (Exp.lam x a b) := insert x (free_vars a ∪ free_vars b)
| (Exp.pi x a b) := insert x (free_vars a ∪ free_vars b)
| _ := ∅ 

-- TODO: this throws the famous 'no goals' error
def pigeonhole
  : Π (ys : finset string) (xs : finset string), 
  (finset.card ys < finset.card xs) → finset.nonempty (xs \ ys)
| ys := λ xs h, if h2 : finset.card ys = 0 then begin 
    have h3 : xs = xs \ ys, rw [finset.ext], intro,
    rw [finset.mem_sdiff], apply iff.intro, intro,
    split, assumption, rw [finset.card_eq_zero] at h2, simp [h2],
    intro, cases a_1, assumption, rw [h2, finset.card_pos] at h,
    rw [h3] at h, assumption,
  end else begin
    have h6 : finset.card ys ≠ 0, assumption,
    rw [finset.card_eq_zero, eq.symm (ne.def _ _)] at h2,
    rw [finset.nonempty_iff_ne_empty.symm] at h2, cases h2.bex, 
    have h' : finset.card (finset.erase ys w) < finset.card (finset.erase xs w),
    cases finset.decidable_mem w xs, rw [finset.erase_eq_of_not_mem h_2],
    have h7 : finset.card ys > 0, exact nat.pos_of_ne_zero h6,
    rw [finset.card_erase_of_mem h_1], rw [(nat.succ_pred_eq_of_pos h7).symm] at h,
    exact nat.lt_of_succ_lt h,
    rw [finset.card_erase_of_mem h_1, finset.card_erase_of_mem h_2],
    exact nat.pred_lt_pred h6 h,
    have h8 : finset.erase ys w ⊂ ys, exact finset.erase_ssubset h_1,
    let ne := pigeonhole (finset.erase ys w) (finset.erase xs w) h',
    cases ne.bex, have h4 : w_1 ∈ xs \ ys, rw [finset.mem_sdiff] at h_2, cases h_2,
    simp [finset.mem_of_mem_erase] at h_2_left, cases h_2_left with neq inxs,
    let h5 : w_1 ∉ ys := mt (finset.mem_erase_of_ne_of_mem neq) h_2_right,
    simp, exact ⟨inxs, h5⟩, exact ⟨w_1, h4⟩,
  end
using_well_founded 
  {rel_tac := λ e es, `[exact ⟨_,(@finset.lt_wf string)⟩] >> wf_tacs.rel_tac e es,
  dec_tac := `[assumption] }

def mk_name (x : string) : nat → string
| 0 := x
| (n+1) := (mk_name n) ++ "'"

def string.length_append (x y : string) :
  (x ++ y).length = x.length + y.length :=
begin
  cases x, cases y, simp [(++), string.append, string.length],
  from list.length_append x y,
end

def mk_name_len (x : string) (n : nat)
  : (mk_name x n).length = x.length + n :=
begin
  induction n, simp [mk_name], simp [mk_name, string.length_append, n_ih],
  have h : string.length "'" = 1 := by refl, rw [h, nat.succ_eq_add_one],
  norm_num,
end

def mk_name_inj (x : string) : function.injective (mk_name x) := 
begin
  intros a1 a2 h, have h2 : (mk_name x a1).length = (mk_name x a2).length,
  from eq.rec_on h (eq.refl (mk_name x a1).length),
  simp [mk_name_len] at h2, from h2,
end

-- | Find a fresh name that is close to x
def fresh (xs : finset string) (x : string) : string :=
  let fresh_names := finset.image (mk_name x) (finset.range (nat.succ (finset.card xs))) in
  finset.min' (fresh_names \ xs) (pigeonhole xs fresh_names begin
    rw [finset.card_image_of_injective, finset.card_range],
    exact nat.lt_succ_self (finset.card xs), exact (mk_name_inj x), end)

lemma fresh_is_fresh {xs x b} (h : b ∈ xs) : fresh xs x ≠ b :=
begin
  simp [fresh], intro,
  have h1 : b ∉ xs, from and.elim_right (iff.elim_left finset.mem_sdiff 
    (eq.mp (by rw [a]) (finset.min'_mem _ _))),
  from absurd h h1,
end

lemma fresh_not_mem {xs x} : fresh xs x ∉ xs :=
  λ e, absurd (eq.refl _) (fresh_is_fresh e)

lemma fresh_avoids_capture_help {x b xs} (h : free_vars b ⊆ xs) (n : nat)
  : abstract_help (fresh xs x) (instantiate_help (Exp.free (fresh xs x)) b n) n = b :=
begin
  induction b generalizing n, 
    simp, cases eq.decidable (fresh xs x) b,
      simp [h_1], simp [free_vars] at h,
      have h_3 := finset.mem_of_subset h (finset.mem_singleton_self b),
      from absurd h_1 (fresh_is_fresh h_3),
    cases eq.decidable b n, iterate 2 { simp [h_1] },
    simp,

    simp [free_vars] at h,
    let h_a := finset.subset.trans (finset.subset_union_left _ _) h,
    let h_a_1 := finset.subset.trans (finset.subset_union_right _ _) h,
    simp [b_ih_a h_a, b_ih_a_1 h_a_1],

  iterate 2 {
    simp [free_vars] at h,
    let h_a_1 := finset.subset.trans (finset.subset_union_left _ _) h,
    let h_a_2 := finset.subset.trans (finset.subset_union_right _ _) h,
    simp [b_ih_a h_a_1, b_ih_a_1 h_a_2], },
end

lemma fresh_avoids_capture {x b xs} (h : free_vars b ⊆ xs) 
  : abstract (fresh xs x) (instantiate (Exp.free (fresh xs x)) b) = b :=
  fresh_avoids_capture_help h 0

-- | Top-level one-step beta reduction.
def head_reduce : Exp → Exp
| (Exp.app a b) := match a with
    Exp.lam _ _ d := instantiate b d,
    _ := Exp.app a b
  end
| e := e

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
inductive Judgement : Context → Exp → Exp → Type
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

inductive ContextWF : Context → Type
| empty : ContextWF Context.empty
| cons : Π {x A g s} (h : ContextWF g) (noShadowing : x ∉ context_domain g), Judgement g A (Exp.sort s)
  → ContextWF (Context.cons x A g)

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
def beta_reduce_terminates {g e t} : Judgement g e t → (beta_reduce e).dom 
  := sorry

inductive TypeError : Type
| TypeMismatch : Exp → Exp → TypeError
| UnboundIndex : nat → TypeError
| UnboundVar : string → TypeError
| BoxInTerm : TypeError
| WhileChecking : Exp → TypeError → TypeError
| ExpectedFunctionButGot : Exp → TypeError
| ExpectedSortButGot : Exp → TypeError
open TypeError

def TC := except TypeError
open except
instance tc_has_bind : has_bind TC := { bind := λ _ _, except.bind }

-- | Lookup a variable in a well-formed context.
def lookup (x : string) : Π (g : Context) (h : ContextWF g), TC (Σ t, Judgement g (Exp.free x) t)
| (Context.empty) h := error (UnboundVar x)
| (Context.cons y e g') (ContextWF.cons h_h h_noShadowing h_a) := match string.has_decidable_eq x y with
  | (is_true p) := ok ⟨e, (eq.mp (by simp [p]) (Judgement.start y h_noShadowing h_a))⟩
  | (is_false p) := lookup g' h_h >>= λ ⟨a_fst, a_snd⟩, 
      ok ⟨a_fst, Judgement.weaken y h_noShadowing a_snd h_a⟩
  end

def find_rule : Π (s t : PTSSort), Rule s t
| star star := Rule.vdv
| star box := Rule.tdv
| box star := Rule.vdt
| box box := Rule.tdt

inductive Classification (g : Context) (t : Exp)
| kind : t = Exp.sort box → Classification
| term : Judgement g t (Exp.sort star) → Classification
| constructor : Judgement g t (Exp.sort box) → Classification

-- | See Theorem 3.2 and 3.3 in [snforcc].
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

noncomputable def preserves_type {g e t} 
  : Judgement g e t → Judgement g e (head_reduce t) :=
begin
  intro j, cases classification j, rw [a, head_reduce], rw [a] at j, exact j,
  exact Judgement.conv (Beta.head_reduce Eq t) (preservation a) j,
  exact Judgement.conv (Beta.head_reduce Eq t) (preservation a) j,
end

lemma typing_pi : Π {g x a b t}, Judgement g (Exp.pi x a b) t → Σ s, Judgement g a (Exp.sort s)
| g x a b t (@Judgement.product _ _ _ _ s _ _ r ta _) := ⟨s, ta⟩
| g x a b t (@Judgement.conv _ _ _ _ _ _ _ tr) := typing_pi tr
| (Context.cons _ _ _) x a b t (@Judgement.weaken _ _ _ _ s _ h j js) := 
  let ⟨res, j2⟩ := typing_pi j in ⟨res, @Judgement.weaken _ _ _ _ s _ h j2 js⟩
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ j, begin 
rcases j with ⟨g, x, a, b, t, j⟩, exact Judgement.sizeof g (Exp.pi x a b) t j, end)⟩ ] }

lemma beta_reduce_terminates_head_reduce_pi {g e t x a b} : Judgement g e t
  → head_reduce t = Exp.pi x a b → (beta_reduce a).dom := begin
  intros j h, cases classification j, 
    simp [a_1, head_reduce] at h, from false.elim h,
    iterate 2 { have h2 := preservation a_1, rw [h] at h2,
    from beta_reduce_terminates (typing_pi h2).2, }
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
noncomputable
def typecheck_recur : Π (e : Exp) (g : Context) (h : ContextWF g), 
 (Π y, typecheck_rel y ⟨e, g, h⟩ → TC (Σ t, Judgement y.2.1 y.1 t))
 → TC (Σ t, Judgement g e t)
| (Exp.free x) g h IH := lookup x g h
| (Exp.bound x) g h IH := error (UnboundIndex x)
| (Exp.sort s) g h IH := match s with
  | star := ok (ContextWF.rec_on h (⟨Exp.sort box, Judgement.starInBox⟩) 
    (λ x _ _ _ _ hns a ⟨t, h⟩, ⟨t, Judgement.weaken x hns h a⟩))
  | box := error BoxInTerm
  end
| (Exp.app f a) g h IH :=
  IH ⟨f, g, h⟩ (typecheck_rel.app_1) >>= λ⟨e, je⟩, 
  IH ⟨a, g, h⟩ (typecheck_rel.app_2) >>= λ⟨A, jA⟩, 
    let ⟨z1, beta1⟩ := (beta_reduce A).get (beta_reduce_terminates_type jA) in begin
    cases h : (head_reduce e),
    case Exp.pi : x A' B begin
      rename h_1 h,
      let zb := (beta_reduce A').get (beta_reduce_terminates_head_reduce_pi je h),
      let h2 : Σ s, Judgement g (Exp.pi x A' B) (Exp.sort s) := begin
        cases classification (preserves_type je),
        simp [a_1, head_reduce] at h, from false.elim h,
        repeat { rw [h] at a_1 }, exact ⟨star, a_1⟩, exact ⟨box, a_1⟩,
      end,
      let h4 : Σ s, Judgement g A' (Exp.sort s) := begin
        cases classification (preserves_type je),
        simp [a_1, head_reduce] at h, from false.elim h,
        repeat { rw [h] at a_1, from typing_pi a_1, },
      end,
      cases exp_decidable_eq z1 zb.1,
        exact error (ExpectedFunctionButGot e),
        apply ok, fapply sigma.mk, exact (instantiate a B), apply Judgement.app,
          apply Judgement.conv, apply eq.mp (by simp [h]) (Beta.head_reduce Eq e),
          from h2.2, from je, apply Judgement.conv, 
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

noncomputable
def typecheck (e : Exp) (g : Context) (h : ContextWF g) : roption (TC (Σ t, Judgement g e t)) :=
begin
  refine ⟨acc typecheck_rel ⟨e,g,h⟩, λ h2, @acc.rec_on (Σ' (e : Exp) (g : Context), ContextWF g) _ 
  (λ y, TC (Σ t, Judgement y.2.1 y.1 t)) _ h2 (λ ⟨e1,g1,h1⟩ ih IH, 
  typecheck_recur e1 g1 h1 IH)⟩,
end

def typecheck_terminates (e : Exp) (g : Context) (h : ContextWF g) : (typecheck e g h).dom
  := sorry

inductive ChurchRosser : Exp → Exp → Prop
| mk : Π (A B : Exp), (Σ z, prod (Beta Eq A z) (Beta Eq B z)) → ChurchRosser A B

def Expr := quot ChurchRosser
def reduce : Exp → Expr := quot.mk ChurchRosser

inductive BetaJudgement (g : Context) (A : Expr) (B : Exp) : Prop
| mk (A' : Exp) (h : reduce A' = A) (j : Judgement g A' B) : BetaJudgement

inductive PTSType : Type
| mk : Π {A : Exp}, Judgement Context.empty A (Exp.sort star) → PTSType

inductive PTSMorphism : PTSType → PTSType → Type
| mk : Π {f : Expr} {A B : Exp} {x}
  (typeA : Judgement (Context.empty) A (Exp.sort star))
  (typeB : Judgement (Context.empty) B (Exp.sort star))
  (funF : BetaJudgement (Context.empty) f (Exp.pi x A B)),
  PTSMorphism (PTSType.mk typeA) (PTSType.mk typeB)

instance pts_has_hom : category_theory.has_hom PTSType := 
  { hom := PTSMorphism }

instance pts_cat_struct : category_theory.category_struct PTSType :=
  { id := λ X,
    begin sorry,
    end
  , comp := λ X Y Z f g,
    begin sorry,
    end
  }

instance hask_cat : category_theory.category PTSType :=
  { id_comp' := begin
      intros, cases f, sorry,
    end
  , comp_id' := begin
      intros, cases f, sorry
    end
  , assoc' := begin
      intros, cases f, sorry
    end
  }