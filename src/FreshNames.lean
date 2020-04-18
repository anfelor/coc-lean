import data.finset
import tactic.norm_num

import Terms

/-! This file deals with the generation of fresh variable names -/

/-- The pigeonhole principle for finsets -/
lemma pigeonhole : Π (ys : finset string) (xs : finset string), 
  (finset.card ys < finset.card xs) → finset.nonempty (xs \ ys)
| ys := λ xs h, if h2 : finset.card ys = 0 then 
  begin 
    have h3 : xs = xs \ ys := by
    { rw [finset.ext], intro, rw [finset.mem_sdiff], apply iff.intro,
      { intro, split, assumption, rw [finset.card_eq_zero] at h2, simp [h2], },
      intro, cases a_1, assumption, },
    rw [h2, finset.card_pos, h3] at h, assumption,
  end else 
  begin
    -- we will rewrite h2 later and keep this as a save
    have h6 : finset.card ys ≠ 0 := by assumption,
    rw [finset.card_eq_zero, eq.symm (ne.def _ _)] at h2,
    rw [finset.nonempty_iff_ne_empty.symm] at h2, cases h2.bex,
    have h' : finset.card (finset.erase ys w) < finset.card (finset.erase xs w) := by
    { cases finset.decidable_mem w xs, 
      { rw [finset.erase_eq_of_not_mem h_2],
        have h7 : finset.card ys > 0 := nat.pos_of_ne_zero h6,
        rw [finset.card_erase_of_mem h_1], 
        rw [(nat.succ_pred_eq_of_pos h7).symm] at h,
        exact nat.lt_of_succ_lt h, },
      rw [finset.card_erase_of_mem h_1, finset.card_erase_of_mem h_2],
      exact nat.pred_lt_pred h6 h, },
    let wf_erase : finset.erase ys w ⊂ ys := finset.erase_ssubset h_1,
    let ne := pigeonhole (finset.erase ys w) (finset.erase xs w) h',
    cases ne.bex, have h4 : w_1 ∈ xs \ ys, 
    { rw [finset.mem_sdiff] at h_2, cases h_2,
      simp [finset.mem_of_mem_erase] at h_2_left, cases h_2_left with neq inxs,
      let h5 : w_1 ∉ ys := mt (finset.mem_erase_of_ne_of_mem neq) h_2_right,
      simp, exact ⟨inxs, h5⟩, },
    exact ⟨w_1, h4⟩,
  end
using_well_founded { rel_tac := λ e es, `[exact ⟨_,(@finset.lt_wf string)⟩],
    dec_tac := `[assumption] }

/-- We will create fresh names by appending primes which has the advantage
    of having a short injectivity proof. A real-world compiler should append
    digits though (also injective but harder to prove). -/
def mk_name (x : string) : nat → string
| 0 := x
| (n+1) := (mk_name n) ++ "'"

lemma string.length_append (x y : string) :
  (x ++ y).length = x.length + y.length :=
begin
  cases x, cases y, simp [(++), string.append, string.length],
  from list.length_append x y,
end

lemma mk_name_len (x : string) (n : nat)
  : (mk_name x n).length = x.length + n :=
begin
  induction n, simp [mk_name], simp [mk_name, string.length_append, n_ih],
  have h : string.length "'" = 1 := by refl, rw [h, nat.succ_eq_add_one],
end

lemma mk_name_inj (x : string) : function.injective (mk_name x) := 
begin
  intros a1 a2 h, have h2 : (mk_name x a1).length = (mk_name x a2).length,
  from eq.rec_on h (eq.refl (mk_name x a1).length),
  simp [mk_name_len] at h2, from h2,
end

/-- Find a fresh name that is close to x but not in xs -/
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
      simp [h_1], simp at h,
      from absurd h_1 (fresh_is_fresh h),
    cases eq.decidable b n, iterate 2 { simp [h_1] },
    simp,

    simp at h,
    let h_a := finset.subset.trans (finset.subset_union_left _ _) h,
    let h_a_1 := finset.subset.trans (finset.subset_union_right _ _) h,
    simp [b_ih_a h_a, b_ih_a_1 h_a_1],

  iterate 2 {
    simp at h,
    let h_a_1 := finset.subset.trans (finset.subset_union_left _ _) h,
    let h_a_2 := finset.subset.trans (finset.subset_union_right _ _) h,
    simp [b_ih_a h_a_1, b_ih_a_1 h_a_2], },
end

/-- Instantiating a fresh variable and then abstracting it is the identity. -/
lemma fresh_avoids_capture {x b xs} (h : free_vars b ⊆ xs) 
  : abstract (fresh xs x) (instantiate (Exp.free (fresh xs x)) b) = b :=
  fresh_avoids_capture_help h 0

/-- Top-level one-step beta reduction. -/
def head_reduce : Exp → Exp
| (Exp.app a b) := match a with
    Exp.lam _ _ d := instantiate b d,
    _ := Exp.app a b
  end
| e := e