import category_theory.category

import Terms
import CoC

/-! This file will eventually contain a proof that CoC Types form a category.
    It is very much incomplete and depends on computablility of the type-checker. -/

open PTSSort
open BetaOpt

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