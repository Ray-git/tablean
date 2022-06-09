-- MODELGRAPHS

import syntax
import semantics

open formula

-- Definition 18, page 31
def saturated : finset formula → Prop
| X := ∀ P Q : formula,
  ( ~~P ∈ X → P ∈ X ) ∧
  ( P⋏Q ∈ X → P ∈ X ∧ Q ∈ X ) ∧
  ( ~(P⋏Q) ∈ X → ~P ∈ X ∨ ~Q ∈ X )
  -- TODO: closure for program combinators!

-- Definition 19, page 31
-- TODO: change [] to [A] later
@[simp]
def modelGraph ( Worlds : finset (finset formula) ) :=
  let
    W := subtype (λ x, x ∈ Worlds),
    i   := ∀ X : W, saturated X.val  ∧  ⊥ ∉ X.val  ∧  (∀ P, P ∈ X.val  →  ~P ∉ X.val),
    ii  := λ M : kripkeModel W, (∀ (X : W) pp, ((·pp) ∈ X.val ↔ M.val X pp)),
           -- Note: Borzechowski only has → in ii. We follow BRV, Def 4.18 and 4.84.
    iii := λ M : kripkeModel W, ∀ (X Y : W) P, M.rel X Y → □P ∈ X.val → P ∈ Y.val,
    iv  := λ M : kripkeModel W, ∀ (X : W) P, ~□P ∈ X.val → ∃ Y, M.rel X Y ∧ ~P ∈ Y.val
  in subtype ( λ M : kripkeModel W , i ∧ ii M ∧ iii M ∧ iv M )

-- Lemma 9, page 32
lemma truthLemma { Worlds : finset (finset formula) } (MG : modelGraph Worlds) :
  ∀ X : Worlds, ∀ P, P ∈ X.val → evaluate (MG.val,X) P :=
begin
  intros X P,
  cases MG with M M_prop,
  rcases M_prop with ⟨ i, ii, iii, iv ⟩,
  -- induction loading!!
  let plus  := λ P (X : Worlds),  P ∈ X.val →   evaluate (M,X) P,
  let minus := λ P (X : Worlds), ~P ∈ X.val → ¬ evaluate (M,X) P,
  let oh    := λ P (X : Worlds), □P ∈ X.val → ∀ Y, M.rel X Y → P ∈ Y.val,
  have claim : ∀ P X, plus P X ∧ minus P X ∧ oh P X, {
    intro P,
    induction P, all_goals { intro X, },
    case bottom : {
      specialize i X,
      rcases i with ⟨_, bot_not_in_X, _ ⟩,
      repeat { split },
      { intro P_in_X, apply absurd P_in_X bot_not_in_X, },
      { intro notP_in_X, tauto, },
      { intros boxBot_in_X Y X_rel_Y, exact iii X Y ⊥ X_rel_Y boxBot_in_X },
    },
    case atom_prop : pp {
      repeat { split },
      { intro P_in_X, unfold evaluate, rw (ii X pp) at P_in_X, exact P_in_X, },
      { intro notP_in_X, unfold evaluate, rw ← ii X pp,
        rcases i X with ⟨ _, _, P_in_then_notP_not_in ⟩,
        specialize P_in_then_notP_not_in (· pp), tauto, },
      { intros boxPp_in_X Y X_rel_Y, exact iii X Y (· pp) X_rel_Y boxPp_in_X, },
    },
    case neg : P IH {
      rcases IH X with ⟨ plus_IH, minus_IH, oh_OH ⟩,
      repeat { split },
      { intro notP_in_X, unfold evaluate,
        exact minus_IH notP_in_X, },
      { intro notnotP_in_X,
        rcases i X with ⟨X_saturated, _, _ ⟩,
        cases X_saturated P ⊥ with doubleNeg, -- ⊥ is unused!
        unfold evaluate, simp,
        exact plus_IH (doubleNeg notnotP_in_X),
      },
      { intros notPp_in_X Y X_rel_Y, exact iii X Y (~P) X_rel_Y notPp_in_X, },
    },
    case and : P Q IH_P IH_Q {
      rcases IH_P X with ⟨ plus_IH_P, minus_IH_P, oh_P ⟩,
      rcases IH_Q X with ⟨ plus_IH_Q, minus_IH_Q, oh_Q ⟩,
      rcases i X with ⟨X_saturated, _, _ ⟩,
      unfold saturated at X_saturated,
      rcases X_saturated P Q with ⟨ doubleNeg, andSplit, notAndSplit ⟩,
      repeat { split },
      { intro PandQ_in_X,
        specialize andSplit PandQ_in_X, cases andSplit with P_in_X Q_in_X,
        unfold evaluate,
        split, { exact plus_IH_P P_in_X }, { exact plus_IH_Q Q_in_X, } },
      { intro notPandQ_in_X,
        unfold evaluate, rw not_and_distrib,
        specialize notAndSplit notPandQ_in_X,
        cases notAndSplit with notP_in_X notQ_in_X,
        { left, exact minus_IH_P notP_in_X },
        { right, exact minus_IH_Q notQ_in_X, },
      },
      { intros PandQ_in_X Y X_rel_Y, exact iii X Y (P ⋏ Q) X_rel_Y PandQ_in_X, }
    },
    case box : P IH {
      repeat { split },
      { intro boxP_in_X, unfold evaluate,
        intros Y X_rel_Y,
        rcases IH Y with ⟨ plus_IH_Y, _, _ ⟩,
        apply plus_IH_Y,
        rcases IH X with ⟨ _, _, oh_IH_X ⟩,
        exact oh_IH_X boxP_in_X Y X_rel_Y, },
      { intro notBoxP_in_X, unfold evaluate,
        push_neg,
        rcases iv X P notBoxP_in_X with ⟨ Y, X_rel_Y, notP_in_Y ⟩,
        use Y, split, exact X_rel_Y,
        rcases IH Y with ⟨ _, minus_IH_Y, _ ⟩,
        exact minus_IH_Y notP_in_Y, },
      { intros boxBoxP_in_X Y X_rel_Y, exact iii X Y (□P) X_rel_Y boxBoxP_in_X, }
    },
  },
  apply (claim P X).left,
end
