-- TABLEAU

import data.finset.basic
import data.finset.pimage
import algebra.big_operators.order
import tactic
import order.well_founded_set

import syntax
import semantics
import setsimp

open formula
open hasLength

-- Definition 9, page 15
-- A set X is closed  iff  0 ∈ X or X contains a formula and its negation.
def closed : finset formula → Prop := λ X, ⊥ ∈ X ∨ ∃ f ∈ X, ~f ∈ X
-- A set X is simple  iff  all P ∈ X are (negated) atoms or [A]_ or ¬[A]_.
def simpleForm : formula → Prop
| ⊥       := true
| (~⊥)    := true -- added!
| (· _)   := true
| ~(· _)  := true
| (□ _)   := true
| ~(□ _)  := true
| _       := false
instance (ϕ) : decidable (simpleForm ϕ) := begin
  cases ϕ,
  case bottom: { apply decidable.is_true, tauto, },
  case atom_prop: { apply decidable.is_true, tauto, },
  case neg: { cases ϕ,
    case bottom: { apply decidable.is_true, tauto, },
    case atom_prop: { apply decidable.is_true, tauto, },
    case neg: { apply decidable.is_false, tauto, },
    case and: { apply decidable.is_false, tauto, },
    case box: { apply decidable.is_true, tauto, },
  },
  case and: { apply decidable.is_false, tauto, },
  case box: { apply decidable.is_true, tauto, },
end
@[derive decidable]
def simple : finset formula → Prop
| X := ∀ P ∈ X, simpleForm P
-- Let X_A := { R | [A]R ∈ X }.
@[simp]
def formProjection : formula → option formula
| (□f) := some f
| _    := none
def projection : finset formula → finset formula
| X := X.bUnion (λ x, (formProjection x).to_finset)

lemma proj { g: formula } { X : finset formula } :
  g ∈ projection X ↔ □g ∈ X :=
begin
  unfold projection,
  simp,
  split,
  { intro lhs,
    rcases lhs with ⟨ boxg, boxg_in_X, projboxg_is_g ⟩,
    cases boxg,
    repeat { finish },
  },
  { intro rhs,
    use □g,
    split,
    exact rhs,
    simp,
  },
end

lemma projSet {X : finset formula} : ↑(projection X) = { ϕ | □ϕ ∈ X } :=
begin
  ext1,
  unfold_coes,
  simp,
  exact proj,
end

lemma projection_length_leq : ∀ f, (projection {f}).sum lengthOfFormula ≤ lengthOfFormula f :=
begin
  intro f,
  cases f,
  { omega, },
  { exact dec_trivial, },
  { exact dec_trivial, },
  { exact dec_trivial, },
  { have subsubClaim : projection {□f} = {f}, {
      ext1, rw proj, simp,
    },
    rw subsubClaim,
    unfold lengthOfFormula, simp,
  },
end

lemma projection_set_length_leq : ∀ X, lengthOfSet (projection X) ≤ lengthOfSet X :=
begin
intro X,
apply finset.induction_on X,
{ unfold lengthOfSet, simp, intros f f_in_empty, cases f_in_empty, },
{ intros f S f_not_in_S IH,
  unfold lengthOfSet,
  rw finset.sum_insert f_not_in_S,
  simp,
  have insert_comm_proj : ∀ X f, projection (insert f X) = (projection {f}) ∪ (projection X), {
    intros X f,
    unfold projection,
    ext1 g,
    simp,
  },
  { calc (projection (insert f S)).sum lengthOfFormula
       = (projection (insert f S)).sum lengthOfFormula : refl _
   ... = (projection {f} ∪ projection S).sum lengthOfFormula : by { rw insert_comm_proj S f, }
   ... ≤ (projection {f}).sum lengthOfFormula + (projection S).sum lengthOfFormula : by { apply sum_union_le, }
   ... ≤ lengthOfFormula f + (projection S).sum lengthOfFormula : by { simp only [add_le_add_iff_right, projection_length_leq], }
   ... ≤ lengthOfFormula f + S.sum lengthOfFormula : by { simp, apply IH, },
  },
},
end

-- local rules: given this set, we get these sets as child nodes
inductive localRule : finset formula → finset (finset formula) → Type
-- closing rules:
| bot {X    } (h : ⊥          ∈ X) : localRule X ∅
| not {X ϕ  } (h : ϕ ∈ X ∧ ~ϕ ∈ X) : localRule X ∅
-- one-child rules:
| neg {X ϕ  } (h : ~~ϕ   ∈ X) : localRule X { (X \ {~~ϕ}) ∪ { ϕ }    }
| con {X ϕ ψ} (h : ϕ ⋏ ψ ∈ X) : localRule X { (X \ {ϕ ⋏ ψ}) ∪ { ϕ, ψ } }
-- splitting rule:
| nCo {X ϕ ψ} (h : ~(ϕ ⋏ ψ) ∈ X) : localRule X { X \ { ~ (ϕ ⋏ ψ) } ∪ {~ϕ}
                                                 , X \ { ~ (ϕ ⋏ ψ) } ∪ {~ψ} }

-- If X is not simple, then a local rule can be applied.
-- (page 13)
lemma notSimpleThenLocalRule { X } :
  -- TODO write this as: nonempty (Σ B, localRule X B)
  ¬ simple X → (∃ B (_ : localRule X B), true) :=
begin
  intro notSimple,
  unfold simple at notSimple,
  simp at notSimple,
  rcases notSimple with ⟨ ϕ , ϕ_in_X, ϕ_not_simple ⟩,
  cases ϕ,
  case bottom: { tauto },
  case atom_prop: { tauto },
  case neg: ψ {
    cases ψ,
    case bottom: { tauto, },
    case atom_prop: { tauto, },
    case neg: {
      use { (X \ {~~ψ}) ∪ { ψ } },
      use localRule.neg ϕ_in_X,
    },
    case and: ψ1 ψ2 {
      unfold simpleForm at *,
      use { X \ { ~ (ψ1 ⋏ ψ2) } ∪ {~ψ1}, X \ { ~ (ψ1 ⋏ ψ2) } ∪ {~ψ2} },
      use localRule.nCo ϕ_in_X,
    },
    case box: { unfold simpleForm at *, tauto, },
  },
  case and: ψ1 ψ2 {
      unfold simpleForm at *,
      use { (X \ {ψ1 ⋏ ψ2}) ∪ { ψ1, ψ2 } },
      use localRule.con ϕ_in_X,
  },
  case box: { tauto, },
end

lemma localRulesDecreaseLength { X : finset formula } { B : finset (finset formula) } (r : localRule X B) :
  ∀ Y ∈ B, lengthOfSet Y < lengthOfSet X :=
begin
  cases r,
  all_goals { intros β inB, simp at *, },
  case bot : {
    cases inB, -- no premises
  },
  case not : {
    cases inB, -- no premises
  },
  case neg : X ϕ notnot_in_X {
    subst inB,
    { calc lengthOfSet (insert ϕ (X.erase (~~ϕ)))
         ≤ lengthOfSet (X.erase (~~ϕ)) + lengthOf (ϕ) : by { apply lengthOf_insert_leq_plus, }
     ... < lengthOfSet (X.erase (~~ϕ)) + lengthOf (ϕ) + 2 : by { simp, }
     ... = lengthOfSet (X.erase (~~ϕ)) + lengthOf (~~ϕ) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet X : lengthRemove X (~~ϕ) notnot_in_X,
    },
  },
  case con : X ϕ ψ in_X {
    subst inB,
    { calc lengthOf (insert ϕ (insert ψ (X.erase (ϕ⋏ψ))))
         ≤ lengthOf (insert ψ (X.erase (ϕ⋏ψ))) + lengthOf ϕ : by { apply lengthOf_insert_leq_plus, }
     ... ≤ lengthOf (X.erase (ϕ⋏ψ)) + lengthOf ψ + lengthOf ϕ : by { simp, apply lengthOf_insert_leq_plus, }
     ... = lengthOf (X.erase (ϕ⋏ψ)) + lengthOf ϕ + lengthOf ψ : by { ring, }
     ... < lengthOf (X.erase (ϕ⋏ψ)) + lengthOf ϕ + lengthOf ψ + 1 : by { unfold lengthOf, simp, }
     ... = lengthOf (X.erase (ϕ⋏ψ)) + lengthOf (ϕ⋏ψ) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet X : (lengthRemove X (ϕ⋏ψ) in_X)
    },
  },
  case nCo : X ϕ ψ in_X {
    cases inB, -- splitting rule!
    all_goals {
      subst inB,
    },
    { -- f
    calc lengthOfSet (insert (~ϕ) (X.erase (~(ϕ⋏ψ))))
         ≤ lengthOfSet (X.erase (~(ϕ⋏ψ))) + lengthOf (~ϕ) : lengthOf_insert_leq_plus
     ... < lengthOfSet (X.erase (~(ϕ⋏ψ))) + 1 + 1 + lengthOf ϕ + lengthOf ψ :
           by { unfold lengthOf, unfold lengthOfFormula, ring_nf, simp, }
     ... = lengthOfSet (X.erase (~(ϕ⋏ψ))) + lengthOf (~(ϕ⋏ψ)) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet X : lengthRemove X (~(ϕ⋏ψ)) in_X,
    },
    { -- g
    calc lengthOfSet (insert (~ψ) (X.erase (~(ϕ⋏ψ))))
         ≤ lengthOfSet (X.erase (~(ϕ⋏ψ))) + lengthOf (~ψ) : lengthOf_insert_leq_plus
     ... < lengthOfSet (X.erase (~(ϕ⋏ψ))) + 1 + 1 + lengthOf ϕ + lengthOf ψ :
           by { unfold lengthOf, unfold lengthOfFormula, ring_nf, simp, }
     ... = lengthOfSet (X.erase (~(ϕ⋏ψ))) + lengthOf (~(ϕ⋏ψ)) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet X : lengthRemove X (~(ϕ⋏ψ)) in_X,
    },
  },
end

lemma atmRuleDecreasesLength { X : finset formula } { ϕ } :
  ~□ϕ ∈ X → lengthOfSet (projection X ∪ {~ϕ}) < lengthOfSet X :=
begin
  intro notBoxPhi_in_X,
  simp,
    have proj_form_lt : ∀ f g, some g = formProjection f → lengthOfFormula g < lengthOfFormula f, {
      intros f g g_is_fP_f, cases f, all_goals { finish, },
    },
    have lengthSingleton : ∀ f, lengthOfFormula f = lengthOfSet { f }, {
      intro f, unfold lengthOfSet, simp,
    },
    have otherClaim : projection X = projection (X.erase (~□ϕ)), {
      ext1 phi,
      rw proj, rw proj,
      simp,
    },
    { calc lengthOfSet (insert (~ϕ) (projection X))
         ≤ lengthOfSet (projection X) + lengthOf (~ϕ) : lengthOf_insert_leq_plus
     ... = lengthOfSet (projection X) + 1 + lengthOf ϕ : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... < lengthOfSet (projection X) + 1 + 1 + lengthOf ϕ : by { simp, }
     ... = lengthOfSet (projection X) + lengthOf (~□ϕ) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet (projection (X.erase (~□ϕ))) + lengthOf (~□ϕ) : by { rw otherClaim, }
     ... ≤ lengthOfSet (X.erase (~□ϕ)) + lengthOf (~□ϕ) : by { simp, apply projection_set_length_leq, }
     ... = lengthOfSet X : lengthRemove X (~□ϕ) notBoxPhi_in_X,
    }
end

-- Definition 8, page 14
-- mixed with Definition 11 (with all PDL stuff missing for now)
-- a local tableau for X, must be maximal
inductive localTableau : finset formula → Type
| byLocalRule { X B } (_ : localRule X B) (next : Π Y ∈ B, localTableau Y) : localTableau X
| sim { X } : simple X → localTableau X

open localTableau

-- needed for endNodesOf
instance localTableau_has_sizeof : has_sizeof (Σ {X}, localTableau X) := ⟨ λ ⟨X, T⟩, lengthOfSet X ⟩

-- open end nodes of a given localTableau
@[simp]
def endNodesOf : (Σ X, localTableau X) → finset (finset formula)
| ⟨X, @byLocalRule _ B lr next⟩ := B.attach.bUnion (λ ⟨Y,h⟩, have lengthOfSet Y < lengthOfSet X := localRulesDecreaseLength lr Y h, endNodesOf ⟨Y, next Y h⟩)
| ⟨X, sim _                   ⟩ := { X }

@[simp]
lemma botNoEndNodes {X h n} : endNodesOf ⟨X, localTableau.byLocalRule (@localRule.bot X h) n⟩ = ∅ := by { unfold endNodesOf, simp, }

@[simp]
lemma notNoEndNodes {X h ϕ n} : endNodesOf ⟨X, localTableau.byLocalRule (@localRule.not X h ϕ) n⟩ = ∅ := by { unfold endNodesOf, simp, }

lemma setEndNodes {X B lr next} : endNodesOf ⟨X, @byLocalRule _ B lr next⟩ = B.attach.bUnion (λ ⟨Y,h⟩, endNodesOf ⟨Y, next Y h⟩) :=
begin
  simp,
  ext1,
  finish,
end

-- Definition 16, page 29
inductive closedTableau : finset formula → Type
| loc {X} (lt : localTableau X) : (Π Y ∈ endNodesOf ⟨X, lt⟩, closedTableau Y) → closedTableau X
| atm {X ϕ} : ~□ϕ ∈ X → simple X → closedTableau (projection X ∪ {~ϕ}) → closedTableau X

inductive provable : formula → Prop
| byTableau {φ : formula} : closedTableau { ~ φ } → provable φ

-- Definition 17, page 30
def inconsistent : finset formula → Prop
| X := nonempty (closedTableau X)

def consistent : finset formula → Prop
| X := ¬ inconsistent X


-- FIXME: should be data instead of Prop
def existsLocalTableauFor : ∀ N α, N = lengthOf α → ∃ _ : localTableau α, true :=
begin
  intro N,
  apply nat.strong_induction_on N, -- TODO: only works in Prop?
  intros n IH α nDef,
  have canApplyRule := em (¬ ∃ B (_ : localRule α B), true),
  cases canApplyRule,
  { split,
    apply localTableau.sim,
    by_contradiction hyp,
    have fop := notSimpleThenLocalRule hyp,
    tauto,
    tauto,
  },
  { simp at canApplyRule,
    cases canApplyRule with B r_exists,
    cases r_exists with r _hyp,
    cases r,
    case bot : _ h {
      have t := (localTableau.byLocalRule (localRule.bot h)) _, use t,
      intro beta, intro beta_in_empty, tauto,
    },
    case not : _ _ h {
      have t := (localTableau.byLocalRule (localRule.not h)) _, use t,
      intro beta, intro beta_in_empty, tauto,
    },
    case neg : _ f h {
      have t := (localTableau.byLocalRule (localRule.neg h)) _, use t,
      intros beta beta_def,
      have rDec := localRulesDecreaseLength (localRule.neg h) beta beta_def,
      subst nDef,
      specialize IH (lengthOf beta) rDec beta,
      simp at IH,
      choose t _true using IH,
      use t,
    },
    case con : _ f g h {
      have t := localTableau.byLocalRule (localRule.con h) _, use t,
      intros beta beta_def,
      have rDec := localRulesDecreaseLength (localRule.con h) beta beta_def,
      subst nDef,
      specialize IH (lengthOf beta) rDec beta,
      simp at IH,
      choose t _true using IH,
      use t,
    },
    case nCo : _ f g h {
      have t := localTableau.byLocalRule (localRule.nCo h) _, use t,
      intros beta beta_def,
      have rDec := localRulesDecreaseLength (localRule.nCo h) beta beta_def,
      subst nDef,
      specialize IH (lengthOf beta) rDec beta,
      simp at IH,
      choose t _true using IH,
      use t,
    },
  }
end

lemma endNodesOfLEQ {X Z ltX} :
  Z ∈ endNodesOf ⟨X, ltX⟩ → lengthOf Z ≤ lengthOf X :=
begin
  induction ltX,
  case byLocalRule : Y B lr next IH {
    intro Z_endOf_Y,
    have foo := localRulesDecreaseLength lr Y,
    unfold endNodesOf at Z_endOf_Y,
    simp at Z_endOf_Y,
    rcases Z_endOf_Y with ⟨W, W_in_B, Z_endOf_W⟩,
    apply le_of_lt,
    { calc lengthOf Z
         ≤ lengthOf W : IH W W_in_B Z_endOf_W
     ... < lengthOf Y : localRulesDecreaseLength lr W W_in_B },
  },
  case sim : a b {
    intro Z_endOf_Y,
    unfold endNodesOf at Z_endOf_Y,
    finish,
  },
end

lemma endNodesOfLocalRuleLT {X Z B next lr} :
  Z ∈ endNodesOf ⟨X, (@localTableau.byLocalRule _ B lr next)⟩ → lengthOf Z < lengthOf X :=
begin
  intros ZisEndNode,
  rw setEndNodes at ZisEndNode,
  simp only [finset.mem_bUnion, finset.mem_attach, exists_true_left, subtype.exists] at ZisEndNode,
  rcases ZisEndNode with ⟨a,a_in_WS,Z_endOf_a⟩,
  change Z ∈ endNodesOf ⟨a, next a a_in_WS⟩ at Z_endOf_a,
  { calc lengthOf Z
       ≤ lengthOf a : endNodesOfLEQ Z_endOf_a
   ... < lengthOfSet X : localRulesDecreaseLength lr a a_in_WS },
end

-- thanks to Mario Carneiro via Zulip!
instance contains_diamond.decidable (X : finset formula) : decidable (∃ ϕ, ~□ϕ ∈ X) :=
begin
  haveI : ∀ X, decidable (∃ ϕ, X = (~□ ϕ)) := by
    rintro (_ | _ | (_|_|_) | z);
      { exact is_true ⟨_, rfl⟩ <|> { apply is_false, rintro ⟨_, ⟨⟩⟩ } },
  exact decidable_of_iff (∃ f ∈ X, ∃ ϕ, f = ~□ϕ)
    ⟨λ ⟨_, h, ϕ, rfl⟩, ⟨ϕ, h⟩, λ ⟨ϕ, h⟩, ⟨_, h, ϕ, rfl⟩⟩,
end
