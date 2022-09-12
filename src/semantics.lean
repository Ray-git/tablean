import order.complete_lattice
import order.fixed_points
import data.set.lattice

import syntax

-- Definition 2, page 6
structure kripkeModel (W : Type) : Type :=
  (val : W → char → Prop)
  (rel : W → W → Prop)

-- Definition 3, page 6
def evaluate {W : Type} : (kripkeModel W × W) → formula → Prop
| (M,w) ⊥       := false
| (M,w) (· p)   := M.val w p
| (M,w) (~ φ)   := ¬ evaluate (M,w) φ
| (M,w) (φ ⋏ ψ) := evaluate (M,w) φ ∧ evaluate (M,w) ψ
| (M,w) (□ φ)   := ∀ v : W, (M.rel w v → evaluate (M,v) φ)

def tautology     (φ : formula) := ∀ W (M : kripkeModel W) w, evaluate (M,w) φ
def contradiction (φ : formula) := ∀ W (M : kripkeModel W) w, ¬ evaluate (M,w) φ

-- Definition 4, page 8

-- Definition 5, page 9
class has_sat (α : Type) := (satisfiable : α → Prop)
open has_sat
instance form_has_sat : has_sat formula := has_sat.mk (λ ϕ, ∃ W (M : kripkeModel W) w, evaluate (M,w) ϕ)
instance set_has_sat : has_sat (finset formula) := has_sat.mk (λ X, ∃ W (M : kripkeModel W) w, (∀ φ ∈ X, evaluate (M,w) φ))

lemma notsatisfnotThenTaut : ∀ φ, ¬ satisfiable (~φ) → tautology φ :=
begin
  intro phi,
  unfold satisfiable,
  unfold tautology,
  simp,
  intro lhs,
  intros W M w,
  specialize lhs W M w,
  unfold evaluate at *,
  simp at lhs,
  exact lhs,
end

@[simp]
lemma singletonSat_iff_sat : ∀ φ, satisfiable ({ φ } : finset formula) ↔ satisfiable φ :=
begin
  intro phi,
  unfold satisfiable,
  simp,
end

lemma tautImp_iff_comboNotUnsat {ϕ ψ} : tautology (ϕ ↣ ψ) ↔ ¬satisfiable ({ϕ, ~ψ} : finset formula) :=
begin
  unfold tautology,
  unfold satisfiable,
  simp,
  split ;
  { intro hyp,
    intros W M w,
    specialize hyp W M w,
    intro sat_phi,
    unfold evaluate at *, simp at *, tauto,
  },
end

def semImplies_sets (X : finset formula) (Y : finset formula) := ∀ (W : Type) (M : kripkeModel W) w,
  (∀ φ ∈ X, evaluate (M,w) φ) → (∀ ψ ∈ Y, evaluate (M,w) ψ)

-- Definition 5, page 9
class vDash {α : Type} {β : Type} := (semImplies : α → β → Prop)
open vDash
@[simp]
instance model_canSemImply_form {W : Type} : vDash := vDash.mk (@evaluate W)
@[simp]
instance model_canSemImply_set {W : Type} : vDash := @vDash.mk (kripkeModel W × W) (finset formula) (λ Mw X, ∀ f ∈ X, @evaluate W Mw f)
instance set_canSemImply_set : vDash := vDash.mk semImplies_sets
instance set_canSemImply_form : vDash := vDash.mk (λ X ψ, semImplies_sets X {ψ})
instance form_canSemImply_set : vDash := vDash.mk (λ φ X, semImplies_sets {φ} X)
instance form_canSemImply_form : vDash := vDash.mk (λ φ ψ, semImplies_sets {φ} {ψ})

infixl `⊨`:40 := semImplies
infixl `⊭`:40 := λ a b, ¬ (a ⊨ b)

-- useful lemmas to connect all the different ⊨ cases

lemma forms_to_sets { φ ψ : formula } : φ ⊨ ψ → ({φ}: finset formula) ⊨ ({ψ} : finset formula):=
begin
  intros impTaut,
  intros W M w lhs ψ1 psi1_in_setpsi,
  specialize impTaut W M w,
  simp at *,
  subst psi1_in_setpsi,
  apply impTaut,
  exact lhs
end



/- Semantics for PDL -/

structure frame (W : Type) : Type :=
  (val : W → char → Prop)
  (rel : char → W → W → Prop)


def size {W : Type} : psum (Σ' (ᾰ : frame W) (ᾰ : W), form) 
(Σ' (ᾰ : frame W) (ᾰ : prog) (ᾰ : W), W) → ℕ
| (psum.inl ⟨_, ⟨_, φ⟩⟩) := form_size φ 
| (psum.inr ⟨_, ⟨a, ⟨_, _⟩⟩⟩) := prog_size a

inductive closure {X: Type} (P : X → X → Prop) :  X → X → Prop
| base : ∀ (x : X), closure x x
| inductive_step : ∀ (x y z : X), P x y → closure y z → closure x z




lemma decrease1 {W : Type} { F : frame W} {w : W } {φ} :  
size (psum.inl ⟨F, ⟨w, φ⟩⟩) < size (psum.inl ⟨F, ⟨w, !φ⟩⟩) := 
begin 
  intros, unfold size, unfold form_size, finish,
end 

lemma decrease2 {W : Type} { F : frame W} {w : W } {φ} {ψ}:  
size (psum.inl ⟨F, ⟨w, φ⟩⟩) < size (psum.inl ⟨F, ⟨w, φ&&ψ⟩⟩) :=
begin 
  intros, unfold size, unfold form_size,
  have h1 : form_size φ <  form_size φ + 1, finish,
  have h2 : form_size φ + 1 ≤ form_size φ + form_size ψ + 1, 
  have h3 : form_size φ + form_size ψ + 1 = form_size φ + 1 + form_size ψ, finish,
  rw h3, have h4 := fsize ψ,
  have h5 :  form_size φ + 1 + 0 < form_size φ + 1 + form_size ψ, finish,
  finish, exact nat.lt_of_lt_of_le h1 h2,
end 

lemma decrease3 {W : Type} { F : frame W} {w : W } {φ} {ψ}:  
size (psum.inl ⟨F, ⟨w, ψ⟩⟩) < size (psum.inl ⟨F, ⟨w, φ&&ψ⟩⟩) :=
begin 
  intros, unfold size, unfold form_size,
  have h1 : form_size ψ <  form_size ψ + 1, finish,
  have h2 : form_size ψ + 1 ≤ form_size φ + form_size ψ + 1, 
  have h3 : form_size φ + form_size ψ + 1 = form_size ψ + 1 + form_size φ, finish,
  rw h3, have h4 := fsize φ,
  have h5 :  form_size ψ + 1 + 0 < form_size ψ + 1 + form_size φ, finish,
  finish, exact nat.lt_of_lt_of_le h1 h2,
end 

lemma decrease4 {W : Type} { F : frame W} {w : W } {φ} {a}:  
size (psum.inl ⟨F, ⟨w, φ⟩⟩) < size (psum.inl ⟨F, ⟨w, form.box a φ⟩⟩) := 
begin 
  intros, unfold size, unfold form_size,
  have h1 : form_size φ <  form_size φ + 1, finish,
  have h2 : form_size φ + 1 ≤ form_size φ + prog_size a + 1, 
  have h3 : form_size φ + prog_size a + 1 = form_size φ + 1 + prog_size a, finish,
  rw h3, have h4 := psize a,
  have h5 :  form_size φ + 1 + 0 < form_size φ + 1 + prog_size a, finish,
  finish, exact nat.lt_of_lt_of_le h1 h2,
end 

lemma decrease5 {W : Type} { F : frame W} {w v : W } {φ} {a}: 
size (psum.inr ⟨F, ⟨a, ⟨w, v⟩⟩⟩) < size (psum.inl ⟨F, ⟨w, form.box a φ⟩⟩) := 
begin 
  intros, unfold size, unfold form_size,
  have h1 : prog_size a <  prog_size a + 1, finish,
  have h2 : prog_size a + 1 ≤ form_size φ + prog_size a + 1, 
  have h3 : prog_size a + 1 + form_size φ = form_size φ + prog_size a + 1, finish,
  rw ← h3, have h4 := fsize φ,
  have h5 : prog_size a + 1 + 0 < prog_size a + 1 + form_size φ, finish,
  finish, exact nat.lt_of_lt_of_le h1 h2,
end 

lemma decrease6 {W : Type} { F : frame W} {w v: W } {a b}: 
size (psum.inr ⟨F, ⟨a, ⟨w, v⟩⟩⟩) < size (psum.inr ⟨F, ⟨a ; b, ⟨w, v⟩⟩⟩) := 
begin 
  intros, unfold size, unfold prog_size,
  have h1 : prog_size a <  prog_size a + 1, finish,
  have h2 : prog_size a + 1 ≤ prog_size a + prog_size b + 1, 
  have h3 : prog_size a + 1 + prog_size b = prog_size a + prog_size b + 1, finish,
  rw ← h3, have h4 := psize b,
  have h5 : prog_size a + 0 + 1 < prog_size a + prog_size b + 1, finish,
  finish, exact nat.lt_of_lt_of_le h1 h2,
end 

lemma decrease7 {W : Type} { F : frame W} {w v: W } {a b}: 
size (psum.inr ⟨F, ⟨b, ⟨w, v⟩⟩⟩) < size (psum.inr ⟨F, ⟨a ; b, ⟨w, v⟩⟩⟩) := 
begin 
  intros, unfold size, unfold prog_size,
  have h1 : prog_size b <  prog_size b + 1, finish,
  have h2 : prog_size b + 1 ≤ prog_size a + prog_size b + 1, 
  have h3 : prog_size a + 1 + prog_size b = prog_size a + prog_size b + 1, finish,
  rw ← h3, have h4 := psize b,
  have h5 : prog_size a + 0 + 1 < prog_size a + prog_size b + 1, finish,
  finish, exact nat.lt_of_lt_of_le h1 h2,
end

lemma decrease8 {W : Type} { F : frame W} {w v: W } {φ}: 
size (psum.inl ⟨F, ⟨w, φ⟩⟩) < size (psum.inr ⟨F, ⟨?φ, ⟨w, v⟩⟩⟩) := 
begin 
  intros, unfold size, unfold prog_size, finish,
end 

lemma  decrease9 {W : Type} { F : frame W} {w v: W } {a}:
size (psum.inr ⟨F, ⟨a, ⟨w, v⟩⟩⟩) < size (psum.inr ⟨F, ⟨⋆a, ⟨w, v⟩⟩⟩) := 
begin 
  intros, unfold size, unfold prog_size, finish,
end 



mutual def sat, path {W : Type}{ v : W } 
with sat : (frame W) → W → form → Prop 
| F w (# p) := F.val w p
| F w (! φ) := 
  have size (psum.inl ⟨F, ⟨w, φ⟩⟩) < size (psum.inl ⟨F, ⟨w, !φ⟩⟩),
  from decrease1,
  ¬ (sat F w φ)
| F w (φ && ψ) := 
  have size (psum.inl ⟨F, ⟨w, φ⟩⟩) < size (psum.inl ⟨F, ⟨w, φ&&ψ⟩⟩), 
  from decrease2,
  have size (psum.inl ⟨F, ⟨w, ψ⟩⟩) < size (psum.inl ⟨F, ⟨w, φ&&ψ⟩⟩), 
  from decrease3,
  (sat F w φ) ∧ (sat F w ψ) 
| F w (form.box a φ) := 
  have size (psum.inr ⟨F, ⟨a, ⟨w, v⟩⟩⟩) < size (psum.inl ⟨F, ⟨w, form.box a φ⟩⟩),
  from decrease5,
  have size (psum.inl ⟨F, ⟨w, φ⟩⟩) < size (psum.inl ⟨F, ⟨w, form.box a φ⟩⟩),
  from decrease4,
  ∃ (v : W), (path F a w v) ∧ (sat F v φ)
with path : frame W → prog → W → W → Prop
| F ($ a) w v := F.rel a w v 
| F (a ; b) w v := 
  have size (psum.inr ⟨F, ⟨a, ⟨w, v⟩⟩⟩) < size (psum.inr ⟨F, ⟨a ; b, ⟨w, v⟩⟩⟩),
  from decrease6,
  have size (psum.inr ⟨F, ⟨b, ⟨w, v⟩⟩⟩) < size (psum.inr ⟨F, ⟨a ; b, ⟨w, v⟩⟩⟩),
  from decrease7,
  ∃ (u : W), (path F a w u) ∧ (path F b u v) 
| F (? φ) w v := 
  have size (psum.inl ⟨F, ⟨w, φ⟩⟩) < size (psum.inr ⟨F, ⟨?φ, ⟨w, v⟩⟩⟩),
  from decrease8,
  (w = v) ∧ (sat F w φ)
| F (⋆ a) w v := 
  have size (psum.inr ⟨F, ⟨a, ⟨w, v⟩⟩⟩) < size (psum.inr ⟨F, ⟨⋆a, ⟨w, v⟩⟩⟩),
  from  decrease9,
  closure (path F a) w v 
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf size⟩] }



