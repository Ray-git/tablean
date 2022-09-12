-- SYNTAX

import data.set.finite
import algebra.big_operators.basic

-- Definition 1, page 4
@[derive decidable_eq]
inductive formula : Type
| bottom : formula
| atom_prop : char -> formula
| neg : formula → formula
| and : formula → formula → formula
| box : formula → formula

/- Predefined atomic propositions for convenience -/
def p := formula.atom_prop 'p'
def q := formula.atom_prop 'q'
def r := formula.atom_prop 'r'

/- Notation and abbreviations -/
notation `·` c       := formula.atom_prop c
prefix `~`:88        := formula.neg
prefix `□`:77        := formula.box
infixr `⋏`:66        := formula.and
@[simp]
def impl (φ ψ : formula) := ~(φ ⋏ (~ψ))
infixr `↣`:55        := impl
infixl `⟷`:77       := λ ϕ ψ, (ϕ ↣ ψ) ⋏ (ψ ↣ ϕ)

@[simp]
instance : has_bot formula := ⟨formula.bottom⟩
instance : has_top formula := ⟨formula.neg formula.bottom⟩

-- showing formulas as strings that are valid Lean code
def formToString : formula → string
| ⊥       := "⊥"
| (· c)   := repr c
| ~ϕ      := "~" ++ formToString ϕ
| (ϕ ⋏ ψ) := "(" ++ formToString ϕ ++ " ⋏ " ++ formToString ψ ++ ")"
| (□ ϕ)   := "(□ "++ formToString ϕ ++ ")"

instance : has_repr formula := ⟨formToString⟩

-- COMPLEXITY

-- this should later be the measure from Lemma 2, page 20
@[simp]
def lengthOfFormula : formula → ℕ
| (⊥)     := 1 -- FIXME: has bad width
| (· c)   := 1
| (~ φ)   := 1 + lengthOfFormula φ
| (φ ⋏ ψ) := 1 + lengthOfFormula φ + lengthOfFormula ψ
| (□ φ)   := 1 + lengthOfFormula φ

@[simp]
def lengthOfSet : finset formula → ℕ
| X := X.sum lengthOfFormula

class hasLength (α : Type) := (lengthOf : α → ℕ)
open hasLength
instance formula_hasLength : hasLength formula := hasLength.mk lengthOfFormula
instance setFormula_hasLength : hasLength (finset formula) := hasLength.mk lengthOfSet

@[simp]
def complexityOfFormula : formula → ℕ
| (⊥)     := 1
| (· c)   := 1
| (~ φ)   := 1 + complexityOfFormula φ
| (φ ⋏ ψ) := 1 + max (complexityOfFormula φ) (complexityOfFormula ψ)
| (□ φ)   := 1 + complexityOfFormula φ

def complexityOfSet : finset formula → ℕ
| X := X.sum complexityOfFormula

class hasComplexity (α : Type) := (complexityOf : α → ℕ)
open hasComplexity
instance formula_hasComplexity : hasComplexity formula := hasComplexity.mk complexityOfFormula
instance setFormula_hasComplexity : hasComplexity (finset formula) := hasComplexity.mk complexityOfSet



/- Syntax of PDL -/

mutual inductive form, prog 
with form : Type 
| atom_form : char → form
| neg : form → form
| conj : form → form → form
| box : prog → form → form
with prog : Type
| atom_prog : char → prog 
| seq : prog → prog → prog 
| star : prog → prog 
| test : form → prog

notation `#` p := form.atom_form p
prefix `!`: 40 := form.neg 
infixr `&&` : 50 := form.conj
prefix `[]` : 42 := form.box
notation `$` a : 40 := prog.atom_prog a
infixr `;` : 48 := prog.seq
-- the next two notation should appear at the end rather than the front, 
-- but I cannot find the dual to "prefix"
prefix `⋆` : 40 := prog.star
prefix `?` : 40 := prog.test


mutual def form_size, prog_size
with form_size : form → nat 
| (form.atom_form _) := 1
| (form.neg φ)       := form_size φ + 1
| (form.conj φ ψ)    := form_size φ + form_size ψ + 1
| (form.box a φ)     := form_size φ + prog_size a  + 1
with prog_size : prog → nat 
| (prog.atom_prog _) := 1
| (prog.seq a b)     := prog_size a + prog_size b + 1
| (prog.star a)      := prog_size a + 1
| (prog.test φ)      := form_size φ + 1


lemma formatom : ∀ (p : char), 0 < form_size (# p) := 
begin 
  intro, unfold form_size, finish,
end 

lemma formneg { φ : form } : 0 < form_size φ → 0 < form_size (! φ) :=
begin 
  intro,unfold form_size, finish,
end 

lemma formconj { φ ψ : form } : 0 < form_size φ → 0 < form_size ψ → 0 < form_size (φ&&ψ) := 
begin 
  intros, unfold form_size, finish,
end 

lemma formbox { φ : form }{ a : prog } : 0 < form_size φ → 0 < prog_size a → 0 < form_size (([]a) φ) :=
begin 
  intros, unfold form_size, finish,
end 

lemma progatom : ∀ (a : char),  0 <  prog_size ($ a) := 
begin 
   intro, unfold prog_size, finish,
end

lemma progseq { a b : prog } : 0 < prog_size a → 0 < prog_size b →  0 < prog_size (a;b) :=
begin 
  intros, unfold prog_size, finish,
end

lemma progstar { a : prog } : 0 < prog_size a → 0 < prog_size (⋆a) :=
begin 
  intros, unfold prog_size, finish,
end 

lemma progtest { φ : form } : 0 < form_size φ → 0 < prog_size (?φ) :=
begin 
  intro, unfold prog_size, finish,
end 

mutual lemma fsize, psize
with fsize : ∀ φ, 0 < form_size φ 
| (# _)       := formatom _
| (! φ)       := formneg (fsize φ)
| (φ&&ψ)      := formconj (fsize φ) (fsize ψ)
| (([]a) φ)   := formbox (fsize φ) (psize a)
with psize :  ∀ a, 0 < prog_size a
| ($ _)       := progatom _
| (a ; b)     := progseq (psize a) (psize b)
| (⋆a)        := progstar (psize a)
| (?φ)        := progtest (fsize φ)