module

public import Foundation.Logic.LogicSymbol
public import Mathlib.Data.Finset.Preimage

/-!
# Modal formulas

Formulas of the modal propositional language with the primitives `⊥`, `🡒` and `□`; the other
connectives are abbreviations in the Łukasiewicz style.
-/

@[expose] public section

namespace FFL.ProvabilityLogic

inductive Formula (α : Type*) where
  | atom   : α → Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α
  deriving DecidableEq

abbrev FormulaFinset (α) := Finset (Formula α)

namespace Formula

variable {α : Type*} {A B : Formula α}

prefix:max "#" => Formula.atom

abbrev neg (A : Formula α) : Formula α := imp A falsum

abbrev verum : Formula α := imp falsum falsum

abbrev or (A B : Formula α) : Formula α := imp (neg A) B

abbrev and (A B : Formula α) : Formula α := neg (imp A (neg B))

abbrev dia (A : Formula α) : Formula α := neg (box (neg A))

instance : LogicalConnective (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or

instance : LogicalNeutral (Formula α) where
  top := verum
  bot := falsum

instance : Box (Formula α) := ⟨box⟩

instance : Dia (Formula α) := ⟨dia⟩

instance : ŁukasiewiczAbbrev (Formula α) where
  neg := rfl
  top := rfl
  or := rfl
  and := rfl

@[simp, grind =] lemma imp_inj {A₁ A₂ B₁ B₂ : Formula α} : A₁ 🡒 A₂ = B₁ 🡒 B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ :=
  Iff.of_eq <| imp.injEq _ _ _ _

@[simp, grind =] lemma box_inj : □A = □B ↔ A = B := Iff.of_eq <| box.injEq _ _

@[elab_as_elim, induction_eliminator]
def rec' {C : Formula α → Sort*}
    (atom : ∀ a, C (#a))
    (falsum : C ⊥)
    (imp : ∀ A B, C A → C B → C (A 🡒 B))
    (box : ∀ A, C A → C (□A)) :
    (A : Formula α) → C A
  | #a    => atom a
  | .falsum => falsum
  | .imp A B => imp A B (rec' atom falsum imp box A) (rec' atom falsum imp box B)
  | .box A => box A (rec' atom falsum imp box A)

@[elab_as_elim, cases_eliminator]
def cases' {C : Formula α → Sort*}
    (atom : ∀ a, C (#a))
    (falsum : C ⊥)
    (imp : ∀ A B, C (A 🡒 B))
    (box : ∀ A, C (□A)) :
    (A : Formula α) → C A
  | #a    => atom a
  | .falsum => falsum
  | .imp A B => imp A B
  | .box A => box A

/-- `□^[n]A` is `A` prefixed with `n` boxes. -/
def boxItr (n : ℕ) (A : Formula α) : Formula α := (□·)^[n] A

@[inherit_doc] notation:76 "□^[" n "]" A:80 => boxItr n A

@[simp, grind =] lemma boxItr_zero : □^[0]A = A := rfl

@[simp, grind =] lemma boxItr_succ {n : ℕ} : □^[n + 1]A = □(□^[n]A) := Function.iterate_succ_apply' _ _ _

@[grind]
def complexity : Formula α → ℕ
  | #_      => 0
  | ⊥       => 0
  | A 🡒 B   => max A.complexity B.complexity + 1
  | □A      => A.complexity + 1

@[simp, grind =]
lemma complexity_imp : (A 🡒 B).complexity = max A.complexity B.complexity + 1 := rfl

variable [DecidableEq α]

@[grind]
def subfmls : Formula α → FormulaFinset α
  | #a    => {#a}
  | ⊥     => {⊥}
  | A 🡒 B => insert (A 🡒 B) (A.subfmls ∪ B.subfmls)
  | □A    => insert (□A) A.subfmls

@[simp, grind .]
lemma mem_subfmls_self : A ∈ A.subfmls := by cases A <;> simp [subfmls];

@[grind .]
lemma mem_subfmls_imp_left : A ∈ (A 🡒 B).subfmls := by simp [subfmls];

@[grind .]
lemma mem_subfmls_imp_right : B ∈ (A 🡒 B).subfmls := by simp [subfmls];

@[grind .]
lemma mem_subfmls_box : A ∈ (□A).subfmls := by simp [subfmls];

@[grind →]
lemma subfmls_trans : A ∈ B.subfmls → A.subfmls ⊆ B.subfmls := by
  induction B with
  | imp C D ihC ihD =>
    intro h;
    simp only [subfmls, Finset.mem_insert, Finset.mem_union] at h;
    rcases h with rfl | h | h;
    . rfl;
    . exact (ihC h).trans (by intro; simp [subfmls]; tauto);
    . exact (ihD h).trans (by intro; simp [subfmls]; tauto);
  | box C ih =>
    intro h;
    simp only [subfmls, Finset.mem_insert] at h;
    rcases h with rfl | h;
    . rfl;
    . exact (ih h).trans (by intro; simp [subfmls]; tauto);
  | _ => intro h; simp_all [subfmls];

end Formula

namespace FormulaFinset

variable {α : Type*} [DecidableEq α] {Γ Δ : FormulaFinset α} {A B C : Formula α}

/-- `□Γ` is the image of `Γ` under `□`. -/
abbrev box (Γ : FormulaFinset α) : FormulaFinset α := Γ.image (□·)

@[grind]
def subfmls (Γ : FormulaFinset α) : FormulaFinset α := Γ.biUnion Formula.subfmls

@[grind .] lemma subset_subfmls : Γ ⊆ Γ.subfmls := by
  intro A hA;
  simpa [subfmls] using ⟨A, hA, Formula.mem_subfmls_self⟩;

@[grind →]
lemma mem_subfmls_subfmls (hB : B ∈ Γ.subfmls) (hC : C ∈ B.subfmls) : C ∈ Γ.subfmls := by
  simp only [subfmls, Finset.mem_biUnion] at hB ⊢;
  obtain ⟨D, hD, hBD⟩ := hB;
  exact ⟨D, hD, Formula.subfmls_trans hBD hC⟩;

/-- `Γ.prebox` is the set of formulas `A` with `□A ∈ Γ`. -/
noncomputable def prebox (Γ : FormulaFinset α) : FormulaFinset α :=
  Γ.preimage (□·) (by intro _ _ _ _ h; simpa using h)

omit [DecidableEq α] in
@[simp, grind =]
lemma mem_prebox : A ∈ Γ.prebox ↔ □A ∈ Γ := by simp [prebox]

@[grind .]
lemma box_prebox_subset : Γ.prebox.box ⊆ Γ := by
  intro A;
  simp only [Finset.mem_image, mem_prebox];
  rintro ⟨B, hB, rfl⟩;
  exact hB;

end FormulaFinset

end FFL.ProvabilityLogic

end
