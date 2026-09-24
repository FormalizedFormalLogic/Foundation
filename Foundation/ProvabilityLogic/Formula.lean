module

public import Foundation.Logic.LogicSymbol
public import Mathlib.Data.Finset.Preimage

/-!
# Modal formulas
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

def boxItr (n : ℕ) (A : Formula α) : Formula α := (□·)^[n] A

notation:76 "□^[" n "]" A:80 => boxItr n A

@[simp, grind =] lemma boxItr_zero : □^[0]A = A := rfl

@[simp, grind =] lemma boxItr_succ {n : ℕ} : □^[n + 1]A = □(□^[n]A) := Function.iterate_succ_apply' _ _ _

abbrev boxdot (A : Formula α) : Formula α := A ⋏ □A

prefix:76 "⊡" => boxdot

def boxdotTranslate : Formula α → Formula α
  | #a    => #a
  | ⊥     => ⊥
  | A 🡒 B => A.boxdotTranslate 🡒 B.boxdotTranslate
  | □A    => ⊡A.boxdotTranslate

postfix:90 "ᵇ" => boxdotTranslate

@[simp, grind =] lemma boxdotTranslate_atom {a : α} : (#a)ᵇ = #a := rfl
@[simp, grind =] lemma boxdotTranslate_bot : (⊥ : Formula α)ᵇ = ⊥ := rfl
@[simp, grind =] lemma boxdotTranslate_top : (⊤ : Formula α)ᵇ = ⊤ := rfl
@[simp, grind =] lemma boxdotTranslate_imp : (A 🡒 B)ᵇ = Aᵇ 🡒 Bᵇ := rfl
@[simp, grind =] lemma boxdotTranslate_neg : (∼A)ᵇ = ∼Aᵇ := rfl
@[simp, grind =] lemma boxdotTranslate_and : (A ⋏ B)ᵇ = Aᵇ ⋏ Bᵇ := rfl
@[simp, grind =] lemma boxdotTranslate_or : (A ⋎ B)ᵇ = Aᵇ ⋎ Bᵇ := rfl
@[simp, grind =] lemma boxdotTranslate_box : (□A)ᵇ = ⊡Aᵇ := rfl

@[grind]
def complexity : Formula α → ℕ
  | #_      => 0
  | ⊥       => 0
  | A 🡒 B   => max A.complexity B.complexity + 1
  | □A      => A.complexity + 1

@[simp, grind =]
lemma complexity_imp : (A 🡒 B).complexity = max A.complexity B.complexity + 1 := rfl

@[grind]
def ModalizedIn (p : α) : Formula α → Prop
  | #a    => a ≠ p
  | ⊥     => True
  | A 🡒 B => A.ModalizedIn p ∧ B.ModalizedIn p
  | □_    => True

@[simp, grind =]
lemma complexity_box : (□A).complexity = A.complexity + 1 := rfl

variable [DecidableEq α]

@[grind]
def atoms : Formula α → Finset α
  | #a    => {a}
  | ⊥     => ∅
  | A 🡒 B => A.atoms ∪ B.atoms
  | □A    => A.atoms

@[simp, grind =] lemma atoms_atom {a : α} : (#a : Formula α).atoms = {a} := rfl
@[simp, grind =] lemma atoms_bot : (⊥ : Formula α).atoms = ∅ := rfl
@[simp, grind =] lemma atoms_imp : (A 🡒 B).atoms = A.atoms ∪ B.atoms := rfl
@[simp, grind =] lemma atoms_neg : (∼A).atoms = A.atoms := Finset.union_empty _
@[simp, grind =] lemma atoms_or : (A ⋎ B).atoms = A.atoms ∪ B.atoms := by simp [atoms]
@[simp, grind =] lemma atoms_iff : (A 🡘 B).atoms = A.atoms ∪ B.atoms := by
  simp [atoms, Finset.union_comm];
@[simp, grind =] lemma atoms_box : (□A).atoms = A.atoms := rfl

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

abbrev box (Γ : FormulaFinset α) : FormulaFinset α := Γ.image (□·)

@[simp, grind =]
lemma box_insert : (insert A Γ).box = insert (□A) Γ.box := Finset.image_insert _ _ _

def atoms (Γ : FormulaFinset α) : Finset α := Γ.biUnion Formula.atoms

@[simp, grind =] lemma atoms_empty : (∅ : FormulaFinset α).atoms = ∅ := rfl

@[simp, grind =]
lemma atoms_insert : (insert A Γ).atoms = A.atoms ∪ Γ.atoms := Finset.biUnion_insert

@[simp, grind =]
lemma atoms_singleton : ({A} : FormulaFinset α).atoms = A.atoms := Finset.singleton_biUnion

@[simp, grind =]
lemma atoms_union : (Γ ∪ Δ).atoms = Γ.atoms ∪ Δ.atoms := Finset.union_biUnion

@[simp, grind =] lemma atoms_box : Γ.box.atoms = Γ.atoms := Finset.image_biUnion

lemma atoms_subset_of_mem (h : A ∈ Γ) : A.atoms ⊆ Γ.atoms := Finset.subset_biUnion_of_mem _ h

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

noncomputable def prebox (Γ : FormulaFinset α) : FormulaFinset α :=
  Γ.preimage (□·) (by intro _ _ _ _ h; simpa using h)

omit [DecidableEq α] in
@[simp, grind =]
lemma mem_prebox : A ∈ Γ.prebox ↔ □A ∈ Γ := by simp [prebox]

lemma atoms_prebox : Γ.prebox.atoms ⊆ Γ.atoms := by
  intro a;
  simpa [atoms] using fun A hA ha ↦ ⟨□A, hA, ha⟩;

@[grind .]
lemma box_prebox_subset : Γ.prebox.box ⊆ Γ := by
  intro A;
  simp only [Finset.mem_image, mem_prebox];
  rintro ⟨B, hB, rfl⟩;
  exact hB;

end FormulaFinset

/-! ### Substitution -/

namespace Formula

variable {α β : Type*}

abbrev Substitution (α β : Type*) := α → Formula β

@[grind]
def subst (s : Substitution α β) : Formula α → Formula β
  | #a    => s a
  | ⊥     => ⊥
  | A 🡒 B => A.subst s 🡒 B.subst s
  | □A    => □(A.subst s)

scoped notation:80 A "⟦" s "⟧" => Formula.subst s A

variable {s : Substitution α β} {A B : Formula α}

@[simp, grind =] lemma subst_atom {a : α} : (#a)⟦s⟧ = s a := rfl
@[simp, grind =] lemma subst_bot : (⊥ : Formula α)⟦s⟧ = ⊥ := rfl
@[simp, grind =] lemma subst_top : (⊤ : Formula α)⟦s⟧ = ⊤ := rfl
@[simp, grind =] lemma subst_imp : (A 🡒 B)⟦s⟧ = A⟦s⟧ 🡒 B⟦s⟧ := rfl
@[simp, grind =] lemma subst_neg : (∼A)⟦s⟧ = ∼A⟦s⟧ := rfl
@[simp, grind =] lemma subst_and : (A ⋏ B)⟦s⟧ = A⟦s⟧ ⋏ B⟦s⟧ := rfl
@[simp, grind =] lemma subst_or : (A ⋎ B)⟦s⟧ = A⟦s⟧ ⋎ B⟦s⟧ := rfl
@[simp, grind =] lemma subst_box : (□A)⟦s⟧ = □A⟦s⟧ := rfl
@[simp, grind =] lemma subst_dia : (◇A)⟦s⟧ = ◇A⟦s⟧ := rfl

@[simp, grind =] lemma subst_iff : (A 🡘 B)⟦s⟧ = A⟦s⟧ 🡘 B⟦s⟧ := rfl

@[simp, grind =]
lemma subst_boxItr {n : ℕ} : (□^[n]A)⟦s⟧ = □^[n]A⟦s⟧ := by
  induction n <;> simp_all;

section single

variable [DecidableEq α] {p q : α} {B : Formula α}

def Substitution.single (p : α) (B : Formula α) : Substitution α α :=
  fun a ↦ if a = p then B else #a

scoped notation:80 A "⟦" p " ↦ " B "⟧" => Formula.subst (Substitution.single p B) A

@[simp, grind =]
lemma Substitution.single_apply {a : α} : Substitution.single p B a = if a = p then B else #a := rfl

@[simp, grind =]
lemma subst_single_self : A⟦p ↦ #p⟧ = A := by induction A <;> grind;

lemma subst_single_of_not_mem (h : p ∉ A.atoms) : A⟦p ↦ B⟧ = A := by induction A <;> grind;

lemma subst_single_subst_single (hq : q ∉ A.atoms) : (A⟦p ↦ #q⟧)⟦q ↦ B⟧ = A⟦p ↦ B⟧ := by
  induction A <;> grind;

lemma atoms_subst_single : (A⟦p ↦ B⟧).atoms ⊆ A.atoms.erase p ∪ B.atoms := by
  induction A <;> grind;

end single

end Formula

end FFL.ProvabilityLogic

end
