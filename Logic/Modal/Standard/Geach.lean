import Logic.Modal.Standard.Deduction
import Logic.Logic.Kripke.RelItr
import Logic.Vorspiel.BinaryRelations

structure GeachTaple where
  i : ℕ
  j : ℕ
  m : ℕ
  n : ℕ

def GeachConfluent (t : GeachTaple) (R : Rel α α) := ∀ {x y z : α}, (R.iterate t.i x y) ∧ (R.iterate t.j x z) → ∃ u, (R.iterate t.m y u) ∧ (R.iterate t.n z u)

namespace GeachConfluent

variable {R : Rel α α}

 lemma serial_def : Serial R ↔ (GeachConfluent ⟨0, 0, 1, 1⟩ R) := by simp [GeachConfluent, Serial];

lemma reflexive_def : Reflexive R ↔ (GeachConfluent ⟨0, 0, 1, 0⟩ R) := by simp [GeachConfluent, Reflexive];

lemma symmetric_def : Symmetric R ↔ (GeachConfluent ⟨0, 1, 0, 1⟩ R) := by
  simp [GeachConfluent, Symmetric];
  constructor;
  . rintro h x y z rfl Rxz; exact h Rxz;
  . intro h x y Rxy; exact h rfl Rxy;

lemma transitive_def : Transitive R ↔ (GeachConfluent ⟨0, 2, 1, 0⟩ R) := by
  simp [GeachConfluent, Transitive];
  constructor;
  . rintro h x y z rfl w Rxw Rwz; exact h Rxw Rwz;
  . intro h x y z Rxy Ryz; exact h rfl y Rxy Ryz

lemma euclidean_def : Euclidean R ↔ (GeachConfluent ⟨1, 1, 0, 1⟩ R) := by simp [GeachConfluent, Euclidean];

lemma confluent_def : Confluent R ↔ (GeachConfluent ⟨1, 1, 1, 1⟩ R) := by simp [GeachConfluent, Confluent];

lemma extensive_def : Extensive R ↔ (GeachConfluent ⟨0, 1, 0, 0⟩ R) := by
  simp [GeachConfluent, Extensive];
  constructor;
  . rintro h x y z rfl Rxz; have := h Rxz; tauto;
  . intro h x y Rxy; have := h rfl Rxy; tauto;

lemma functional_def : Functional R ↔ (GeachConfluent ⟨1, 1, 0, 0⟩ R) := by
  simp [GeachConfluent, Functional];
  constructor <;> tauto;

lemma dense_def : Dense R ↔ (GeachConfluent ⟨0, 1, 2, 0⟩ R) := by
  simp [GeachConfluent, Dense];
  constructor;
  . rintro h x y z rfl Rxz; exact h Rxz;
  . intro h x y Rxy; exact h rfl Rxy;

@[simp]
lemma satisfies_eq : GeachConfluent (α := α) t (· = ·) := by simp [GeachConfluent];

end GeachConfluent


def MultiGeachConfluent (ts : List GeachTaple) (R : Rel α α) : Prop :=
  match ts with
  | [] => True
  | [t] => (GeachConfluent t R)
  | t :: ts => (GeachConfluent t R) ∧ (MultiGeachConfluent ts R)

namespace MultiGeachConfluent

@[simp] lemma iff_nil : MultiGeachConfluent [] R := by simp [MultiGeachConfluent];

@[simp] lemma iff_singleton : MultiGeachConfluent [t] R ↔ (GeachConfluent t R) := by simp [MultiGeachConfluent];

lemma iff_cons (h : ts ≠ []) : MultiGeachConfluent (t :: ts) R ↔ (GeachConfluent t R) ∧ (MultiGeachConfluent ts R) := by simp [MultiGeachConfluent];

@[simp]
lemma satisfies_eq : MultiGeachConfluent (α := α) ts (· = ·) := by induction ts using List.induction_with_singleton <;> simp_all [MultiGeachConfluent];

end MultiGeachConfluent



namespace LO.System.Axioms

variable {F : Type*} [LogicalConnective F] [BasicModalLogicalConnective F]

abbrev Geach (l : GeachTaple) (p : F) := ◇^[l.i](□^[l.m]p) ⟶ □^[l.j](◇^[l.n]p)

end LO.System.Axioms


namespace LO.Modal.Standard

variable {Ax : AxiomSet α}

open System

namespace AxiomSet

abbrev Geach (l : GeachTaple) : AxiomSet α := { Axioms.Geach l p | (p) }
notation:max "𝗴𝗲(" t ")" => AxiomSet.Geach t

namespace Geach

lemma T_def : 𝗴𝗲(⟨0, 0, 1, 0⟩) = (𝗧 : AxiomSet α) := by aesop;

lemma B_def : 𝗴𝗲(⟨0, 1, 0, 1⟩) = (𝗕 : AxiomSet α) := by aesop;

lemma D_def : 𝗴𝗲(⟨0, 0, 1, 1⟩) = (𝗗 : AxiomSet α) := by aesop;

lemma Four_def : 𝗴𝗲(⟨0, 2, 1, 0⟩) = (𝟰 : AxiomSet α) := by aesop;

lemma Five_def : 𝗴𝗲(⟨1, 1, 0, 1⟩) = (𝟱 : AxiomSet α) := by aesop;

lemma Dot2_def : 𝗴𝗲(⟨1, 1, 1, 1⟩) = (.𝟮 : AxiomSet α) := by aesop;

lemma C4_def : 𝗴𝗲(⟨0, 1, 2, 0⟩) = (𝗖𝟰 : AxiomSet α) := by aesop;

lemma CD_def : 𝗴𝗲(⟨1, 1, 0, 0⟩) = (𝗖𝗗 : AxiomSet α) := by aesop;

lemma Tc_def : 𝗴𝗲(⟨0, 1, 0, 0⟩) = (𝗧𝗰 : AxiomSet α) := rfl

end Geach

class IsGeach (Ax : AxiomSet α) where
  taple : GeachTaple
  char : Ax = AxiomSet.Geach taple := by rfl

instance : IsGeach (α := α) 𝗧 where taple := ⟨0, 0, 1, 0⟩;

instance : IsGeach (α := α) 𝗕 where taple := ⟨0, 1, 0, 1⟩;

instance : IsGeach (α := α) 𝗗 where taple := ⟨0, 0, 1, 1⟩;

instance : IsGeach (α := α) 𝟰 where taple := ⟨0, 2, 1, 0⟩;

instance : IsGeach (α := α) 𝟱 where taple := ⟨1, 1, 0, 1⟩;

instance : IsGeach (α := α) .𝟮 where taple := ⟨1, 1, 1, 1⟩;

instance : IsGeach (α := α) 𝗖𝟰 where taple := ⟨0, 1, 2, 0⟩;

instance : IsGeach (α := α) 𝗖𝗗 where taple := ⟨1, 1, 0, 0⟩;

instance : IsGeach (α := α) 𝗧𝗰 where taple := ⟨0, 1, 0, 0⟩;


def MultiGeach : List GeachTaple → AxiomSet α
  | [] => ∅
  | x :: xs => (AxiomSet.Geach x) ∪ (AxiomSet.MultiGeach xs)
notation:max "𝗚𝗲(" l ")" => AxiomSet.MultiGeach l

namespace MultiGeach

@[simp]
lemma def_nil : 𝗚𝗲([]) = (∅ : AxiomSet α) := by simp [MultiGeach]

@[simp]
lemma iff_cons : 𝗚𝗲(x :: l) = (𝗴𝗲(x) : AxiomSet α) ∪ 𝗚𝗲(l) := by simp only [MultiGeach];

lemma mem (h : x ∈ l) : (𝗴𝗲(x) : AxiomSet α) ⊆ 𝗚𝗲(l) := by
  induction l with
  | nil => contradiction;
  | cons a as ih =>
    simp_all;
    cases h;
    . subst_vars; tauto;
    . apply Set.subset_union_of_subset_right $ ih (by assumption);

/-
@[simp]
lemma subset_K {l : List Axioms.Geach.Taple} : (𝗞 : AxiomSet α) ⊆ 𝗚𝗲(l) := by
  induction l with
  | nil => simp;
  | cons a as ih => apply Set.subset_union_of_subset_right ih;
-/

/-
@[simp]
lemma subset (h : l₁ ⊆ l₂) : (𝗚𝗲(l₁) : AxiomSet α) ⊆ 𝗚𝗲(l₂) := by
  induction l₁ generalizing l₂ <;> induction l₂;
  case nil.nil | cons.nil | nil.cons => simp_all;
  case cons.cons a as iha b bs ihb =>
    simp_all;
    constructor;
    . cases h.1;
      . subst_vars; tauto;
      . apply Set.subset_union_of_subset_right $ mem (by assumption);
    . simpa using (iha h.2);
-/

end MultiGeach

end AxiomSet


namespace DeductionParameter

protected abbrev Geach (l : List GeachTaple) : DeductionParameter α := 𝝂(𝗚𝗲(l))
notation "𝐆𝐞(" l ")" => DeductionParameter.Geach l

namespace Geach

end Geach

protected class IsGeach (L : DeductionParameter α) (taples : List GeachTaple) where
  char : L = 𝐆𝐞(taples) := by aesop;

attribute [simp] IsGeach.char

namespace IsGeach

lemma ax {Λ : DeductionParameter α} [geach : Λ.IsGeach ts] : Ax(Λ) = (𝗞 ∪ 𝗚𝗲(ts)) := by
  have e := geach.char;
  simp [DeductionParameter.Geach] at e;
  simp_all;

/-
instance {L : DeductionParameter α} [geach : L.IsGeach] : L.IsNormal := by
  rw [geach.char];
  infer_instance;
-/

instance : 𝐊.IsGeach (α := α) [] where

instance : 𝐊𝐃.IsGeach (α := α) [⟨0, 0, 1, 1⟩] where

instance : 𝐊𝐓.IsGeach (α := α) [⟨0, 0, 1, 0⟩] where

instance : 𝐊𝐓𝐁.IsGeach (α := α) [⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩] where

instance : 𝐊𝟒.IsGeach (α := α) [⟨0, 2, 1, 0⟩] where

instance : 𝐒𝟒.IsGeach (α := α) [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩] where

instance : 𝐒𝟒.𝟐.IsGeach (α := α) [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩] where

instance : 𝐒𝟓.IsGeach (α := α) [⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩] where

instance : 𝐊𝐓𝟒𝐁.IsGeach (α := α) [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩] where

instance : 𝐓𝐫𝐢𝐯.IsGeach (α := α) [⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩] where

end IsGeach

end DeductionParameter

end LO.Modal.Standard
