import Logic.Modal.Standard.Deduction

namespace LO.System.Axioms

variable {F : Type*} [LogicalConnective F] [StandardModalLogicalConnective F]

structure Geach.Taple where
  i : ℕ
  j : ℕ
  m : ℕ
  n : ℕ

abbrev Geach (l : Geach.Taple) (p : F) := ◇^[l.i](□^[l.m]p) ⟶ □^[l.j](◇^[l.n]p)

end LO.System.Axioms

namespace LO.Modal.Standard

variable {Ax : AxiomSet α}

open System

namespace AxiomSet

abbrev Geach (l : Axioms.Geach.Taple) : AxiomSet α := { Axioms.Geach l p | (p) }
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
  taple : Axioms.Geach.Taple
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


def MultiGeach : List Axioms.Geach.Taple → AxiomSet α
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

protected abbrev Geach (l : List Axioms.Geach.Taple) : DeductionParameter α := 𝝂(𝗚𝗲(l))
notation "𝐆𝐞(" l ")" => DeductionParameter.Geach l

namespace Geach

end Geach

protected class IsGeach (L : DeductionParameter α) where
  taples : List Axioms.Geach.Taple
  char : L = 𝐆𝐞(taples) := by aesop;

namespace IsGeach

lemma ax {Λ : DeductionParameter α} [geach : Λ.IsGeach] : Ax(Λ) = (𝗞 ∪ 𝗚𝗲(geach.taples)) := by
  have e := geach.char;
  simp [DeductionParameter.Geach] at e;
  simp_all;

instance {L : DeductionParameter α} [geach : L.IsGeach] : L.IsNormal := by
  rw [geach.char];
  infer_instance;

instance : 𝐊.IsGeach (α := α) where taples := [];

instance : 𝐊𝐃.IsGeach (α := α) where taples := [⟨0, 0, 1, 1⟩]

instance : 𝐊𝐓.IsGeach (α := α) where taples := [⟨0, 0, 1, 0⟩]

instance : 𝐊𝐓𝐁.IsGeach (α := α) where taples := [⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩]

instance : 𝐒𝟒.IsGeach (α := α) where taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩]

instance : 𝐒𝟒.𝟐.IsGeach (α := α) where taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩]

instance : 𝐒𝟓.IsGeach (α := α) where taples := [⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩]

instance : 𝐊𝐓𝟒𝐁.IsGeach (α := α) where taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩]

instance : 𝐓𝐫𝐢𝐯.IsGeach (α := α) where taples := [⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩]

end IsGeach

end DeductionParameter

end LO.Modal.Standard
