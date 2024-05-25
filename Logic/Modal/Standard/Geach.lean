import Logic.Modal.Standard.System
import Logic.Modal.Standard.Formula
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

variable {Λ : AxiomSet α}

open System

namespace AxiomSet

def Geach (l : Axioms.Geach.Taple) : AxiomSet α := { Axioms.Geach l p | (p) }
notation:max "𝐠𝐞(" t ")" => AxiomSet.Geach t

namespace Geach

@[simp] lemma def_axiomT : (𝐓 : AxiomSet α) = AxiomSet.Geach ⟨0, 0, 1, 0⟩ := by aesop;

@[simp] lemma def_axiomB : (𝐁 : AxiomSet α) = AxiomSet.Geach ⟨0, 1, 0, 1⟩ := by aesop;

@[simp] lemma def_axiomD : (𝐃 : AxiomSet α) = AxiomSet.Geach ⟨0, 0, 1, 1⟩ := by aesop;

@[simp] lemma def_axiomFour : (𝟒 : AxiomSet α) = AxiomSet.Geach ⟨0, 2, 1, 0⟩ := by aesop;

@[simp] lemma def_axiom5 : (𝟓 : AxiomSet α) = AxiomSet.Geach ⟨1, 1, 0, 1⟩ := by aesop;

@[simp] lemma def_axiomDot2 : (.𝟐 : AxiomSet α) = AxiomSet.Geach ⟨1, 1, 1, 1⟩ := by aesop;

@[simp] lemma def_axiomC4 : (𝐂𝟒 : AxiomSet α) = AxiomSet.Geach ⟨0, 1, 2, 0⟩ := by aesop;

@[simp] lemma def_axiomCD : (𝐂𝐃 : AxiomSet α) = AxiomSet.Geach ⟨1, 1, 0, 0⟩ := by aesop;

end Geach


@[simp]
def GeachLogic : List Axioms.Geach.Taple → AxiomSet α
  | [] => 𝐊
  | x :: xs => (AxiomSet.Geach x) ∪ (AxiomSet.GeachLogic xs)
notation:max "𝐆𝐞(" l ")" => AxiomSet.GeachLogic l

@[simp]
lemma GeachLogic.subsetK {l : List Axioms.Geach.Taple} : (𝐊 : AxiomSet α) ⊆ (AxiomSet.GeachLogic l) := by
  induction l with
  | nil => simp;
  | cons => simp; apply Set.subset_union_of_subset_right (by assumption);

lemma GeachLogic.subsetK' (h : (AxiomSet.GeachLogic l) ⊆ Λ): (𝐊 : AxiomSet α) ⊆ Λ := Set.Subset.trans GeachLogic.subsetK h

instance instKofGeachLogic : System.K (𝐆𝐞(l) : AxiomSet α) := K_of_subset_K (by simp)

class IsGeach (Λ : AxiomSet α) where
  taples : List Axioms.Geach.Taple
  char : Λ = AxiomSet.GeachLogic taples

instance [Λ.IsGeach] : System.K Λ := by rw [IsGeach.char (Λ := Λ)]; exact instKofGeachLogic;

@[simp]
instance : IsGeach (𝐊 : AxiomSet α) where
  taples := [];
  char := rfl

@[simp]
instance : IsGeach (𝐊𝐃 : AxiomSet α) where
  taples := [⟨0, 0, 1, 1⟩];
  char := by simp [AxiomSet.KD]; aesop;

@[simp]
instance : IsGeach (𝐊𝐓 : AxiomSet α) where
  taples := [⟨0, 0, 1, 0⟩];
  char := by simp [AxiomSet.KT]; aesop;

@[simp]
instance : IsGeach (𝐊𝟒 : AxiomSet α) where
  taples := [⟨0, 2, 1, 0⟩];
  char := by simp [AxiomSet.K4]; aesop;

@[simp]
instance : IsGeach (𝐒𝟒 : AxiomSet α) where
  taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩];
  char := by simp [AxiomSet.S4]; aesop;

@[simp]
instance : IsGeach (𝐒𝟒.𝟐 : AxiomSet α) where
  taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩];
  char := by simp [AxiomSet.S4Dot2, AxiomSet.S4]; aesop;

@[simp]
instance : IsGeach (𝐒𝟓 : AxiomSet α) where
  taples := [⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩];
  char := by simp [AxiomSet.S5]; aesop;

@[simp]
instance : IsGeach (𝐊𝐓𝟒𝐁 : AxiomSet α) where
  taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩];
  char := by simp [AxiomSet.KT4B]; aesop;

end AxiomSet


end LO.Modal.Standard
