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

class IsGeachAxiom (Λ : AxiomSet α) where
  taple : Axioms.Geach.Taple
  char : Λ = AxiomSet.Geach taple := by rfl

@[simp] instance : IsGeachAxiom (𝐓 : AxiomSet α) where taple := ⟨0, 0, 1, 0⟩;

@[simp] instance : IsGeachAxiom (𝐁 : AxiomSet α) where taple := ⟨0, 1, 0, 1⟩;

@[simp] instance : IsGeachAxiom (𝐃 : AxiomSet α) where taple := ⟨0, 0, 1, 1⟩;

@[simp] instance : IsGeachAxiom (𝟒 : AxiomSet α) where taple := ⟨0, 2, 1, 0⟩;

@[simp] instance : IsGeachAxiom (𝟓 : AxiomSet α) where taple := ⟨1, 1, 0, 1⟩;

@[simp] instance : IsGeachAxiom (.𝟐 : AxiomSet α) where taple := ⟨1, 1, 1, 1⟩;

@[simp] instance : IsGeachAxiom (𝐂𝟒 : AxiomSet α) where taple := ⟨0, 1, 2, 0⟩;

@[simp] instance : IsGeachAxiom (𝐂𝐃 : AxiomSet α) where taple := ⟨1, 1, 0, 0⟩;

@[simp]
def GeachLogic : List Axioms.Geach.Taple → AxiomSet α
  | [] => 𝐊
  | x :: xs => (AxiomSet.GeachLogic xs) ∪ (AxiomSet.Geach x)
notation:max "𝐆𝐞(" l ")" => AxiomSet.GeachLogic l

namespace GeachLogic

@[simp]
lemma subsetK : (𝐊 : AxiomSet α) ⊆ 𝐆𝐞(l) := by
  induction l with
  | nil => simp;
  | cons => simp; apply Set.subset_union_of_subset_left (by assumption);

lemma subsetK' (h : 𝐆𝐞(l) ⊆ Λ): 𝐊 ⊆ Λ := Set.Subset.trans GeachLogic.subsetK h

instance instK : System.K (𝐆𝐞(l) : AxiomSet α) := K_of_subset_K (by simp)

end GeachLogic

class IsGeachLogic (Λ : AxiomSet α) where
  taples : List Axioms.Geach.Taple
  char : Λ = 𝐆𝐞(taples) := by simp; rfl;

instance [Λ.IsGeachLogic] : System.K Λ := by rw [IsGeachLogic.char (Λ := Λ)]; exact GeachLogic.instK;

@[simp] instance : IsGeachLogic (𝐊 : AxiomSet α) where
  taples := [];
  char := by simp;

@[simp] instance : IsGeachLogic (𝐊𝐃 : AxiomSet α) where taples := [⟨0, 0, 1, 1⟩]

@[simp] instance : IsGeachLogic (𝐊𝐓 : AxiomSet α) where taples := [⟨0, 0, 1, 0⟩]

@[simp] instance : IsGeachLogic (𝐊𝟒 : AxiomSet α) where taples := [⟨0, 2, 1, 0⟩]

@[simp] instance : IsGeachLogic (𝐒𝟒 : AxiomSet α) where taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩].reverse

@[simp] instance : IsGeachLogic (𝐒𝟒.𝟐 : AxiomSet α) where taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩].reverse

@[simp] instance : IsGeachLogic (𝐒𝟓 : AxiomSet α) where taples := [⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩].reverse

@[simp] instance : IsGeachLogic (𝐊𝐓𝟒𝐁 : AxiomSet α) where taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩].reverse

end AxiomSet


end LO.Modal.Standard
