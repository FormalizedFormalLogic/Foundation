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

abbrev Geach (l : Axioms.Geach.Taple) : AxiomSet α := { Axioms.Geach l p | (p) }
notation:max "𝐠𝐞(" t ")" => AxiomSet.Geach t

class IsGeach (Λ : AxiomSet α) where
  taple : Axioms.Geach.Taple
  char : Λ = AxiomSet.Geach taple := by rfl

instance : IsGeach (α := α) 𝐓 where taple := ⟨0, 0, 1, 0⟩;

instance : IsGeach (α := α) 𝐁 where taple := ⟨0, 1, 0, 1⟩;

instance : IsGeach (α := α) 𝐃 where taple := ⟨0, 0, 1, 1⟩;

instance : IsGeach (α := α) 𝟒 where taple := ⟨0, 2, 1, 0⟩;

instance : IsGeach (α := α) 𝟓 where taple := ⟨1, 1, 0, 1⟩;

instance : IsGeach (α := α) .𝟐 where taple := ⟨1, 1, 1, 1⟩;

instance : IsGeach (α := α) 𝐂𝟒 where taple := ⟨0, 1, 2, 0⟩;

instance : IsGeach (α := α) 𝐂𝐃 where taple := ⟨1, 1, 0, 0⟩;


def GeachLogic : List Axioms.Geach.Taple → AxiomSet α
  | [] => 𝐊
  | x :: xs => (AxiomSet.Geach x) ∪ (AxiomSet.GeachLogic xs)
notation:max "𝐆𝐞(" l ")" => AxiomSet.GeachLogic l

namespace GeachLogic

@[simp]
lemma def_nil : 𝐆𝐞([]) = (𝐊 : AxiomSet α) := by simp [GeachLogic]

@[simp]
lemma iff_cons : 𝐆𝐞(x :: l) = (𝐠𝐞(x) : AxiomSet α) ∪ 𝐆𝐞(l) := by simp only [GeachLogic];

@[simp]
lemma subsetK : (𝐊 : AxiomSet α) ⊆ 𝐆𝐞(l) := by
  induction l with
  | nil => simp;
  | cons => simp; apply Set.subset_union_of_subset_right (by assumption);

lemma subsetK' (h : 𝐆𝐞(l) ⊆ Λ): 𝐊 ⊆ Λ := Set.Subset.trans GeachLogic.subsetK h

instance instK : System.K (𝐆𝐞(l) : AxiomSet α) := K_of_subset_K (by simp)

end GeachLogic

class IsGeachLogic (Λ : AxiomSet α) where
  taples : List Axioms.Geach.Taple
  char : Λ = 𝐆𝐞(taples) := by aesop;

instance [Λ.IsGeachLogic] : System.K Λ := by rw [IsGeachLogic.char (Λ := Λ)]; exact GeachLogic.instK;

instance : IsGeachLogic (α := α) 𝐊 where taples := [];

instance : IsGeachLogic (α := α) 𝐊𝐃 where taples := [⟨0, 0, 1, 1⟩]

instance : IsGeachLogic (α := α) 𝐊𝐓 where taples := [⟨0, 0, 1, 0⟩]

instance : IsGeachLogic (α := α) 𝐊𝟒 where taples := [⟨0, 2, 1, 0⟩]

instance : IsGeachLogic (α := α) 𝐒𝟒 where taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩]

instance : IsGeachLogic (α := α) 𝐒𝟒.𝟐 where taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩]

instance : IsGeachLogic (α := α) 𝐒𝟓 where taples := [⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩]

instance : IsGeachLogic (α := α) 𝐊𝐓𝟒𝐁 where taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩]

end AxiomSet


end LO.Modal.Standard
