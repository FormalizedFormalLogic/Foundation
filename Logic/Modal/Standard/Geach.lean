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

variable {Ax : AxiomSet α}

open System

namespace AxiomSet

abbrev Geach (l : Axioms.Geach.Taple) : AxiomSet α := { Axioms.Geach l p | (p) }
notation:max "𝗴𝗲(" t ")" => AxiomSet.Geach t

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


def MultiGeach : List Axioms.Geach.Taple → AxiomSet α
  | [] => 𝗞
  | x :: xs => (AxiomSet.Geach x) ∪ (AxiomSet.MultiGeach xs)
notation:max "𝗚𝗲(" l ")" => AxiomSet.MultiGeach l

namespace MultiGeach

@[simp]
lemma def_nil : 𝗚𝗲([]) = (𝗞 : AxiomSet α) := by simp [MultiGeach]

@[simp]
lemma iff_cons : 𝗚𝗲(x :: l) = (𝗴𝗲(x) : AxiomSet α) ∪ 𝗚𝗲(l) := by simp only [MultiGeach];

@[simp]
lemma subsetK : (𝗞 : AxiomSet α) ⊆ 𝗚𝗲(l) := by
  induction l with
  | nil => simp;
  | cons => simp; apply Set.subset_union_of_subset_right (by assumption);

lemma subsetK' (h : 𝗚𝗲(l) ⊆ Ax): 𝗞 ⊆ Ax := Set.Subset.trans subsetK h

-- instance instK : System.K (𝐆𝐞(l) : AxiomSet α) := K_of_subset_K (by simp)

end MultiGeach

end AxiomSet


namespace DeductionParameter

protected abbrev Geach (l : List Axioms.Geach.Taple) : DeductionParameter α where
  axiomSet := 𝗚𝗲(l)
  nec := true
notation "𝐆𝐞(" l ")" => DeductionParameter.Geach l
instance instNormal : Normal (α := α) 𝐆𝐞(l) where
  include_K := by simp [AxiomSet.MultiGeach.subsetK]

protected class IsGeach (L : DeductionParameter α) where
  taples : List Axioms.Geach.Taple
  char : L = 𝐆𝐞(taples) := by aesop;

namespace IsGeach

variable {L : DeductionParameter α} [geach : L.IsGeach]

instance : L.Normal := by
  rw [geach.char];
  infer_instance

@[simp]
lemma eq_axiomset : Ax(L) = 𝗚𝗲(IsGeach.taples L) := by have := geach.char; simp_all;

instance : DeductionParameter.IsGeach (α := α) 𝐊 where taples := [];

instance : DeductionParameter.IsGeach (α := α) 𝐊𝐃 where taples := [⟨0, 0, 1, 1⟩]

instance : DeductionParameter.IsGeach (α := α) 𝐊𝐓 where taples := [⟨0, 0, 1, 0⟩]

instance : DeductionParameter.IsGeach (α := α) 𝐒𝟒 where taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩]

instance : DeductionParameter.IsGeach (α := α) 𝐒𝟒.𝟐 where taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩]

instance : DeductionParameter.IsGeach (α := α) 𝐒𝟓 where taples := [⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩]

instance : DeductionParameter.IsGeach (α := α) 𝐊𝐓𝟒𝐁 where taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩]

end IsGeach

end DeductionParameter

end LO.Modal.Standard
