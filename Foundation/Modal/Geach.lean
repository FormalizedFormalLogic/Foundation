import Foundation.Modal.Hilbert
import Foundation.Vorspiel.Geach

namespace LO.Axioms

variable {F : Type*} [LogicalConnective F] [BasicModalLogicalConnective F]

protected abbrev Geach (t : GeachConfluent.Taple) (φ : F) := ◇^[t.i](□^[t.m]φ) ➝ □^[t.j](◇^[t.n]φ)
abbrev Geach.set (t : GeachConfluent.Taple) : Set F := { Axioms.Geach t φ | (φ) }
notation:max "𝗴𝗲(" t ")" => Geach.set t


section

lemma T.is_geach : (𝗧 : Set F) = 𝗴𝗲(⟨0, 0, 1, 0⟩) := rfl

lemma B.is_geach : (𝗕 : Set F) = 𝗴𝗲(⟨0, 1, 0, 1⟩) := rfl

lemma D.is_geach : (𝗗 : Set F) = 𝗴𝗲(⟨0, 0, 1, 1⟩) := rfl

lemma Four.is_geach : (𝟰 : Set F) = 𝗴𝗲(⟨0, 2, 1, 0⟩) := rfl

lemma Five.is_geach : (𝟱 : Set F) = 𝗴𝗲(⟨1, 1, 0, 1⟩) := rfl

lemma Dot2.is_geach : (.𝟮 : Set F) = 𝗴𝗲(⟨1, 1, 1, 1⟩) := rfl

lemma C4.is_geach : (𝗖𝟰 : Set F) = 𝗴𝗲(⟨0, 1, 2, 0⟩) := rfl

lemma CD.is_geach : (𝗖𝗗 : Set F) = 𝗴𝗲(⟨1, 1, 0, 0⟩) := rfl

lemma Tc.is_geach : (𝗧𝗰 : Set F) = 𝗴𝗲(⟨0, 1, 0, 0⟩) := rfl

end


def MultiGeach.set : List (GeachConfluent.Taple) → Set F
  | [] => ∅
  | t :: ts => 𝗴𝗲(t) ∪ (MultiGeach.set ts)
notation:max "𝗚𝗲(" ts ")" => MultiGeach.set ts

namespace MultiGeach

@[simp] lemma def_nil : 𝗚𝗲([]) = (∅ : Set F) := by simp [MultiGeach.set]

lemma def_one {t : GeachConfluent.Taple} : (𝗚𝗲([t]) : Set F) = 𝗴𝗲(t) := by simp [MultiGeach.set]

lemma def_two {t₁ t₂ : GeachConfluent.Taple} : (𝗚𝗲([t₁, t₂]) : Set F) = 𝗴𝗲(t₁) ∪ 𝗴𝗲(t₂) := by simp [MultiGeach.set]

lemma def_three {t₁ t₂ t₃ : GeachConfluent.Taple} : (𝗚𝗲([t₁, t₂, t₃]) : Set F) = 𝗴𝗲(t₁) ∪ 𝗴𝗲(t₂) ∪ 𝗴𝗲(t₃) := by simp [MultiGeach.set, Set.union_assoc];

@[simp] lemma iff_cons : 𝗚𝗲(x :: l) = (𝗴𝗲(x) : Set F) ∪ 𝗚𝗲(l) := by simp only [MultiGeach.set];

lemma mem (h : x ∈ l) : (𝗴𝗲(x) : Set F) ⊆ 𝗚𝗲(l) := by
  induction l with
  | nil => contradiction;
  | cons a as ih =>
    simp_all;
    cases h;
    . subst_vars; tauto;
    . apply Set.subset_union_of_subset_right $ ih (by assumption);

end MultiGeach

end LO.Axioms


namespace LO.Modal

variable {Ax : Theory α}

open System

protected abbrev Hilbert.Geach (α) (l : List GeachConfluent.Taple) : Hilbert α := Hilbert.ExtK (𝗚𝗲(l))

abbrev Hilbert.IsGeach (L : Hilbert α) (ts : List GeachConfluent.Taple) : Prop := L = Hilbert.Geach _ ts


namespace Hilbert.IsGeach

lemma ax {H : Hilbert α} (geach : H.IsGeach ts) : H.axioms = (𝗞 ∪ 𝗚𝗲(ts)) := by simp_all;

end Hilbert.IsGeach


instance Hilbert.K.is_geach : (Hilbert.K α).IsGeach [] := by simp;

instance Hilbert.KD.is_geach : (Hilbert.KD α).IsGeach [⟨0, 0, 1, 1⟩] := by simp [Axioms.D.is_geach];

instance Hilbert.KT.is_geach : (Hilbert.KT α).IsGeach [⟨0, 0, 1, 0⟩] := by simp [Axioms.T.is_geach];

instance Hilbert.KTB.is_geach : (Hilbert.KTB α).IsGeach [⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩] := by simp [Axioms.T.is_geach, Axioms.B.is_geach];

instance Hilbert.K4.is_geach : (Hilbert.K4 α).IsGeach [⟨0, 2, 1, 0⟩] := by simp [Axioms.Four.is_geach];

instance Hilbert.S4.is_geach : (Hilbert.S4 α).IsGeach [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩] := by simp [Axioms.T.is_geach, Axioms.Four.is_geach];

instance Hilbert.S4Dot2.is_geach : (Hilbert.S4Dot2 α).IsGeach [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩] := by
  simp [Axioms.T.is_geach, Axioms.Four.is_geach, Axioms.Dot2.is_geach, Set.union_assoc];

instance Hilbert.S5.is_geach : (Hilbert.S5 α).IsGeach [⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩] := by
  simp [Axioms.T.is_geach, Axioms.Five.is_geach];

instance Hilbert.KT4B.is_geach : (Hilbert.KT4B α).IsGeach [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩] := by
  simp [Axioms.T.is_geach, Axioms.Four.is_geach, Axioms.B.is_geach, Set.union_assoc];

instance Hilbert.Triv.is_geach : (Hilbert.Triv α).IsGeach [⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩] := by
  simp [Axioms.T.is_geach, Axioms.Tc.is_geach];

end LO.Modal
