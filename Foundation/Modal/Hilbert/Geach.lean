import Foundation.Modal.Hilbert.Systems


namespace LO.Modal

variable {Ax : Theory α}

open System

protected abbrev Hilbert.Geach (α) (l : List GeachConfluent.Taple) : Hilbert α := Hilbert.ExtK (𝗚𝗲(l))

abbrev Hilbert.IsGeach (L : Hilbert α) (ts : List GeachConfluent.Taple) : Prop := L = Hilbert.Geach _ ts


namespace Hilbert.IsGeach

lemma ax {H : Hilbert α} (geach : H.IsGeach ts) : H.axioms = (𝗞 ∪ 𝗚𝗲(ts)) := by simp_all;

end Hilbert.IsGeach


instance Hilbert.K.is_geach : (Hilbert.K α).IsGeach [] := by simp;

instance Hilbert.KD.is_geach : (Hilbert.KD α).IsGeach [⟨0, 0, 1, 1⟩] := by
  simp [Axioms.D.is_geach];

instance Hilbert.KT.is_geach : (Hilbert.KT α).IsGeach [⟨0, 0, 1, 0⟩] := by
  simp [Axioms.T.is_geach];

instance Hilbert.KTB.is_geach : (Hilbert.KTB α).IsGeach [⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩] := by
  simp [Axioms.T.is_geach, Axioms.B.is_geach];

instance Hilbert.K4.is_geach : (Hilbert.K4 α).IsGeach [⟨0, 2, 1, 0⟩] := by
  simp [Axioms.Four.is_geach];

instance Hilbert.S4.is_geach : (Hilbert.S4 α).IsGeach [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩] := by
  simp [Axioms.T.is_geach, Axioms.Four.is_geach];

instance Hilbert.S4Dot2.is_geach : (Hilbert.S4Dot2 α).IsGeach [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩] := by
  simp [Axioms.T.is_geach, Axioms.Four.is_geach, Axioms.Dot2.is_geach, Set.union_assoc];

instance Hilbert.S5.is_geach : (Hilbert.S5 α).IsGeach [⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩] := by
  simp [Axioms.T.is_geach, Axioms.Five.is_geach];

instance Hilbert.KT4B.is_geach : (Hilbert.KT4B α).IsGeach [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩] := by
  simp [Axioms.T.is_geach, Axioms.Four.is_geach, Axioms.B.is_geach, Set.union_assoc];

instance Hilbert.Triv.is_geach : (Hilbert.Triv α).IsGeach [⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩] := by
  simp [Axioms.T.is_geach, Axioms.Tc.is_geach];

end LO.Modal
