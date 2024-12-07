import Foundation.Modal.Hilbert.Systems


namespace LO.Modal

variable {Ax : Theory α}

open System

protected abbrev Hilbert.Geach (α) (l : List GeachConfluent.Taple) : Hilbert α := Hilbert.ExtK (𝗚𝗲(l))

abbrev Hilbert.IsGeach (L : Hilbert α) (ts : List GeachConfluent.Taple) : Prop := L = Hilbert.Geach _ ts


namespace Hilbert.IsGeach

lemma ax {H : Hilbert α} (geach : H.IsGeach ts) : H.axioms = (𝗞 ∪ 𝗚𝗲(ts)) := by simp_all;

end Hilbert.IsGeach


namespace Hilbert

instance K.is_geach : (Hilbert.K α).IsGeach [] := by simp;

instance K4.is_geach : (Hilbert.K4 α).IsGeach [⟨0, 2, 1, 0⟩] := by simp;

instance K45.is_geach : (Hilbert.K45 α).IsGeach [⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩] := by simp;

instance K5.is_geach : (Hilbert.K5 α).IsGeach [⟨1, 1, 0, 1⟩] := by simp;

instance KB4.is_geach : (Hilbert.KB4 α).IsGeach [⟨0, 1, 0, 1⟩, ⟨0, 2, 1, 0⟩] := by simp;

instance KB5.is_geach : (Hilbert.KB5 α).IsGeach [⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩] := by simp;

instance KD.is_geach : (Hilbert.KD α).IsGeach [⟨0, 0, 1, 1⟩] := by simp;

instance KB.is_geach : (Hilbert.KB α).IsGeach [⟨0, 1, 0, 1⟩] := by simp;

instance KD4.is_geach : (Hilbert.KD4 α).IsGeach [⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩] := by simp;

instance KD45.is_geach : (Hilbert.KD45 α).IsGeach [⟨0, 0, 1, 1⟩,  ⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩] := by simp [Set.union_assoc];

instance KD5.is_geach : (Hilbert.KD5 α).IsGeach [⟨0, 0, 1, 1⟩, ⟨1, 1, 0, 1⟩] := by simp;

instance KDB.is_geach : (Hilbert.KDB α).IsGeach [⟨0, 0, 1, 1⟩, ⟨0, 1, 0, 1⟩] := by simp;

instance KT.is_geach : (Hilbert.KT α).IsGeach [⟨0, 0, 1, 0⟩] := by simp;

instance KT4B.is_geach : (Hilbert.KT4B α).IsGeach [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩] := by simp [Set.union_assoc];

instance KTB.is_geach : (Hilbert.KTB α).IsGeach [⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩] := by simp;

instance S4.is_geach : (Hilbert.S4 α).IsGeach [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩] := by simp;

instance S4Dot2.is_geach : (Hilbert.S4Dot2 α).IsGeach [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩] := by simp [Set.union_assoc];

instance S5.is_geach : (Hilbert.S5 α).IsGeach [⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩] := by simp;

instance Triv.is_geach : (Hilbert.Triv α).IsGeach [⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩] := by simp;

end Hilbert

end LO.Modal
