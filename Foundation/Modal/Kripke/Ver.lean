import Foundation.Modal.Kripke.Completeness

namespace LO.Modal

namespace Kripke

abbrev IsolatedFrameClass : FrameClass := { F | Isolated F }

lemma IsolatedFrameClass.is_defined_by_Ver : IsolatedFrameClass.DefinedBy 𝗩𝗲𝗿 := by
  intro F;
  simp [IsolatedFrameClass, Isolated, Semantics.RealizeSet];
  constructor;
  . intro h φ V x y Rxy;
    have := h Rxy;
    contradiction;
  . intro h x y hxy;
    exact h ⊥ (λ _ _ => True) x _ hxy;

end Kripke

namespace Hilbert

instance Ver.Kripke.sound : Sound (Hilbert.Ver ℕ) (Kripke.IsolatedFrameClass) := Kripke.instSound Kripke.IsolatedFrameClass.is_defined_by_Ver rfl

instance Ver.consistent : System.Consistent (Hilbert.Ver ℕ) := Kripke.instConsistent (C := Kripke.IsolatedFrameClass) $ by
  use Kripke.irreflexivePointFrame;
  tauto;

lemma Kripke.isolated_CanonicalFrame (h : 𝗩𝗲𝗿 ⊆ Ax) [System.Consistent (Hilbert.ExtK Ax)] : Isolated (canonicalFrame (Hilbert.ExtK Ax)) := by
  intro x y Rxy;
  have : (canonicalModel (Hilbert.ExtK Ax)) ⊧ □⊥ := iff_valid_on_canonicalModel_deducible.mpr $ (Hilbert.ExtK.maxm!) (by apply h; simp);
  exact this x _ Rxy;

instance Ver.Kripke.complete : Complete (Hilbert.Ver ℕ) (Kripke.IsolatedFrameClass) := Kripke.instCompleteOfCanonical (C := Kripke.IsolatedFrameClass) $ by
  apply Kripke.isolated_CanonicalFrame;
  tauto;

end Hilbert

end LO.Modal
