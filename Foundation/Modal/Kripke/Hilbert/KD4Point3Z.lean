import Foundation.Modal.Kripke.Completeness
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.AxiomWeakDot3
import Foundation.Modal.Kripke.AxiomGeach
import Mathlib.Order.Interval.Finset.Nat

namespace LO.Modal

namespace Kripke


section definability

open Formula (atom)
open Formula.Kripke

variable {F : Kripke.Frame}

def natLtFrame : Kripke.Frame where
  World := ℕ
  Rel x y := x < y

namespace natLtFrame

protected lemma serial : Serial natLtFrame.Rel := by
  rintro x;
  unfold natLtFrame at *;
  use x + 1;
  omega;

protected lemma transitive : Transitive natLtFrame.Rel := by simp [Transitive, natLtFrame]; omega;

protected lemma wellConnected : WeakConnected natLtFrame.Rel := by
  rintro x y z ⟨Rxy, Rxz, hyz⟩;
  unfold natLtFrame at x y z;
  rcases lt_trichotomy y z with (Ryz | rfl | Rzy) <;> tauto;

end natLtFrame

lemma natLtFrame_validates_axiomZ : natLtFrame ⊧ (Axioms.Z (.atom 0)) := by
  rintro V x;
  intro h₁ h₂ y Rxy;
  obtain ⟨z, Rxz, h₃⟩ := Satisfies.dia_def.mp h₂;
  unfold natLtFrame at x y z;
  rcases lt_trichotomy y z with (Ryz | rfl | Rzy);
  . apply h₁ _ Rxy;
    suffices ∀ i ∈ Finset.Ioo y z, Satisfies ⟨natLtFrame, V⟩ i (.atom 0) by
      intro u Ryu;
      simp only [natLtFrame, Frame.Rel'] at u Ryu;
      rcases (lt_trichotomy u z) with (Ruz | rfl | Rzu);
      . apply this; simp_all [Finset.mem_Ioo];
      . exact h₁ _ Rxz $ h₃;
      . apply h₃ _ Rzu;
    /-
      Now consider z - 1.
      We know z ⊧ 0 and z ⊧ □0, imedeiately proves any u > z, u ⊧ 0, so z - 1 ⊧ □0.
      By hypothesis, z - 1 ⊧ □0 ➝ 0, so z - 1 ⊧ 0.
      By similar arguents (by induction), z - 2, z - 3, ... y ⊧ 0.
    -/
    sorry;
  . exact h₁ y Rxy $ h₃;
  . exact h₃ _ Rzy;

lemma Hilbert.KD4Point3Z.Kripke.sound : Hilbert.KD4Point3Z ⊢! φ → natLtFrame ⊧ φ := by
  intro hφ;
  induction hφ using Hilbert.Deduction.rec! with
  | maxm h =>
    rcases (by simpa using h) with ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩;
    . tauto;
    . exact ValidOnFrame.subst $ validate_axiomD_of_serial natLtFrame.serial;
    . exact ValidOnFrame.subst $ validate_axiomFour_of_transitive natLtFrame.transitive;
    . exact ValidOnFrame.subst $ validate_WeakDot3_of_weakConnected natLtFrame.wellConnected;
    . exact ValidOnFrame.subst $ natLtFrame_validates_axiomZ;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | imply₁ => exact ValidOnFrame.imply₁;
  | imply₂ => exact ValidOnFrame.imply₂;
  | ec => exact ValidOnFrame.elimContra;

end definability

end Kripke

end LO.Modal
