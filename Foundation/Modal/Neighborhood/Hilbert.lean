import Foundation.Modal.Hilbert.Minimal.Basic
import Foundation.Modal.Neighborhood.Basic

namespace LO.Modal

open Formula
open Modal.Neighborhood
open Formula.Neighborhood

variable {H : Hilbert.WithRE ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}
variable {F : Neighborhood.Frame} {C : Neighborhood.FrameClass}

namespace Hilbert.Neighborhood

section Frame

lemma soundness_of_axioms_validOnFrame (hC : F ⊧* H.axioms) : H ⊢! φ → F ⊧ φ := by
  intro hφ
  induction hφ using Hilbert.WithRE.rec! with
  | imply₁ | imply₂ | ec => simp
  | mdp ihφψ ihφ => exact ValidOnFrame.mdp ihφψ ihφ
  | re ihφ => exact ValidOnFrame.re ihφ
  | axm s h =>
    apply ValidOnFrame.subst s
    apply hC.RealizeSet
    assumption

instance instSound_of_axioms_validOnFrame (hV : F ⊧* H.axioms) : Sound H F := ⟨fun {_} => soundness_of_axioms_validOnFrame hV⟩

end Frame


section FrameClass

lemma soundness_of_validates_axioms (hC : C ⊧* H.axioms) : H ⊢! φ → C ⊧ φ := by
  intro hφ F hF
  induction hφ using Hilbert.WithRE.rec! with
  | imply₁ | imply₂ | ec => simp
  | mdp ihφψ ihφ => exact ValidOnFrame.mdp ihφψ ihφ
  | re ihφ => exact ValidOnFrame.re ihφ
  | axm s h =>
    intro V x
    apply ValidOnFrame.subst s $ @hC.RealizeSet _ h F hF

instance instSound_of_validates_axioms (hV : C ⊧* H.axioms) : Sound H C := ⟨fun {_} => soundness_of_validates_axioms hV⟩

lemma consistent_of_sound_frameclass
  (C : Neighborhood.FrameClass) (C_nonempty: C.Nonempty := by simp) [sound : Sound H C]
  : Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable (f := ⊥)
  apply not_imp_not.mpr sound.sound
  apply Semantics.set_models_iff.not.mpr
  push_neg
  use C_nonempty.choose
  constructor
  . exact C_nonempty.choose_spec
  . simp

end FrameClass

end Hilbert.Neighborhood

end LO.Modal
