import Foundation.InterpretabilityLogic.Hilbert.Basic
import Foundation.InterpretabilityLogic.Veltman.Basic

namespace LO.InterpretabilityLogic

open Formula
open Formula.Veltman

namespace Veltman

variable {Ax Ax₁ Ax₂ : Axiom ℕ} {φ : Formula ℕ}
variable {F : Frame} {C : FrameClass}

lemma soundness_of_validates_axioms (hV : C ⊧* Ax) : Hilbert Ax ⊢ φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ using Hilbert.rec! with
  | @axm φ s h =>
    apply ValidOnFrame.subst;
    apply hV.models;
    . assumption;
    . assumption;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | imply₁ => exact ValidOnFrame.imply₁;
  | imply₂ => exact ValidOnFrame.imply₂;
  | ec => exact ValidOnFrame.elimContra;

instance instSound_of_validates_axioms (hV : C ⊧* Ax) : Sound (Hilbert Ax) C := ⟨fun {_} =>
  soundness_of_validates_axioms hV
⟩

lemma consistent_of_sound_frameclass
  (C : Veltman.FrameClass) (C_nonempty: C.Nonempty)
  [sound : Sound (Hilbert Ax) C]
  : Entailment.Consistent (Hilbert Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨F, hF⟩ := C_nonempty;
  use F;
  constructor;
  . assumption;
  . simp;


lemma soundness_of_frame_validates_axioms (hV : F ⊧* Ax) : (Hilbert Ax) ⊢ φ → F ⊧ φ := by
  intro hφ;
  induction hφ using Hilbert.rec! with
  | axm s h =>
    apply ValidOnFrame.subst;
    apply hV.models;
    assumption;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | imply₁ => exact ValidOnFrame.imply₁;
  | imply₂ => exact ValidOnFrame.imply₂;
  | ec => exact ValidOnFrame.elimContra;

instance instSound_of_frame_validates_axioms (hV : F ⊧* Ax) : Sound (Hilbert Ax) F := ⟨fun {_} =>
  soundness_of_frame_validates_axioms hV
⟩

lemma consistent_of_sound_frames (F : Veltman.Frame) [sound : Sound (Hilbert Ax) F] : Entailment.Consistent (Hilbert Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  exact Veltman.ValidOnFrame.bot_def;

lemma weakerThan_of_subset_frameClass
  (C₁ C₂ : FrameClass) (hC : C₂ ⊆ C₁)
  [Sound (Hilbert Ax₁) C₁] [Complete (Hilbert Ax₂) C₂]
  : (Hilbert Ax₁) ⪯ (Hilbert Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ hφ;
  apply Complete.complete (𝓜 := C₂);
  intro F hF;
  apply Sound.sound (𝓜 := C₁) hφ;
  apply hC hF;

lemma validates_CL_axioms_union (hV : C ⊧* Ax) : C ⊧* CL.axioms ∪ Ax := by
  constructor;
  rintro φ ((rfl | rfl | rfl | rfl | rfl | rfl) | hφ);
  . intro _ _; apply ValidOnFrame.axiomK;
  . intro _ _; apply ValidOnFrame.axiomL;
  . intro _ _; apply ValidOnFrame.axiomJ1;
  . intro _ _; apply ValidOnFrame.axiomJ2;
  . intro _ _; apply ValidOnFrame.axiomJ3;
  . intro _ _; apply ValidOnFrame.axiomJ4;
  . apply hV.models;
    assumption;

end Veltman

end LO.InterpretabilityLogic
