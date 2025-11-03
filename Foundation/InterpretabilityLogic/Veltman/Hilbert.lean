import Foundation.InterpretabilityLogic.Hilbert.Basic.Basic
import Foundation.InterpretabilityLogic.Veltman.Basic

namespace LO.InterpretabilityLogic

open Formula
open Formula.Veltman

namespace Veltman

variable {Ax Ax₁ Ax₂ : Axiom ℕ} {φ : Formula ℕ}
variable {F : Frame} {C : FrameClass}

lemma soundness_of_validates_axioms (hGL : ∀ F ∈ C, F.IsInfiniteGL) (hV : C ⊧* Ax) : Hilbert.Basic Ax ⊢ φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ using Hilbert.Basic.rec! with
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
  | axiomK => exact ValidOnFrame.axiomK;
  | axiomL => have := hGL F hF; exact ValidOnFrame.axiomL;

instance instSound_of_validates_axioms (hGL : ∀ F ∈ C, F.IsInfiniteGL) (hV : C ⊧* Ax) : Sound (Hilbert.Basic Ax) C := ⟨fun {_} =>
  soundness_of_validates_axioms hGL hV
⟩

lemma consistent_of_sound_frameclass
  (C : Veltman.FrameClass) (C_nonempty: C.Nonempty)
  [sound : Sound (Hilbert.Basic Ax) C]
  : Entailment.Consistent (Hilbert.Basic Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨F, hF⟩ := C_nonempty;
  use F;
  constructor;
  . assumption;
  . simp;


lemma soundness_of_frame_validates_axioms [F.IsInfiniteGL] (hV : F ⊧* Ax) : (Hilbert.Basic Ax) ⊢ φ → F ⊧ φ := by
  intro hφ;
  induction hφ using Hilbert.Basic.rec! with
  | axm s h =>
    apply ValidOnFrame.subst;
    apply hV.models;
    assumption;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | imply₁ => exact ValidOnFrame.imply₁;
  | imply₂ => exact ValidOnFrame.imply₂;
  | ec => exact ValidOnFrame.elimContra;
  | axiomK => exact ValidOnFrame.axiomK;
  | axiomL => exact ValidOnFrame.axiomL;

instance instSound_of_frame_validates_axioms [F.IsInfiniteGL] (hV : F ⊧* Ax) : Sound (Hilbert.Basic Ax) F := ⟨fun {_} =>
  soundness_of_frame_validates_axioms hV
⟩

lemma consistent_of_sound_frames (F : Veltman.Frame) [sound : Sound (Hilbert.Basic Ax) F] : Entailment.Consistent (Hilbert.Basic Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  exact Veltman.ValidOnFrame.bot_def;

lemma weakerThan_of_subset_frameClass
  (C₁ C₂ : FrameClass) (hC : C₂ ⊆ C₁)
  [Sound (Hilbert.Basic Ax₁) C₁] [Complete (Hilbert.Basic Ax₂) C₂]
  : (Hilbert.Basic Ax₁) ⪯ (Hilbert.Basic Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ hφ;
  apply Complete.complete (𝓜 := C₂);
  intro F hF;
  apply Sound.sound (𝓜 := C₁) hφ;
  apply hC hF;

/-
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
-/

end Veltman

end LO.InterpretabilityLogic
