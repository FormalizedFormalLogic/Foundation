module

public import Foundation.Modal.Hilbert.Normal.Basic
public import Foundation.Modal.Kripke.Basic

@[expose] public section

namespace LO.Modal

open Formula
open Kripke
open Formula.Kripke

namespace Kripke

variable {Ax : Axiom ℕ} {φ : Formula ℕ}
variable {F : Frame} {C : FrameClass}

lemma soundness_of_validates_axioms (hV : C ⊧* Ax) : Hilbert.Normal Ax ⊢ φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ using Hilbert.Normal.rec! with
  | @axm φ s h =>
    apply ValidOnFrame.subst;
    apply hV.models;
    . assumption;
    . assumption;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | implyK => exact ValidOnFrame.implyK;
  | implyS => exact ValidOnFrame.implyS;
  | ec => exact ValidOnFrame.elimContra;

instance instSound_of_validates_axioms (hV : C ⊧* Ax) : Sound (Hilbert.Normal Ax) C := ⟨fun {_} =>
  soundness_of_validates_axioms hV
⟩

lemma consistent_of_sound_frameclass
  (C : Kripke.FrameClass) (C_nonempty: C.Nonempty := by simp)
  [sound : Sound (Hilbert.Normal Ax) C]
  : Entailment.Consistent (Hilbert.Normal Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push Not;
  obtain ⟨F, hF⟩ := C_nonempty;
  use F;
  constructor;
  . assumption;
  . simp;

lemma soundness_of_frame_validates_axioms (hV : F ⊧* Ax) : (Hilbert.Normal Ax) ⊢ φ → F ⊧ φ := by
  intro hφ;
  induction hφ using Hilbert.Normal.rec! with
  | axm s h =>
    apply ValidOnFrame.subst;
    apply hV.models;
    assumption;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | implyK => exact ValidOnFrame.implyK;
  | implyS => exact ValidOnFrame.implyS;
  | ec => exact ValidOnFrame.elimContra;

instance instSound_of_frame_validates_axioms (hV : F ⊧* Ax) : Sound (Hilbert.Normal Ax) F := ⟨fun {_} =>
  soundness_of_frame_validates_axioms hV
⟩

lemma consistent_of_sound_frames (F : Kripke.Frame) [sound : Sound (Hilbert.Normal Ax) F] : Entailment.Consistent (Hilbert.Normal Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  exact Kripke.ValidOnFrame.bot_def;

lemma weakerThan_of_subset_frameClass
  (C₁ C₂ : FrameClass) (hC : C₂ ⊆ C₁)
  [Sound (Hilbert.Normal Ax₁) C₁] [Complete (Hilbert.Normal Ax₂) C₂]
  : (Hilbert.Normal Ax₁) ⪯ (Hilbert.Normal Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ hφ;
  apply Complete.complete (𝓜 := C₂);
  intro F hF;
  apply Sound.sound (𝓜 := C₁) hφ;
  apply hC hF;

end Kripke

end LO.Modal
end
