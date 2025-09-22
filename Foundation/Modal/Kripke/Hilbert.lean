import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.Basic

namespace LO.Modal

open Formula
open Kripke
open Formula.Kripke

variable {H H₁ H₂ : Hilbert.Normal ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}
variable {F : Kripke.Frame} {C : Kripke.FrameClass}


lemma eq_hilbert_logic_frameClass_logic {H : Hilbert.Normal ℕ} {C : FrameClass} [sound : Sound H C] [complete : Complete H C] : H.logic = C.logic := by
  ext φ;
  constructor;
  . intro h;
    apply sound.sound;
    simpa;
  . intro h;
    simpa using complete.complete h;


namespace Hilbert.Kripke


lemma soundness_of_validates_axioms (hV : C ⊧* H.axioms) : H ⊢ φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ using Hilbert.Normal.rec! with
  | @axm φ s h =>
    apply ValidOnFrame.subst;
    apply hV.realize;
    . assumption;
    . assumption;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | imply₁ => exact ValidOnFrame.imply₁;
  | imply₂ => exact ValidOnFrame.imply₂;
  | ec => exact ValidOnFrame.elimContra;

instance instSound_of_validates_axioms (hV : C ⊧* H.axioms) : Sound H C := ⟨fun {_} =>
  soundness_of_validates_axioms hV
⟩

lemma consistent_of_sound_frameclass (C : Kripke.FrameClass) (C_nonempty: C.Nonempty := by simp)
  [sound : Sound H C] : Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨F, hF⟩ := C_nonempty;
  use F;
  constructor;
  . assumption;
  . simp;

instance [Sound H C] : Sound H.logic C := by
  constructor;
  intro φ hφ;
  apply Sound.sound (𝓢 := H);
  grind;

instance [Complete H C] : Complete H.logic C := by
  constructor;
  intro φ hφ;
  suffices H ⊢ φ by grind;
  apply Complete.complete hφ;

lemma soundness_of_frame_validates_axioms (hV : F ⊧* H.axioms) : H ⊢ φ → F ⊧ φ := by
  intro hφ;
  induction hφ using Hilbert.Normal.rec! with
  | axm s h =>
    apply ValidOnFrame.subst;
    apply hV.realize;
    assumption;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | imply₁ => exact ValidOnFrame.imply₁;
  | imply₂ => exact ValidOnFrame.imply₂;
  | ec => exact ValidOnFrame.elimContra;

instance instSound_of_frame_validates_axioms (hV : F ⊧* H.axioms) : Sound H F := ⟨fun {_} =>
  soundness_of_frame_validates_axioms hV
⟩

lemma consistent_of_sound_frames (F : Kripke.Frame) [sound : Sound H F] : Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  exact Kripke.ValidOnFrame.bot_def;

lemma weakerThan_of_subset_frameClass (C₁ C₂ : FrameClass) (hC : C₂ ⊆ C₁) [Sound H₁ C₁] [Complete H₂ C₂] : H₁ ⪯ H₂ := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ hφ;
  apply Complete.complete (𝓜 := C₂);
  intro F hF;
  apply Sound.sound (𝓢 := H₁) (𝓜 := C₁) hφ;
  apply hC hF;

instance [Sound H F] : Sound H.logic F := by
  constructor;
  intro φ hφ;
  apply Sound.sound (𝓢 := H);
  grind;

instance [Complete H F] : Complete H.logic F := by
  constructor;
  intro φ hφ;
  suffices H ⊢ φ by grind;
  apply Complete.complete hφ;

end Hilbert.Kripke

end LO.Modal
