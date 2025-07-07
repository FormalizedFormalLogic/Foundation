import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.Basic

namespace LO.Modal

open Formula
open Kripke
open Formula.Kripke

variable {H : Hilbert.Normal ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}
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

lemma soundness_of_validates_axioms (hV : C.Validates H.axioms) : H ⊢! φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ using Hilbert.Normal.rec! with
  | axm s h =>
    apply ValidOnFrame.subst;
    apply hV F hF _ h;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | imply₁ => exact ValidOnFrame.imply₁;
  | imply₂ => exact ValidOnFrame.imply₂;
  | ec => exact ValidOnFrame.elimContra;

instance instSound_of_validates_axioms (hV : C.Validates H.axioms) : Sound H C := ⟨fun {_} =>
  soundness_of_validates_axioms hV
⟩

lemma consistent_of_sound_frameclass (C : Kripke.FrameClass) (C_nonempty: C.Nonempty := by simp)
  [sound : Sound H C] : Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable (f := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨F, hF⟩ := C_nonempty;
  use F;
  constructor;
  . assumption;
  . simp;


lemma soundness_of_frame_validates_axioms (hV : F ⊧* H.axioms) : H ⊢! φ → F ⊧ φ := by
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
  apply Entailment.Consistent.of_unprovable (f := ⊥);
  apply not_imp_not.mpr sound.sound;
  exact Kripke.ValidOnFrame.bot_def;

end Hilbert.Kripke

end LO.Modal
