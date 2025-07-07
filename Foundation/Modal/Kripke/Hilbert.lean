import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.Basic

namespace LO.Modal

open Formula
open Kripke
open Formula.Kripke

variable {H : Hilbert ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}
variable {F : Kripke.Frame} {C : Kripke.FrameClass}


lemma Logic.eq_hilbert_logic_frameClass_logic {H : Hilbert ℕ} {C : FrameClass} [sound : Sound H.logic C] [complete : Complete H.logic C] : H.logic = C.logic := by
  ext φ;
  constructor;
  . intro h;
    apply sound.sound;
    simpa;
  . intro h;
    simpa using complete.complete h;

namespace Hilbert.Kripke

lemma soundness_of_validates_axiomInstances (hV : C.Validates H.axiomInstances) : H.logic ⊢! φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ with
  | maxm h =>
    obtain ⟨ψ, h, ⟨s, rfl⟩⟩ := h;
    apply hV F hF (ψ⟦s⟧);
    use ψ;
    constructor;
    . assumption;
    . use s;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | imply₁ => exact ValidOnFrame.imply₁;
  | imply₂ => exact ValidOnFrame.imply₂;
  | ec => exact ValidOnFrame.elimContra;

lemma validates_axioms_of_validates_axiomInstances (hV : C.Validates H.axioms) : C.Validates H.axiomInstances := by
  rintro F hF _ ⟨φ, hφ, ⟨s, rfl⟩⟩;
  exact ValidOnFrame.subst $ hV F hF φ hφ;

instance instSound_of_validates_axioms (hV : C.Validates H.axioms) : Sound H.logic C := ⟨fun {_} =>
  soundness_of_validates_axiomInstances (validates_axioms_of_validates_axiomInstances hV)
⟩

lemma consistent_of_sound_frameclass (C : Kripke.FrameClass) (C_nonempty: C.Nonempty := by simp)
  [sound : Sound H.logic C] : Entailment.Consistent H.logic := by
  apply Entailment.Consistent.of_unprovable (f := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨F, hF⟩ := C_nonempty;
  use F;
  constructor;
  . assumption;
  . simp;


lemma soundness_of_frame_validates_axiomInstances (hV : F ⊧* H.axiomInstances) : H.logic ⊢! φ → F ⊧ φ := by
  intro hφ;
  induction hφ with
  | maxm h =>
    simp only [Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff, forall_exists_index, and_imp] at hV;
    obtain ⟨ψ, h, ⟨s, rfl⟩⟩ := h;
    exact hV _ ψ h s rfl;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | imply₁ => exact ValidOnFrame.imply₁;
  | imply₂ => exact ValidOnFrame.imply₂;
  | ec => exact ValidOnFrame.elimContra;

lemma validates_axioms_of_frame_validates_axiomInstances (hV : F ⊧* H.axioms) : F ⊧* H.axiomInstances := by
  simp only [Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff, forall_exists_index, and_imp] at hV ⊢;
  rintro φ ψ hψ s rfl;
  apply ValidOnFrame.subst;
  exact hV.realize _ hψ;

instance instSound_of_frame_validates_axioms (hV : F ⊧* H.axioms) : Sound H.logic F := ⟨fun {_} =>
  soundness_of_frame_validates_axiomInstances (validates_axioms_of_frame_validates_axiomInstances hV)
⟩

lemma consistent_of_sound_frames (F : Kripke.Frame) [sound : Sound H.logic F] : Entailment.Consistent H.logic := by
  apply Entailment.Consistent.of_unprovable (f := ⊥);
  apply not_imp_not.mpr sound.sound;
  exact Kripke.ValidOnFrame.bot_def;

end Hilbert.Kripke

end LO.Modal
