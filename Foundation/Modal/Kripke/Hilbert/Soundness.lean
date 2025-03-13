import Foundation.Modal.Hilbert.Basic
import Foundation.Modal.Kripke.Basic

namespace LO.Modal

open Formula
open Kripke
open Formula.Kripke

namespace Hilbert.Kripke

variable {H : Hilbert ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ} {C : Kripke.FrameClass}

lemma soundness_of_validates_axiomInstances (hV : C.Validates H.axiomInstances)
  : H ⊢! φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ using Hilbert.Deduction.rec! with
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

instance instSound_of_validates_axioms (hV : C.Validates H.axioms) : Sound H C := ⟨fun {_} =>
  soundness_of_validates_axiomInstances (validates_axioms_of_validates_axiomInstances hV)
⟩

lemma consistent_of_sound_frameclass
  (C : Kripke.FrameClass) (C_nonempty: C.Nonempty := by simp) [sound : Sound H C]
  : Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable (f := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨F, hF⟩ := C_nonempty;
  use F;
  constructor;
  . assumption;
  . simp;

end Hilbert.Kripke

end LO.Modal
