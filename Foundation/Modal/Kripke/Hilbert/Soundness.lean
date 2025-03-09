import Foundation.Modal.Hilbert.Basic
import Foundation.Modal.Kripke.Basic

namespace LO.Modal

open Formula
open Kripke
open Formula.Kripke

namespace Kripke.Hilbert

variable {H : Hilbert ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}


section

variable {C : Kripke.FrameClass}

lemma soundness_of_FrameClass_definedBy_axiomInstances [defined : C.DefinedBy H.axiomInstances] : H ⊢! φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ using Hilbert.Deduction.rec! with
  | maxm h =>
    obtain ⟨ψ, h, ⟨s, rfl⟩⟩ := h;
    apply defined.defines F |>.mp hF (ψ⟦s⟧);
    use ψ;
    constructor;
    . assumption;
    . use s;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | imply₁ => exact ValidOnFrame.imply₁;
  | imply₂ => exact ValidOnFrame.imply₂;
  | ec => exact ValidOnFrame.elimContra;

instance [defs : C.DefinedBy H.axioms] : C.DefinedBy H.axiomInstances := ⟨by
  intro F;
  constructor;
  . rintro hF φ ⟨ψ, hψ, ⟨s, rfl⟩⟩;
    exact ValidOnFrame.subst $ defs.defines F |>.mp hF ψ hψ;
  . intro h;
    apply defs.defines F |>.mpr;
    intro φ hφ;
    apply h;
    use φ;
    constructor;
    . assumption;
    . use .id;
      simp;
⟩

instance [C.DefinedBy H.axioms] : Sound H C := ⟨fun {_} => soundness_of_FrameClass_definedBy_axiomInstances⟩

lemma consistent_of_FrameClass (C : Kripke.FrameClass) (C_nonempty: C.Nonempty := by simp) [sound : Sound H C] : Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable (f := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨F, hF⟩ := C_nonempty;
  use F;
  constructor;
  . assumption;
  . simp;

lemma finite_sound_of_sound (sound : Sound H C) : Sound H ({ F | F ∈ C ∧ Finite F }) := ⟨by
  rintro φ hφ F ⟨hF₁, _⟩;
  exact sound.sound hφ hF₁;
⟩

end

end Kripke.Hilbert

end LO.Modal
