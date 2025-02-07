import Foundation.Modal.Hilbert.Basic
import Foundation.Modal.Kripke.FiniteFrame

namespace LO.Modal

open Kripke
open Formula
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

lemma consistent_of_FrameClass_aux [nonempty : C.IsNonempty] [sound : Sound H C] : H ⊬ ⊥ := by
  apply not_imp_not.mpr sound.sound;
  apply ValidOnFrameClass.not_of_exists_frame;
  obtain ⟨F, hF⟩ := nonempty;
  use F;
  constructor;
  . assumption;
  . simp;

lemma consistent_of_FrameClass (C : Kripke.FrameClass) [C.IsNonempty] [Sound H C] : System.Consistent H := by
  apply System.Consistent.of_unprovable;
  exact consistent_of_FrameClass_aux (C := C);

end


section

variable {C : Kripke.FiniteFrameClass}

lemma soundness_of_FiniteFrameClass_definedBy_axiomInstances [defined : C.DefinedBy H.axiomInstances] : H ⊢! φ → C ⊧ φ := by
  rintro hφ _ ⟨F, ⟨hF, rfl⟩⟩;
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

instance [C.DefinedBy H.axioms] : Sound H C := ⟨fun {_} => soundness_of_FiniteFrameClass_definedBy_axiomInstances⟩

lemma consistent_of_FiniteFrameClass_aux [nonempty : C.IsNonempty] [sound : Sound H C] : H ⊬ ⊥ := by
  apply not_imp_not.mpr sound.sound;
  apply ValidOnFrameClass.not_of_exists_frame;
  obtain ⟨F, hF⟩ := nonempty;
  use F.toFrame;
  constructor;
  . use F;
  . simp;

lemma consistent_of_FiniteFrameClass (C : Kripke.FiniteFrameClass) [C.IsNonempty] [Sound H C] : System.Consistent H := by
  apply System.Consistent.of_unprovable;
  exact consistent_of_FiniteFrameClass_aux (C := C);

end


end Kripke.Hilbert

end LO.Modal
