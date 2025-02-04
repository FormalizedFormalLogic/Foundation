import Foundation.Modal.Hilbert2.Basic
import Foundation.Modal.Kripke2.Basic

namespace LO.Modal

open Kripke
open Formula
open Formula.Kripke

namespace Kripke.Hilbert

variable {C : Kripke.FrameClass}
variable {H : Hilbert ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}

lemma soundness_of_defined_by_AxiomInstances [defined : C.DefinedBy H.axiomInstances] : H ⊢! φ → C ⊧ φ := by
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

instance [C.DefinedBy H.axioms] : Sound H C := ⟨fun {_} => soundness_of_defined_by_AxiomInstances⟩

lemma instConsistent_aux [nonempty : C.IsNonempty] [sound : Sound H C] : H ⊬ ⊥ := by
  apply not_imp_not.mpr sound.sound;
  apply ValidOnFrameClass.not_of_exists_frame;
  obtain ⟨F, hF⟩ := nonempty;
  use F;
  constructor;
  . assumption;
  . simp;

lemma instConsistent (C : Kripke.FrameClass) [C.IsNonempty] [Sound H C] : System.Consistent H := by
  apply System.Consistent.of_unprovable;
  exact instConsistent_aux (C := C);

end Kripke.Hilbert

end LO.Modal
