import Foundation.Modal.Hilbert2.Basic
import Foundation.Modal.Kripke2.Definability

namespace LO.Modal

namespace Kripke.Hilbert

variable {C : Kripke.FrameClass}
variable {H : Hilbert ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}

open Formula
open Formula.Kripke

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

-- instance [C.DefinedBy H.axiomInstances] : Sound H C := ⟨fun {_} => soundness_of_defined_by_AxiomInstances⟩

instance [C.DefinedBy H.axioms] : Sound H C := ⟨fun {_} => soundness_of_defined_by_AxiomInstances⟩

lemma instConsistent_aux [sound : Sound H C] (hNonempty : C.Nonempty) : H ⊬ ⊥ := by
  apply not_imp_not.mpr sound.sound;
  apply not_validOnFrameClass_of_exists_frame;
  obtain ⟨F, hF⟩ := hNonempty;
  use F;
  constructor;
  . exact hF;
  . simp;

lemma instConsistent [Sound H C] (hNonempty : C.Nonempty) : System.Consistent H := by
  apply System.Consistent.of_unprovable;
  exact instConsistent_aux hNonempty

end Kripke.Hilbert

end LO.Modal
