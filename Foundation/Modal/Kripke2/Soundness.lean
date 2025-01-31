import Foundation.Modal.Hilbert2.Basic
import Foundation.Modal.Kripke2.Definability

namespace LO.Modal

namespace Hilbert.Kripke

variable {C : Kripke.FrameClass}
variable {H : Hilbert ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}

open Formula
open Formula.Kripke

lemma soundness_of_defined_by_AxiomInstances (definedBy : C.definedBy H.axiomInstances)
  : H ⊢! φ → C ⊧ φ := by
  intro hφ F hF;
  replace hφ := deductive₂_of_deductive hφ;
  induction hφ using Deduction₂.inducition! with
  | hMaxm h =>
    obtain ⟨ψ, h, ⟨s, rfl⟩⟩ := h;
    apply definedBy F |>.mp hF (ψ⟦s⟧);
    use ψ;
    constructor;
    . assumption;
    . use s;
  | hMdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | hNec ih => exact ValidOnFrame.nec ih;
  | hImply₁ => exact ValidOnFrame.imply₁;
  | hImply₂ => exact ValidOnFrame.imply₂;
  | hElimContra => exact ValidOnFrame.elimContra;

lemma defined_by_AxiomInstances_of_defined_by_Axioms (definedBy : C.definedBy H.axioms)
  : C.definedBy H.axiomInstances := by
  intro F;
  constructor;
  . rintro hC φ ⟨ψ, hs, ⟨s, rfl⟩⟩;
    exact Kripke.ValidOnFrame.subst $ definedBy F |>.mp hC ψ hs;
  . intro h;
    apply definedBy F |>.mpr;
    intro φ hφ;
    apply h;
    use φ;
    constructor;
    . assumption;
    . use id;

end Hilbert.Kripke

end LO.Modal
