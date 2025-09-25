import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.PLoN.Basic

namespace LO.Modal

open PLoN
open Formula
open Formula.PLoN

namespace PLoN.Hilbert

open Formula

variable {Ax : Axiom ℕ} {φ : Formula ℕ}
variable {F : Frame} {C : FrameClass}

lemma soundness_of_defined_by_AxiomInstances [defined : C.DefinedBy Ax.instances] : Hilbert.Normal Ax ⊢ φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ using Hilbert.Normal.rec! with
  | @axm φ s h =>
    apply defined.defines F |>.mp hF;
    use φ;
    tauto;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | imply₁ => exact ValidOnFrame.imply₁;
  | imply₂ => exact ValidOnFrame.imply₂;
  | ec => exact ValidOnFrame.elimContra;

instance [C.DefinedBy Ax.instances] : Sound (Hilbert.Normal Ax) C := ⟨fun {_} => soundness_of_defined_by_AxiomInstances⟩

lemma consistent_of_FrameClass_aux [nonempty : C.IsNonempty] [sound : Sound (Hilbert.Normal Ax) C] : (Hilbert.Normal Ax) ⊬ ⊥ := by
  apply not_imp_not.mpr sound.sound;
  apply ValidOnFrameClass.not_of_exists_frame;
  obtain ⟨F, hF⟩ := nonempty;
  use F;
  constructor;
  . assumption;
  . simp;

lemma consistent_of_FrameClass (C : PLoN.FrameClass) [C.IsNonempty] [Sound (Hilbert.Normal Ax) C] : Entailment.Consistent (Hilbert.Normal Ax) := by
  apply Entailment.Consistent.of_unprovable;
  exact consistent_of_FrameClass_aux (C := C);

end PLoN.Hilbert

end LO.Modal
