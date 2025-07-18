import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.PLoN.Basic

namespace LO.Modal

open PLoN
open Formula
open Formula.PLoN

namespace PLoN.Hilbert

open Formula
variable {C : PLoN.FrameClass}
variable {H : Hilbert.Normal ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}

lemma soundness_of_defined_by_AxiomInstances [defined : C.DefinedBy H.axiomInstances] : H ⊢! φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ using Hilbert.Normal.rec! with
  | axm s h =>
    apply defined.defines F |>.mp hF;
    aesop;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | imply₁ => exact ValidOnFrame.imply₁;
  | imply₂ => exact ValidOnFrame.imply₂;
  | ec => exact ValidOnFrame.elimContra;

instance [C.DefinedBy H.axiomInstances] : Sound H C := ⟨fun {_} => soundness_of_defined_by_AxiomInstances⟩

lemma consistent_of_FrameClass_aux [nonempty : C.IsNonempty] [sound : Sound H C] : H ⊬ ⊥ := by
  apply not_imp_not.mpr sound.sound;
  apply ValidOnFrameClass.not_of_exists_frame;
  obtain ⟨F, hF⟩ := nonempty;
  use F;
  constructor;
  . assumption;
  . simp;

lemma consistent_of_FrameClass (C : PLoN.FrameClass) [C.IsNonempty] [Sound H C] : Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable;
  exact consistent_of_FrameClass_aux (C := C);

end PLoN.Hilbert

end LO.Modal
