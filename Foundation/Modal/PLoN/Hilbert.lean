module
import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.PLoN.Basic

namespace LO.Modal

open PLoN
open Formula
open Formula.PLoN

namespace Hilbert.PLoN

open Formula

variable {Ax : Axiom ℕ} {φ : Formula ℕ}
variable {F : Frame} {C : FrameClass}

lemma soundness_frameclass (hV : C ⊧* Ax.instances) : Hilbert.Normal Ax ⊢ φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ using Hilbert.Normal.rec! with
  | axm s h =>
    apply hV.models;
    . grind;
    . assumption;
  | mdp ihpq ihp =>
    intro V;
    apply ValidOnModel.mdp (ihpq V) (ihp V);
  | _ => grind;

instance instFrameClassSound (hV : C ⊧* Ax.instances) : Sound (Hilbert.Normal Ax) C := ⟨fun {_} => soundness_frameclass hV⟩

lemma consistent_of_nonempty_frameClass (C : PLoN.FrameClass) (hC : Set.Nonempty C) [sound : Sound (Hilbert.Normal Ax) C] : Entailment.Consistent (Hilbert.Normal Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨F, hF⟩ := hC;
  use F;
  grind;

end Hilbert.PLoN

end LO.Modal
