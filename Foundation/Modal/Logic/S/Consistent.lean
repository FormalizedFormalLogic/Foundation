import Foundation.ProvabilityLogic.GL.Completeness
import Foundation.ProvabilityLogic.S.Soundness

namespace LO

namespace Modal.Logic

open ProvabilityLogic
open Entailment
open Kripke Formula.Kripke

lemma iff_provable_GL_provable_box_S {A : Modal.Formula _} : Modal.GL ⊢ A ↔ Modal.S ⊢ □A := by
  constructor;
  . intro h;
    apply Logic.sumQuasiNormal.mem₁!;
    apply nec! h;
  . intro h;
    apply GL.arithmetical_completeness (T := 𝗜𝚺₁) (by simp);
    intro f;
    exact Iff.mp FirstOrder.ProvabilityAbstraction.sound_on_model (S.arithmetical_soundness h f)

theorem S.no_boxbot : Modal.S ⊬ □⊥ := iff_provable_GL_provable_box_S.not.mp $ by simp;

instance : Entailment.Consistent Modal.S := Entailment.Consistent.of_unprovable S.no_boxbot

end Modal.Logic

end LO
