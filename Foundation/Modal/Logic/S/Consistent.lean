import Foundation.ProvabilityLogic.GL.Completeness
import Foundation.ProvabilityLogic.S.Soundness

namespace LO

namespace Modal.Logic

open ProvabilityLogic
open Entailment
open Kripke Formula.Kripke

lemma iff_provable_GL_provable_box_S {A : Modal.Formula _} : Logic.GL ⊢! A ↔ Logic.S ⊢! □A := by
  constructor;
  . intro h;
    apply Logic.sumQuasiNormal.mem₁!;
    apply nec! h;
  . intro h;
    apply GL.arithmetical_completeness (T := 𝐈𝚺₁);
    intro f;
    exact Iff.mp ((𝐈𝚺₁).standardDP 𝐈𝚺₁).sound (S.arithmetical_soundness h f)

theorem S.no_boxbot : Logic.S ⊬ □⊥ := iff_provable_GL_provable_box_S.not.mp $ by simp;

instance : Entailment.Consistent Logic.S := Entailment.Consistent.of_unprovable S.no_boxbot

end Modal.Logic

end LO
