import Foundation.ProvabilityLogic.GL.Completeness
import Foundation.ProvabilityLogic.S.Soundness

namespace LO

namespace Modal.Logic

open ProvabilityLogic
open Entailment
open Kripke Formula.Kripke

lemma iff_provable_GL_provable_box_S {A : Modal.Formula _} : A ∈ Logic.GL ↔ □A ∈ Logic.S := by
  constructor;
  . intro h;
    apply Logic.sumQuasiNormal.mem₁;
    apply nec! h;
  . intro h;
    apply GL.arithmetical_completeness (T := 𝐈𝚺₁);
    intro f;
    exact Iff.mp ((𝐈𝚺₁).standardDP 𝐈𝚺₁).sound (S.arithmetical_soundness h f)

theorem S.no_boxbot : □⊥ ∉ Logic.S := by
  apply iff_provable_GL_provable_box_S.not.mp;
  apply Logic.no_bot;

instance : Logic.S.Consistent := ⟨by
  apply Set.eq_univ_iff_forall.not.mpr;
  push_neg;
  use □⊥;
  exact Logic.S.no_boxbot;
⟩

end Modal.Logic

end LO
