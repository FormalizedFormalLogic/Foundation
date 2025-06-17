import Foundation.Modal.Boxdot.Basic
import Foundation.Modal.Kripke.Logic.GL.Completeness
import Foundation.Modal.Kripke.Logic.Grz.Completeness

namespace LO.Modal


namespace Kripke

variable {F : Frame}

instance [F.IsFiniteGL] : F^=.IsFiniteGrz where
instance [F.IsFiniteGrz] : (F^≠).IsFiniteGL := by sorry

end Kripke


namespace Logic

open Kripke
open Formula.Kripke
open Formula (boxdotTranslate)
open Modal.Kripke
open Entailment


lemma provable_boxdot_GL_of_provable_Grz : φ ∈ Logic.Grz → φᵇ ∈ Logic.GL := Hilbert.boxdotTranslated_of_dominate $ by
  intro φ hp;
  rcases (by simpa using hp) with (⟨_, _, rfl⟩ | ⟨_, rfl⟩);
  . exact boxdot_axiomK!;
  . exact boxdot_Grz_of_L!

lemma provable_Grz_of_provable_boxdot_GL : φᵇ ∈ Logic.GL → φ ∈ Logic.Grz := by
  contrapose;
  intro h;
  obtain ⟨F, hF, h⟩ := iff_not_validOnFrameClass_exists_frame.mp $ (not_imp_not.mpr $ Hilbert.Grz.Kripke.complete |>.complete) h;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply not_imp_not.mpr $ Hilbert.GL.Kripke.finite_sound.sound;
  apply iff_not_validOnFrameClass_exists_frame.mpr;
  use F^≠;
  constructor;
  . apply Set.mem_setOf_eq.mpr; infer_instance;
  . apply Kripke.iff_frame_boxdot_reflexive_closure.not.mpr;
    apply iff_reflexivize_irreflexivize'.not.mp;
    assumption;

theorem iff_provable_boxdot_GL_provable_Grz : φᵇ ∈ Logic.GL ↔ φ ∈ Logic.Grz := ⟨
  provable_Grz_of_provable_boxdot_GL,
  provable_boxdot_GL_of_provable_Grz
⟩

instance : BoxdotProperty (Logic.GL) (Logic.Grz) := ⟨Logic.iff_provable_boxdot_GL_provable_Grz⟩

end Logic

end LO.Modal
