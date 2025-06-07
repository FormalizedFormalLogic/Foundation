import Foundation.Modal.Boxdot.Basic
import Foundation.Modal.Kripke.Logic.GL.Completeness
import Foundation.Modal.Kripke.Logic.Grz.Completeness

namespace LO.Modal


namespace Kripke

lemma mem_reflClosure_GrzFiniteFrameClass_of_mem_GLFiniteFrameClass (hF : F ∈ FrameClass.finite_trans_irrefl) : F^= ∈ FrameClass.finite_partial_order := by
  obtain ⟨_, _, _⟩ := hF;
  refine ⟨inferInstance, inferInstance⟩;

lemma mem_irreflClosure_GLFiniteFrameClass_of_mem_GrzFiniteFrameClass (hF : F ∈ FrameClass.finite_partial_order) : F^≠ ∈ FrameClass.finite_trans_irrefl := by
  obtain ⟨_, _, F_trans, F_antisymm⟩ := hF;
  refine ⟨inferInstance, inferInstance, inferInstance⟩;

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
  obtain ⟨F, ⟨_, _, _⟩, h⟩ := iff_not_validOnFrameClass_exists_frame.mp $ (not_imp_not.mpr $ Hilbert.Grz.Kripke.complete |>.complete) h;
  apply not_imp_not.mpr $ Hilbert.GL.Kripke.finite_sound.sound;
  apply iff_not_validOnFrameClass_exists_frame.mpr;
  use F^≠;
  constructor;
  . refine ⟨inferInstance, inferInstance, inferInstance⟩;
  . apply Kripke.iff_frame_boxdot_reflexive_closure.not.mpr;
    apply iff_reflexivize_irreflexivize'.not.mp;
    exact h;

theorem iff_provable_boxdot_GL_provable_Grz : φᵇ ∈ Logic.GL ↔ φ ∈ Logic.Grz := ⟨
  provable_Grz_of_provable_boxdot_GL,
  provable_boxdot_GL_of_provable_Grz
⟩

instance : BoxdotProperty (Logic.GL) (Logic.Grz) := ⟨Logic.iff_provable_boxdot_GL_provable_Grz⟩

end Logic

end LO.Modal
