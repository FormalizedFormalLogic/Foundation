import Foundation.Modal.Kripke.AxiomVer
import Foundation.Modal.Kripke.Logic.GLPoint3
import Foundation.Modal.Kripke.Logic.KTc

namespace LO.Modal

open Entailment
open Entailment.Context
open Formula
open Formula.Kripke
open Hilbert.Kripke
open Kripke

namespace Kripke

variable {F : Frame}

protected abbrev Frame.IsVer (F : Frame) := F.IsIsolated
protected class Frame.IsFiniteVer (F : Frame) extends F.IsFinite, F.IsVer

instance [F.IsFiniteVer] : F.IsFiniteGLPoint3 where

@[simp] lemma Frame.isolated [F.IsVer] {x y : F} : ¬x ≺ y := by apply _root_.isolated;

protected abbrev FrameClass.Ver : FrameClass := { F | F.IsVer }
protected abbrev FrameClass.finite_Ver : FrameClass := { F | F.IsFiniteVer }

end Kripke


namespace Logic.Ver.Kripke

instance : Sound Logic.Ver FrameClass.Ver := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F hF _ (rfl | rfl);
  simp_all only [Set.mem_setOf_eq];
  exact validate_AxiomVer_of_isIsolated;

instance : Sound (Logic.Ver) Kripke.FrameClass.finite_Ver :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomK;
    rintro F hF _ (rfl | rfl);
    simp_all only [Set.mem_setOf_eq];
    exact validate_AxiomVer_of_isIsolated;

instance : Entailment.Consistent Logic.Ver := consistent_of_sound_frameclass FrameClass.Ver $ by
  use blackpoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Kripke.Canonical Logic.Ver FrameClass.Ver := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance : Complete Logic.Ver FrameClass.Ver := inferInstance

instance complete : Complete (Logic.Ver) Kripke.FrameClass.finite_Ver := ⟨by
  intro φ hφ;
  apply LO.Complete.complete (𝓢 := Logic.Ver) (𝓜 := FrameClass.Ver);
  intro F hF V r;
  apply Model.pointGenerate.modal_equivalent_at_root (r := r) |>.mp;
  apply hφ;
  exact {
    world_finite := by
      apply finite_iff_exists_equiv_fin.mpr;
      use 1;
      constructor;
      trans Unit;
      . refine ⟨λ _ => (), λ _ => ⟨r, by tauto⟩, ?_, ?_⟩
        . simp only [Function.LeftInverse, Subtype.forall, Subtype.mk.injEq, forall_eq_or_imp, true_and];
          intro x Rrx;
          induction Rrx <;> simp_all;
        . simp [Function.RightInverse, Function.LeftInverse];
      . exact finOneEquiv.symm;
    isolated := by rintro ⟨x, (rfl | Rrx)⟩ ⟨y, (rfl | Rry)⟩ <;> simp_all;
  }
⟩

lemma isolated : Logic.Ver = FrameClass.Ver.logic := eq_hilbert_logic_frameClass_logic
lemma finite_Ver : Logic.Ver = FrameClass.finite_Ver.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.KTc ⪱ Logic.Ver := by
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    suffices ∀ φ, FrameClass.KTc ⊧ φ → FrameClass.Ver ⊧ φ by
      simpa [KTc.Kripke.corefl, Ver.Kripke.isolated];
    rintro φ hφ F hF;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply hφ;
    apply Set.mem_setOf_eq.mpr;
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Hilbert.Ver ⊢! φ ∧ ¬FrameClass.KTc ⊧ φ by simpa [KTc.Kripke.corefl];
    use (Axioms.Ver ⊥);
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 1, λ x y => True⟩, λ w _ => False⟩;
      use M, 0;
      constructor;
      . refine ⟨by unfold Coreflexive; trivial⟩
      . suffices ∃ x, (0 : M.World) ≺ x by
          simpa [Satisfies, Semantics.Realize];
        use 0;

instance : Logic.GLPoint3 ⪱ Logic.Ver := by
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    suffices ∀ φ, FrameClass.finite_GLPoint3 ⊧ φ → FrameClass.finite_Ver ⊧ φ by
      simpa [GLPoint3.Kripke.finite_strict_linear_order, Ver.Kripke.finite_Ver];
    rintro φ hφ F hF;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply hφ;
    apply Set.mem_setOf_eq.mpr;
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Hilbert.Ver ⊢! φ ∧ ¬FrameClass.finite_GLPoint3 ⊧ φ by simpa [GLPoint3.Kripke.finite_strict_linear_order];
    use (Axioms.Ver ⊥);
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => x < y⟩, (λ w a => False)⟩, 0;
      constructor;
      . exact {}
      . simp only [Semantics.Realize, Satisfies, imp_false, not_forall, not_not];
        use 1;
        tauto;

end Logic.Ver.Kripke

end LO.Modal
