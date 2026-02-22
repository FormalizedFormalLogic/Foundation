module

public import Foundation.Modal.Kripke.AxiomVer
public import Foundation.Modal.Kripke.Logic.GLPoint3
public import Foundation.Modal.Kripke.Logic.KTc

@[expose] public section

namespace LO.Modal

open Entailment
open Entailment.Context
open Formula
open Formula.Kripke
open Modal.Kripke
open Kripke

namespace Kripke

variable {F : Frame}

protected abbrev Frame.IsVer (F : Frame) := F.IsIsolated
protected class Frame.IsFiniteVer (F : Frame) extends F.IsFinite, F.IsVer

instance [F.IsFiniteVer] : F.IsFiniteGLPoint3' where

@[simp] lemma Frame.isolated [F.IsVer] {x y : F} : ¬x ≺ y := by apply _root_.isolated;

protected abbrev FrameClass.Ver : FrameClass := { F | F.IsVer }
protected abbrev FrameClass.finite_Ver : FrameClass := { F | F.IsFiniteVer }

end Kripke



instance : Sound Modal.Ver FrameClass.Ver := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  simp only [Set.mem_singleton_iff, forall_eq];
  rintro F hF
  simp_all only [Set.mem_setOf_eq];
  exact validate_AxiomVer_of_isIsolated;

instance : Sound Modal.Ver Kripke.FrameClass.finite_Ver := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  simp only [Set.mem_singleton_iff, forall_eq];
  rintro F hF;
  simp_all only [Set.mem_setOf_eq];
  exact validate_AxiomVer_of_isIsolated;

instance : Entailment.Consistent Modal.Ver := consistent_of_sound_frameclass FrameClass.Ver $ by
  use blackpoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Kripke.Canonical Modal.Ver FrameClass.Ver := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance : Complete Modal.Ver FrameClass.Ver := inferInstance

instance : Complete Modal.Ver Kripke.FrameClass.finite_Ver := ⟨by
  intro φ hφ;
  apply LO.Complete.complete (𝓢 := Modal.Ver) (𝓜 := FrameClass.Ver);
  intro F hF V r;
  replace hF := Set.mem_setOf_eq.mp hF;
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
          exfalso;
          exact hF.isolated Rrx;
        . simp [Function.RightInverse, Function.LeftInverse];
      . exact finOneEquiv.symm;
    isolated := by rintro ⟨x, (rfl | Rrx)⟩ ⟨y, (rfl | Rry)⟩ <;> simp_all;
  }
⟩


instance : Modal.KTc ⪱ Modal.Ver := by
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass FrameClass.KTc FrameClass.Ver;
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Ver ⊥);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.KTc);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 1, λ x y => True⟩, λ _ w => False⟩;
      use M, 0;
      constructor;
      . refine ⟨by unfold Coreflexive; trivial⟩
      . suffices ∃ x, (0 : M.World) ≺ x by
          simpa [Satisfies, Semantics.Models];
        use 0;

instance : Modal.GLPoint3 ⪱ Modal.Ver := by
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass { F : Frame | F.IsFiniteGLPoint3' } FrameClass.finite_Ver;
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Ver ⊥);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.finite_GLPoint3);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => x < y⟩, (λ a w => False)⟩, 0;
      constructor;
      . exact {}
      . simp only [Semantics.Models, Satisfies, imp_false, not_forall, not_not];
        use 1;
        tauto;

end LO.Modal
end
