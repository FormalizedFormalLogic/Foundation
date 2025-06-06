import Foundation.Modal.Kripke.AxiomVer
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Rooted
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Kripke.Logic.KTc
import Foundation.Modal.Kripke.Logic.GLPoint3

namespace LO.Modal

open Kripke
open Hilbert.Kripke

protected abbrev Kripke.FrameClass.isolated : FrameClass := { F | IsIsolated _ F }
protected abbrev Kripke.FrameClass.finite_isolated : FrameClass := { F | Finite F.World ∧ IsIsolated _ F }

namespace Hilbert.Ver.Kripke

instance sound : Sound (Hilbert.Ver) FrameClass.isolated := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F hF _ (rfl | rfl);
  have := Set.mem_setOf_eq.mp hF;
  exact Kripke.validate_AxiomVer_of_isolated (F := F);

instance sound_finite_isolated : Sound (Hilbert.Ver) Kripke.FrameClass.finite_isolated :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomK;
    rintro F ⟨_, _⟩ _ (rfl | rfl);
    exact validate_AxiomVer_of_isolated (F := F);

instance consistent : Entailment.Consistent (Hilbert.Ver) := consistent_of_sound_frameclass FrameClass.isolated $ by
  use blackpoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Kripke.Canonical (Hilbert.Ver) FrameClass.isolated := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete (Hilbert.Ver) FrameClass.isolated := inferInstance

instance complete_finite_isolated : Complete (Hilbert.Ver) Kripke.FrameClass.finite_isolated := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  intro F ⟨F_iso⟩ V r;
  apply Model.pointGenerate.modal_equivalent_at_root (r := r) |>.mp;
  apply hφ;
  refine ⟨?_, ?_⟩;
  . apply finite_iff_exists_equiv_fin.mpr;
    use 1;
    constructor;
    trans Unit;
    . refine ⟨λ _ => (), λ _ => ⟨r, by tauto⟩, ?_, ?_⟩
      . simp [Function.LeftInverse];
        intro x Rrx;
        exfalso;
        induction Rrx with
        | single h => exact F_iso h;
        | tail _ h => exact F_iso h;
      . simp [Function.RightInverse, Function.LeftInverse];
    . exact finOneEquiv.symm;
  . apply isIsolated_iff _ _ |>.mpr;
    rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ <;> apply F_iso;
⟩

end Hilbert.Ver.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma Ver.Kripke.isolated : Logic.Ver = FrameClass.isolated.logic := eq_hilbert_logic_frameClass_logic
lemma Ver.Kripke.finite_isolated : Logic.Ver = FrameClass.finite_isolated.logic := eq_hilbert_logic_frameClass_logic

theorem Ver.proper_extension_of_Ktc : Logic.KTc ⊂ Logic.Ver := by
  constructor;
  . rw [KTc.Kripke.corefl, Ver.Kripke.isolated];
    rintro φ hφ F hF;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply hφ;
    apply Set.mem_setOf_eq.mpr;
    infer_instance;
  . suffices ∃ φ, Hilbert.Ver ⊢! φ ∧ ¬FrameClass.corefl ⊧ φ by
      rw [KTc.Kripke.corefl];
      tauto;
    use (Axioms.Ver ⊥);
    constructor;
    . exact axiomVer!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 1, λ x y => True⟩, λ w _ => False⟩;
      use M, 0;
      constructor;
      . refine ⟨by unfold Coreflexive; trivial⟩
      . suffices ∃ x, (0 : M.World) ≺ x by simpa [Satisfies, Semantics.Realize];
        use 0;

theorem Ver.proper_extension_of_GLPoint3 : Logic.GLPoint3 ⊂ Logic.Ver := by
  constructor;
  . rw [GLPoint3.Kripke.finite_strict_linear_order, Ver.Kripke.finite_isolated];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨by tauto, inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.Ver ⊢! φ ∧ ¬FrameClass.finite_strict_linear_order ⊧ φ by
      rw [GLPoint3.Kripke.finite_strict_linear_order];
      tauto;
    use (Axioms.Ver ⊥);
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => x < y⟩, (λ w a => False)⟩, 0;
      constructor;
      . refine ⟨inferInstance, {irrefl := ?_, trans := ?_}, ⟨?_⟩⟩;
        . omega;
        . omega;
        . simp [WeakConnected];
      . simp only [Semantics.Realize, Satisfies, imp_false, not_forall, not_not];
        use 1;
        tauto;

@[simp]
theorem Univ.proper_extension_of_Ver : Logic.Ver ⊂ Logic.Univ := by  constructor <;> simp;

end Logic


end LO.Modal
