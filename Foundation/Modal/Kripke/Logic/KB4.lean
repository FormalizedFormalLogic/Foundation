import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Logic.K45
import Foundation.Modal.Kripke.Logic.KB

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.symm_trans : FrameClass := { F | IsSymm _ F ∧ IsTrans _ F }

namespace Hilbert.KB4.Kripke

instance sound : Sound (Hilbert.KB4) Kripke.FrameClass.symm_trans := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomB_of_symmetric;
  . exact validate_AxiomFour_of_transitive;

instance consistent : Entailment.Consistent (Hilbert.KB4) := consistent_of_sound_frameclass Kripke.FrameClass.symm_trans $ by
  use whitepoint;
  constructor <;> infer_instance;

instance canonical : Canonical (Hilbert.KB4) Kripke.FrameClass.symm_trans := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.KB4) Kripke.FrameClass.symm_trans := inferInstance

end Hilbert.KB4.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma KB4.Kripke.refl_trans : Logic.KB4 = FrameClass.symm_trans.logic := eq_hilbert_logic_frameClass_logic

instance : ProperSublogic Logic.K45 Logic.KB4 := ⟨by
  constructor;
  . rw [K45.Kripke.trans_eucl, KB4.Kripke.refl_trans];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.KB4 ⊢! φ ∧ ¬FrameClass.trans_eucl ⊧ φ by
      rw [K45.Kripke.trans_eucl];
      tauto;
    use Axioms.B (.atom 0);
    constructor;
    . exact axiomB!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => y = 1⟩, λ w _ => w = 0⟩, 0;
      constructor;
      . refine ⟨⟨by tauto⟩, ⟨by tauto⟩⟩;
      . simp [Semantics.Realize, Satisfies];
⟩

instance : ProperSublogic Logic.KB Logic.KB4 := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KB4 ⊢! φ ∧ ¬FrameClass.symm ⊧ φ by
      rw [KB.Kripke.symm];
      tauto;
    use Axioms.Four (.atom 0);
    constructor;
    . exact axiomFour!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Bool, λ x y => x != y⟩, λ w _ => w = true⟩, false;
      constructor;
      . refine ⟨by simp⟩;
      . simp [Semantics.Realize, Satisfies];
        tauto;
⟩

end Logic

end LO.Modal
