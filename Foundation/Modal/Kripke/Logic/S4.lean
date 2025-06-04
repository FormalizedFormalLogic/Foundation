import Foundation.Modal.Entailment.KT
import Foundation.Modal.Kripke.Filtration
import Foundation.Modal.Kripke.Logic.KD4
import Foundation.Modal.Kripke.Logic.KT

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open GeachConfluent


namespace Kripke

protected abbrev FrameClass.preorder : FrameClass := { F | IsPreorder _ F }

protected abbrev FrameClass.finite_preorder: FrameClass := { F | Finite F.World ∧ IsPreorder _ F.Rel }

end Kripke


namespace Hilbert.S4.Kripke

instance sound : Sound (Hilbert.S4) Kripke.FrameClass.preorder := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;

instance consistent : Entailment.Consistent (Hilbert.S4) := consistent_of_sound_frameclass Kripke.FrameClass.preorder $ by
  use whitepoint;
  constructor;

instance canonical : Canonical (Hilbert.S4) Kripke.FrameClass.preorder := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor;
⟩

instance complete : Complete (Hilbert.S4) Kripke.FrameClass.preorder := inferInstance

open finestFiltrationTransitiveClosureModel in
instance finiteComplete : Complete (Hilbert.S4) Kripke.FrameClass.finite_preorder := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  rintro F F_preorder V x;
  replace F_preorder := Set.mem_setOf_eq.mp F_preorder;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFiltrationTransitiveClosureModel M φ.subformulas;
  apply filtration FM (finestFiltrationTransitiveClosureModel.filterOf) (by subformula) |>.mpr;
  apply hp;
  refine ⟨?_, ?_⟩;
  . apply FilterEqvQuotient.finite;
    simp;
  . exact finestFiltrationTransitiveClosureModel.isPreorder;
⟩

end Hilbert.S4.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma S4.Kripke.preorder : Logic.S4 = FrameClass.preorder.logic := eq_hilbert_logic_frameClass_logic

instance : ProperSublogic Logic.KT Logic.S4 := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp [axiomK!, axiomT!]) |>.subset;
  . suffices ∃ φ, Hilbert.S4 ⊢! φ ∧ ¬Kripke.FrameClass.refl ⊧ φ by
      rw [KT.Kripke.refl];
      tauto;
    use Axioms.Four (.atom 0);
    constructor;
    . exact axiomFour!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
          ⟨Fin 3, λ x y => (x = 0 ∧ y ≠ 2) ∨ (x = 1 ∧ y ≠ 0) ∨ (x = 2 ∧ y = 2)⟩,
          λ w _ => w = 0 ∨ w = 1
        ⟩;
      use M, 0;
      constructor;
      . refine ⟨by omega⟩;
      . suffices (∀ (y : M.World), (0 : M.World) ≺ y → y = 0 ∨ y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∃ y, x ≺ y ∧ y ≠ 0 ∧ y ≠ 1 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . intro y hy;
          match y with
          | 0 => tauto;
          | 1 => tauto;
          | 2 => omega;
        . use 1;
          constructor;
          . omega;
          . use 2;
            refine ⟨by omega;, by trivial, by trivial⟩;
⟩

instance : ProperSublogic Logic.KD4 Logic.S4 := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S4 ⊢! φ ∧ ¬FrameClass.serial_trans ⊧ φ by
      rw [KD4.Kripke.serial_trans];
      tauto;
    use Axioms.T (.atom 0);
    constructor;
    . exact axiomT!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 3, λ _ y => y = 1⟩, (λ w _ => w = 1)⟩, 0;
      constructor;
      . refine ⟨⟨by tauto⟩, ⟨by omega⟩⟩;
      . simp [Semantics.Realize, Satisfies];
⟩

instance : ProperSublogic Logic.KD Logic.S4 := ProperSublogic.trans Logic.KD Logic.KT Logic.S4

end Logic

end LO.Modal
