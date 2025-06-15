import Foundation.Modal.Entailment.KT
import Foundation.Modal.Kripke.Filtration
import Foundation.Modal.Kripke.Logic.KD4
import Foundation.Modal.Kripke.Logic.KT

namespace LO.Modal

open Kripke
open Hilbert.Kripke


namespace Kripke

protected abbrev FrameClass.preorder : FrameClass := { F | F.IsPreorder }

protected abbrev FrameClass.finite_preorder: FrameClass := { F | F.IsFinite ∧ F.IsPreorder }

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
  . apply finestFiltrationTransitiveClosureModel.isFinite $ by simp;
  . sorry;
⟩

end Hilbert.S4.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma S4.Kripke.preorder : Logic.S4 = FrameClass.preorder.logic := eq_hilbert_logic_frameClass_logic

@[simp]
theorem S4.proper_extension_of_KT : Logic.KT ⊂ Logic.S4 := by
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
      . exact { refl := by omega };
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

@[simp]
theorem S4.proper_extension_of_KD4 : Logic.KD4 ⊂ Logic.S4 := by
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
      . refine ⟨{serial := by simp [Serial]}, {trans := by simp}⟩;
      . simp [Semantics.Realize, Satisfies];

@[simp]
lemma S4.proper_extension_of_KD : Logic.KD ⊂ Logic.S4 := by trans Logic.KT <;> simp;

end Logic

end LO.Modal
