import Foundation.Modal.Kripke.Logic.KT
import Foundation.Modal.Kripke.Logic.KTc
import Foundation.Modal.Kripke.Rooted
import Foundation.Modal.Kripke.Logic.GrzPoint3
import Foundation.Modal.Kripke.Logic.S4Point4M

namespace LO.Modal

open Kripke
open Hilbert.Kripke


namespace Kripke

protected abbrev FrameClass.refl_corefl : FrameClass := { F | F.IsReflexive ∧ IsCoreflexive _ F }
protected abbrev FrameClass.equality : FrameClass := { F | IsEquality _ F }
protected abbrev FrameClass.finite_equality : FrameClass := { F | Finite F.World ∧ IsEquality _ F }

lemma FrameClass.eq_equality_refl_corefl : Kripke.FrameClass.equality = Kripke.FrameClass.refl_corefl := by
  ext F;
  constructor;
  . intro F_eq;
    replace F_eq := Set.mem_setOf_eq.mp F_eq;

  . rintro ⟨hRefl, hCorefl⟩;
    apply Set.mem_setOf_eq.mpr;
    infer_instance;

end Kripke


namespace Hilbert.Triv.Kripke

instance sound_refl_corefl : Sound (Hilbert.Triv) Kripke.FrameClass.refl_corefl :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomK;
    rintro F ⟨_, _⟩ _ (rfl | rfl);
    . exact validate_AxiomT_of_reflexive;
    . exact validate_AxiomTc_of_coreflexive;

instance sound_equality : Sound (Hilbert.Triv) Kripke.FrameClass.equality := by
  convert sound_refl_corefl;
  rw [Kripke.FrameClass.eq_equality_refl_corefl];

instance sound_finite_equality : Sound (Hilbert.Triv) Kripke.FrameClass.finite_equality :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomK;
    rintro F ⟨_, _⟩ _ (rfl | rfl);
    . exact validate_AxiomT_of_reflexive;
    . exact validate_AxiomTc_of_coreflexive;

instance consistent : Entailment.Consistent (Hilbert.Triv) := consistent_of_sound_frameclass Kripke.FrameClass.refl_corefl $ by
  use whitepoint;



instance cannonical_refl_corefl : Canonical (Hilbert.Triv) Kripke.FrameClass.refl_corefl := ⟨by
  apply Set.mem_setOf_eq.mpr;

⟩

instance complete_refl_corefl : Complete (Hilbert.Triv) Kripke.FrameClass.refl_corefl := inferInstance

instance complete_equality : Complete (Hilbert.Triv) Kripke.FrameClass.equality := by
  rw [Kripke.FrameClass.eq_equality_refl_corefl];
  infer_instance;


section FFP

open Relation in
instance complete_finite_equality : Complete (Hilbert.Triv) Kripke.FrameClass.finite_equality := ⟨by
  intro φ hφ;
  apply Kripke.complete_equality.complete;
  intro F F_eq V r;
  replace F_eq := Set.mem_setOf_eq.mp F_eq;
  apply Model.pointGenerate.modal_equivalent_at_root (r := r) |>.mp;
  apply hφ;
  refine ⟨?_, ?_⟩;
  . apply finite_iff_exists_equiv_fin.mpr;
    use 1;
    constructor;
    trans Unit;
    . refine ⟨λ _ => (), λ _ => ⟨r, by tauto⟩, ?_, ?_⟩
      . simp only [Function.LeftInverse, Subtype.forall, Subtype.mk.injEq, forall_eq_or_imp, true_and];
        intro x Rrx;
        exact IsEquality.equality.mp $ Relation.TransGen.unwrap Rrx
      . simp [Function.RightInverse, Function.LeftInverse];
    . exact finOneEquiv.symm;
  . apply isEquality_iff _ _ |>.mpr;
    rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩;
    . simp [IsRefl.refl];
    all_goals
    . simp only [Subtype.mk.injEq]; apply IsEquality.equality;
⟩

end FFP

end Hilbert.Triv.Kripke


namespace Logic

open Formula
open Entailment
open Kripke


lemma Triv.Kripke.equality : Logic.Triv = FrameClass.equality.logic := eq_hilbert_logic_frameClass_logic
lemma Triv.Kripke.finite_equality : Logic.Triv = FrameClass.finite_equality.logic := eq_hilbert_logic_frameClass_logic

@[simp]
theorem Triv.proper_extension_of_KTc : Logic.KTc ⊂ Logic.Triv := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.Triv ⊢! φ ∧ ¬FrameClass.corefl ⊧ φ by
      rw [KTc.Kripke.corefl];
      tauto;
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => False⟩, λ w _ => False⟩, 0;
      constructor;
      . refine ⟨by tauto⟩;
      . simp [Satisfies, Semantics.Realize];

@[simp]
theorem Triv.proper_extension_of_GrzPoint3 : Logic.GrzPoint3 ⊂ Logic.Triv := by
  constructor;
  . rw [GrzPoint3.Kripke.finite_connected_partial_order, Triv.Kripke.finite_equality];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨by tauto, inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.Triv ⊢! φ ∧ ¬FrameClass.finite_connected_partial_order ⊧ φ by
      rw [GrzPoint3.Kripke.finite_connected_partial_order];
      tauto;
    use Axioms.Tc (.atom 0);
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, (λ w _ => w = 0)⟩;
      use M, 0;
      constructor;
      . refine ⟨by tauto, {refl := ?_, trans := ?_, antisymm := ?_}, ⟨?_⟩⟩;
        . tauto;
        . omega;
        . simp only [M]; omega;
        . simp only [Connected, and_imp, M]; omega;
      . suffices ∃ x, (0 : M.World) ≺ x ∧ x ≠ 0 by
          simpa [Semantics.Realize, Satisfies, ValidOnFrame, M];
        use 1;
        constructor;
        . omega;
        . trivial;

@[simp]
theorem Triv.proper_extension_of_S4Point4M : Logic.S4Point4M ⊂ Logic.Triv := by
  constructor;
  . rw [S4Point4M.Kripke.preorder_sobocinski_mckinsey, Triv.Kripke.finite_equality];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨by tauto, inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.Triv ⊢! φ ∧ ¬FrameClass.S4Point4M ⊧ φ by
      rw [S4Point4M.Kripke.preorder_sobocinski_mckinsey];
      tauto;
    use Axioms.Tc (.atom 0);
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, (λ w _ => w = 0)⟩;
      use M, 0;
      constructor;
      . refine ⟨?_, ⟨?_⟩, ⟨?_⟩⟩;
        . tauto;
        . intro x y z _ Rxy Ryz;
          match x, y, z with
          | 0, 0, _ => contradiction;
          | 1, 1, _ => contradiction;
          | 0, 1, _ => omega
          | 1, 0, _ => omega;
        . intro x;
          use 1;
          simp [M];
          constructor <;> omega;
      . suffices ∃ x, (0 : M.World) ≺ x ∧ x ≠ 0 by
          simpa [Semantics.Realize, Satisfies, ValidOnFrame, M];
        use 1;
        constructor;
        . omega;
        . trivial;

@[simp]
theorem Univ.proper_extension_of_Triv : Logic.Triv ⊂ Logic.Univ := by  constructor <;> simp;

end Logic



end LO.Modal
