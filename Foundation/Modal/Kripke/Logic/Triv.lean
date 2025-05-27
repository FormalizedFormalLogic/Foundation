import Foundation.Modal.Kripke.Logic.KT
import Foundation.Modal.Kripke.Logic.KTc
import Foundation.Modal.Kripke.Rooted

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

namespace Kripke

protected abbrev FrameClass.refl_corefl : FrameClass := { F | IsRefl _ F ∧ IsCoreflexive _ F }
protected abbrev FrameClass.equality : FrameClass := { F | IsEquality _ F }
protected abbrev FrameClass.finite_equality : FrameClass := { F | Finite F.World ∧ IsEquality _ F }

lemma FrameClass.eq_equality_refl_corefl : Kripke.FrameClass.equality = Kripke.FrameClass.refl_corefl := by
  ext F;
  constructor;
  . intro F_eq;
    replace F_eq := Set.mem_setOf_eq.mp F_eq;
    constructor <;> infer_instance;
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
  constructor <;> infer_instance;


instance cannonical_refl_corefl : Canonical (Hilbert.Triv) Kripke.FrameClass.refl_corefl := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
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


lemma Logic.Triv.Kripke.equality : Logic.Triv = FrameClass.equality.logic := eq_hilbert_logic_frameClass_logic
lemma Logic.Triv.Kripke.finite_equality : Logic.Triv = FrameClass.finite_equality.logic := eq_hilbert_logic_frameClass_logic


end LO.Modal
