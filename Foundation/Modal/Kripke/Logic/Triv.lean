module

public import Foundation.Modal.Kripke.Logic.KTc
public import Foundation.Modal.Kripke.Logic.GrzPoint3
public import Foundation.Modal.Kripke.Logic.S4Point4McK
public import Foundation.Vorspiel.Rel.Equality

@[expose] public section

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

variable {F : Frame}

protected abbrev Frame.IsTriv (F : Frame) := _root_.IsEquality F.Rel
instance [F.IsTriv] : F.IsS4Point4McK where
  mckinsey := by simp [equality]

protected class Frame.IsFiniteTriv (F : Frame) extends F.IsFinite, F.IsTriv
instance [F.IsFiniteTriv] : F.IsFiniteGrzPoint3' where

@[simp] lemma Frame.equality [F.IsTriv] {x y : F} : x ≺ y ↔ x = y := by apply _root_.equality;

protected abbrev FrameClass.Triv : FrameClass := { F | F.IsTriv }
protected abbrev FrameClass.finite_Triv : FrameClass := { F | F.IsFiniteTriv }

end Kripke

instance : Sound Modal.Triv Kripke.FrameClass.Triv := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomTc_of_coreflexive;

instance : Sound Modal.Triv Kripke.FrameClass.finite_Triv := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomTc_of_coreflexive;

instance : Entailment.Consistent Modal.Triv := consistent_of_sound_frameclass Kripke.FrameClass.Triv $ by
  use whitepoint;
  constructor;

instance : Canonical Modal.Triv Kripke.FrameClass.Triv := ⟨by constructor⟩

instance : Complete Modal.Triv Kripke.FrameClass.Triv := inferInstance

section FFP

open Relation in
instance : Complete Modal.Triv Kripke.FrameClass.finite_Triv := ⟨by
  intro φ hφ;
  apply Complete.complete (𝓜 := Kripke.FrameClass.Triv);
  intro F F_eq V r;
  replace F_eq := Set.mem_setOf_eq.mp F_eq;
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
          exact Frame.equality.mp $ Rrx;
        . simp [Function.RightInverse, Function.LeftInverse];
      . exact finOneEquiv.symm;
    refl := by simp;
    corefl := by rintro ⟨x⟩ ⟨y⟩ Rxy; simpa [Subtype.mk.injEq] using Rxy;
  }
⟩

end FFP

instance : Modal.KTc ⪱ Modal.Triv := by
  constructor;
  . grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.T (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.KTc);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => False⟩, λ _ w => False⟩, 0;
      constructor;
      . refine ⟨by tauto⟩;
      . simp [Satisfies, Semantics.Models];

instance : Modal.GrzPoint3 ⪱ Modal.Triv := by
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass { F : Frame | F.IsFiniteGrzPoint3' } FrameClass.finite_Triv;
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Tc (.atom 0);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.finite_GrzPoint3);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, (λ _ w => w = 0)⟩;
      use M, 0;
      constructor;
      . exact {}
      . simp [Semantics.Models, Satisfies, M];
        grind;

instance : Modal.S4Point4McK ⪱ Modal.Triv := by
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass FrameClass.S4Point4McK FrameClass.Triv;
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Tc (.atom 0);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.S4Point4McK);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, (λ _ w => w = 0)⟩;
      use M, 0;
      constructor;
      . exact {
          refl := by tauto
          sobocinski := by
            intro x y z _ Rxy Ryz;
            match x, y, z with
            | 0, 0, _ => contradiction;
            | 1, 1, _ => contradiction;
            | 0, 1, _ => omega
            | 1, 0, _ => omega;
          mckinsey := by
            intro x;
            use 1;
            simp [M];
            constructor <;> omega;
        }
      . simp [Semantics.Models, Satisfies, M];
        grind;

end LO.Modal
end
