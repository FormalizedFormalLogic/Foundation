import Foundation.Propositional.Kripke.AxiomKrieselPutnam
import Foundation.Propositional.Kripke.Logic.Int

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke

@[reducible] protected alias Kripke.Frame.IsKP := Frame.SatisfiesKriselPutnamCondition
protected abbrev Kripke.FrameClass.KP : FrameClass := { F | F.SatisfiesKriselPutnamCondition }


namespace Hilbert.KP.Kripke

instance : Sound Hilbert.KP FrameClass.KP := instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F hF _ rfl;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply validate_axiomKrieselPutnam_of_satisfiesKrieselPutnamCondition

instance : Entailment.Consistent Hilbert.KP := consistent_of_sound_frameclass FrameClass.KP $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance

instance : Canonical Hilbert.KP FrameClass.KP := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance : Complete Hilbert.KP FrameClass.KP := inferInstance

end KP.Kripke

instance : Hilbert.Int ⪱ Hilbert.KP := by
  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.KrieselPutnam (.atom 0) (.atom 1) (.atom 2);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.all)
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Kripke.Model := {
        World := Fin 5
        Rel x y := x = y ∨ x = 0 ∨ (x ≤ 1 ∧ y = 2) ∨ (x ≤ 1 ∧ y = 3) ∨ (x ≤ 1 ∧ y = 4)
        rel_partial_order := {
          refl := by tauto;
          trans := by omega;
          antisymm := by omega;
        }
        Val := ⟨λ w a =>
          match a with
          | 0 => w = 2
          | 1 => w = 3
          | 2 => w = 4
          | _ => False,
          by
            intro x y Rxy a ha;
            split at ha;
            . subst ha; simp [Frame.Rel'] at Rxy; tauto;
            . subst ha; simp [Frame.Rel'] at Rxy; tauto;
            . subst ha; simp [Frame.Rel'] at Rxy; tauto;
            . tauto;
        ⟩
      }
      use M, 0;
      constructor;
      . tauto;
      . apply Satisfies.imp_def.not.mpr;
        push_neg;
        use 1;
        constructor;
        . tauto;
        . constructor;
          . intro x R1x;
            match x with
            | 0 => omega;
            | 1 =>
              suffices ¬Satisfies M 1 (∼.atom 0) by tauto
              apply Satisfies.neg_def.not.mpr;
              push_neg;
              use 2;
              constructor;
              . tauto;
              . simp [Semantics.Realize, Satisfies, M];
            | 2 => tauto;
            | 3 => tauto;
            | 4 => tauto;
          . apply Satisfies.or_def.not.mpr;
            push_neg;
            constructor;
            . apply Satisfies.imp_def.not.mpr;
              push_neg;
              use 4;
              constructor;
              . tauto;
              . simp [Semantics.Realize, Satisfies, M, Frame.Rel'];
            . apply Satisfies.imp_def.not.mpr;
              push_neg;
              use 3;
              constructor;
              . tauto;
              . simp [Semantics.Realize, Satisfies, M, Frame.Rel'];

end Hilbert


propositional_kripke 𝐊𝐏 FrameClass.KP

instance : 𝐈𝐧𝐭 ⪱ 𝐊𝐏 := inferInstance


end LO.Propositional
