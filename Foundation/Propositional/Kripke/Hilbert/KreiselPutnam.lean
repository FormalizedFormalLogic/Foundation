module

public import Foundation.Propositional.Kripke.AxiomKreiselPutnam
public import Foundation.Propositional.Kripke.Hilbert.Int.Basic

@[expose] public section

namespace LO.Propositional.Hilbert

open Kripke
open Formula.Kripke

namespace KreiselPutnam

instance : ({ F : Frame | F.SatisfiesKreiselPutnamCondition }) ⊧* (Hilbert.KreiselPutnam : Hilbert ℕ) := by
  constructor;
  rintro φ (⟨_, rfl⟩ | ⟨_, _, _, rfl⟩) F hF <;>
  replace hF := Set.mem_setOf_eq.mp hF;
  . grind;
  . exact validate_axiomKreiselPutnam_of_satisfiesKreiselPutnamCondition;

instance : Entailment.Consistent (Hilbert.KreiselPutnam : Hilbert ℕ) := consistent_of_nonempty_frameClass ({ F : Frame | F.SatisfiesKreiselPutnamCondition }) $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Canonical (Hilbert.KreiselPutnam : Hilbert ℕ) ({ F : Frame | F.SatisfiesKreiselPutnamCondition }) := by
  constructor;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Complete (Hilbert.KreiselPutnam : Hilbert ℕ) ({ F : Frame | F.SatisfiesKreiselPutnamCondition }) := inferInstance

end KreiselPutnam

instance : (Hilbert.Int : Hilbert ℕ) ⪱ Hilbert.KreiselPutnam := by
  constructor;
  . apply weakerThan_of_le; simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.KreiselPutnam (.atom 0) (.atom 1) (.atom 2);
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
        Val := ⟨λ a w =>
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
        push Not;
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
              push Not;
              use 2;
              constructor;
              . tauto;
              . simp [Semantics.Models, Satisfies, M];
            | 2 => tauto;
            | 3 => tauto;
            | 4 => tauto;
          . apply Satisfies.or_def.not.mpr;
            push Not;
            constructor;
            . apply Satisfies.imp_def.not.mpr;
              push Not;
              use 4;
              constructor;
              . tauto;
              . simp [Semantics.Models, Satisfies, M, Frame.Rel'];
            . apply Satisfies.imp_def.not.mpr;
              push Not;
              use 3;
              constructor;
              . tauto;
              . simp [Semantics.Models, Satisfies, M, Frame.Rel'];

end LO.Propositional.Hilbert

end
