module

public import Foundation.Propositional.Kripke.AxiomLEM
public import Foundation.Propositional.Kripke.Hilbert.LC

@[expose] public section

namespace LO.Propositional.Hilbert

open Kripke
open Formula.Kripke

namespace Cl

instance : ({ F : Frame | F.IsEuclidean }) ⊧* (Hilbert.Cl : Hilbert ℕ) := by
  constructor;
  rintro φ (⟨_, rfl⟩ | ⟨_, _, _, rfl⟩) F hF <;>
  replace hF := Set.mem_setOf_eq.mp hF;
  . grind;
  . exact validate_axiomLEM_of_isEuclidean;

instance : whitepoint.IsEuclidean := ⟨by tauto⟩

instance : Entailment.Consistent (Hilbert.Cl : Hilbert ℕ) := consistent_of_nonempty_frameClass ({ F : Frame | F.IsEuclidean }) $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Canonical (Hilbert.Cl : Hilbert ℕ) ({ F : Frame | F.IsEuclidean }) := by
  constructor;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance instKripkeComplete : Complete (Hilbert.Cl : Hilbert ℕ) ({ F : Frame | F.IsEuclidean }) := inferInstance

open finestFiltrationTransitiveClosureModel Relation in
instance instKripkeCompleteFinite : Complete (Hilbert.Cl : Hilbert ℕ) ({ F : Frame | Finite F ∧ F.IsSymmetric }) := by
  constructor;
  intro φ hφ;
  apply Complete.complete (𝓜 := ({ F : Frame | F.IsEuclidean }));
  rintro F F_conn V r;
  replace F_conn := Set.mem_setOf_eq.mp F_conn;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;

  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFiltrationTransitiveClosureModel RM (φ.subformulas);
  apply filtration FRM finestFiltrationTransitiveClosureModel.filterOf (by simp) |>.mpr;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  refine ⟨?_, ⟨?_⟩⟩;
  . apply FilterEqvQuotient.finite;
    simp;
  . rintro ⟨x, (rfl | Rrx)⟩ ⟨y, (rfl | Rry)⟩ RXY;
    . simp_all;
    . apply TransGen.single;
      use ⟨y, by tauto⟩, ⟨x, by tauto⟩;
      refine ⟨by tauto, by tauto, ?_⟩;
      . have : y ≺ x := Std.Symm.symm _ _ Rry;
        tauto;
    . apply TransGen.single;
      use ⟨y, by tauto⟩, ⟨x, by tauto⟩;
      refine ⟨by tauto, by tauto, ?_⟩;
      . have : x ≺ y := Std.Symm.symm _ _ Rrx;
        tauto;
    . apply Relation.TransGen.single;
      use ⟨y, by tauto⟩, ⟨x, by tauto⟩;
      refine ⟨by tauto, by tauto, ?_⟩;
      . exact F.eucl Rry Rrx;

instance : Complete (Hilbert.Cl : Hilbert ℕ) ({ F : Frame | Finite F ∧ F.IsEuclidean }) := by
  suffices ({F : Frame | Finite F.World ∧ F.IsEuclidean} = {F : Frame | Finite F.World ∧ F.IsSymmetric}) by
    rw [this]
    infer_instance;
  ext F;
  constructor <;> . rintro ⟨_, _⟩; exact ⟨by tauto, inferInstance⟩;

end Cl

instance : (Hilbert.LC : Hilbert ℕ) ⪱ Hilbert.Cl := by
  constructor;
  . apply weakerThan_of_provable_schema;
    rintro φ (⟨_, rfl⟩ | ⟨_, _, rfl⟩) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.LEM (.atom 0);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := { F : Frame | F.IsPiecewiseStronglyConnected })
      apply not_validOnFrameClass_of_exists_frame;
      let F : Frame := {
        World := Fin 2,
        Rel := λ x y => x ≤ y
        rel_partial_order := {
          refl := by omega;
          trans := by omega;
          antisymm := by omega;
        }
      };
      use F;
      constructor;
      . constructor;
        intro x y z;
        omega;
      . apply not_imp_not.mpr $ Kripke.isEuclidean_of_validate_axiomLEM;
        by_contra hC;
        have := @F.eucl _ 0 1 0;
        omega;

end LO.Propositional.Hilbert

end
