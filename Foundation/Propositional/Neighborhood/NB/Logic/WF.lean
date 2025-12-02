import Foundation.Propositional.Neighborhood.NB.Hilbert
import Foundation.Propositional.Hilbert.Corsi_WF


namespace LO.Propositional

open NBNeighborhood


namespace NBNeighborhood

protected abbrev FrameClass.WF : NBNeighborhood.FrameClass := Set.univ

abbrev trivialFrame : NBNeighborhood.Frame where
  World := Unit
  𝓧 := Set.univ
  NB _ := { (X, Y) | X.1 ⊆ Y.1 }
  NB_spec := by tauto
  𝓧_closed_inter := by tauto
  𝓧_closed_union := by tauto
  𝓧_closed_imp := by tauto
  r := ()
  r_rooted := by simp

end NBNeighborhood


namespace WF

open Hilbert.WF.NBNeighborhood

instance NBNeighborhood.sound : Sound Propositional.WF FrameClass.WF := by
  apply instFrameClassSound;
  constructor;
  tauto;

instance : Entailment.Consistent Propositional.WF := consistent_of_sound_frameclass FrameClass.WF $ by
  use NBNeighborhood.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  simp;

open Formula.NBNeighborhood

lemma unprovable_AxiomC : Propositional.WF ⊬ Axioms.C #0 #1 #2 := by
  apply Sound.not_provable_of_countermodel (𝓜 := NBNeighborhood.FrameClass.WF);
  apply NBNeighborhood.not_validOnFrameClass_of_exists_model_world;
  use {
    World := Fin 2,
    𝓧 := Set.univ,
    NB w := λ ⟨X, Y⟩ =>
      match w with
      | 0 => X.1 ⊆ Y.1
      | 1 => (X.1 ⊆ Y.1) ∨ (X.1 = Set.univ ∧ Y.1 = {0}) ∨ (X.1 = Set.univ ∧ Y.1 = {1})
    ,
    NB_spec {w} := by
      match w with
      | 0 => tauto
      | 1 => tauto
    ,
    𝓧_closed_inter := by tauto,
    𝓧_closed_union := by tauto,
    𝓧_closed_imp := by tauto,
    r := 0,
    r_rooted := by tauto;
    Val := λ p =>
      match p with
      | 0 => ⟨Set.univ, by tauto⟩
      | 1 => ⟨{1}, by tauto⟩
      | 2 => ⟨{0}, by tauto⟩
      | _ => ⟨∅, by tauto⟩
  }, 0;
  constructor;
  . tauto;
  . apply Forces.not_def_imp.mpr;
    apply Set.not_subset_iff_exists_mem_notMem.mpr;
    use 1;
    constructor;
    . simp; tauto;
    . rintro (_ | _ | _) <;> simp_all;

lemma unprovable_axiomD : Propositional.WF ⊬ Axioms.D #0 #1 #2 := by
  apply Sound.not_provable_of_countermodel (𝓜 := NBNeighborhood.FrameClass.WF);
  apply NBNeighborhood.not_validOnFrameClass_of_exists_model_world;
  use {
    World := Fin 2,
    𝓧 := Set.univ,
    NB w := λ ⟨X, Y⟩ =>
      match w with
      | 0 => X.1 ⊆ Y.1
      | 1 => (X.1 ⊆ Y.1) ∨ (X.1 = {0} ∧ Y.1 = {1})
    ,
    NB_spec {w} := by
      match w with
      | 0 => tauto
      | 1 => tauto
    ,
    𝓧_closed_inter := by tauto,
    𝓧_closed_union := by tauto,
    𝓧_closed_imp := by tauto,
    r := 0,
    r_rooted := by tauto;
    Val := λ p =>
      match p with
      | 0 => ⟨{1}, by tauto⟩
      | 1 => ⟨{0}, by tauto⟩
      | 2 => ⟨{1}, by tauto⟩
      | _ => ⟨∅, by tauto⟩
  }, 0;
  constructor;
  . tauto;
  . apply Forces.not_def_imp.mpr;
    apply Set.not_subset_iff_exists_mem_notMem.mpr;
    use 1;
    constructor;
    . simp; tauto;
    . suffices ({0, 1} : Set (Fin 2)) ≠ {0} by
        apply not_or.mpr;
        constructor;
        . simp;
        . simpa;
      grind;

lemma unprovable_AxiomI : Propositional.WF ⊬ Axioms.I #0 #1 #2 := by
  apply Sound.not_provable_of_countermodel (𝓜 := NBNeighborhood.FrameClass.WF);
  apply NBNeighborhood.not_validOnFrameClass_of_exists_model_world;
  use {
    World := Fin 2,
    𝓧 := Set.univ,
    NB w := λ ⟨X, Y⟩ =>
      match w with
      | 0 => X.1 ⊆ Y.1
      | 1 => (X.1 ⊆ Y.1) ∨ (X.1 = {1} ∧ Y.1 = {0}) ∨ (X.1 = {0} ∧ Y.1 = ∅)
    ,
    NB_spec {w} := by
      match w with
      | 0 => tauto
      | 1 => tauto
    ,
    𝓧_closed_inter := by tauto,
    𝓧_closed_union := by tauto,
    𝓧_closed_imp := by tauto,
    r := 0,
    r_rooted := by tauto;
    Val := λ p =>
      match p with
      | 0 => ⟨{1}, by tauto⟩
      | 1 => ⟨{0}, by tauto⟩
      | 2 => ⟨∅, by tauto⟩
      | _ => ⟨∅, by tauto⟩
  }, 0;
  constructor;
  . tauto;
  . apply Forces.not_def_imp.mpr;
    apply Set.not_subset_iff_exists_mem_notMem.mpr;
    use 1;
    constructor;
    . simp; tauto;
    . suffices ({0, 1} : Set (Fin 2)) ≠ {0} by apply not_or.mpr; simp_all;
      grind;

end WF



instance : Propositional.WF ⪱ Propositional.F := by
  constructor;
  . apply weakerThan_WF_Corsi_of_provable_axioms;
    simp [Entailment.ProvableSet]
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.C #0 #1 #2;
    constructor;
    . simp;
    . apply WF.unprovable_AxiomC;


end LO.Propositional
