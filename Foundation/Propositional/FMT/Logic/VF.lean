module

public import Foundation.Propositional.FMT.Hilbert
public import Foundation.Propositional.FMT.Completeness
public import Foundation.Propositional.Hilbert.WF_VF
public import Foundation.Propositional.Hilbert.VF.Disjunctive


@[expose] public section

namespace LO.Propositional

open FMT


namespace FMT

protected abbrev FrameClass.VF : FMT.FrameClass := Set.univ

abbrev trivialFrame : FMT.Frame where
  World := Unit
  Rel := λ _ _ _ => True
  root := ()
  rooted := by simp

end FMT


namespace VF

open Hilbert.VF.FMT

instance FMT.sound : Sound Propositional.VF FrameClass.VF := by
  apply instFrameClassSound;
  constructor;
  tauto;


open Formula.FMT

instance : Entailment.Consistent Propositional.VF := consistent_of_sound_frameclass FrameClass.VF $ by
  use FMT.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  simp;

instance FMT.complete : Complete Propositional.VF FrameClass.VF := by
  constructor;
  intro φ h;
  apply FMT.provable_of_validOnHintikkaModel;
  apply h;
  tauto;

lemma unprovable_top_dntop : Propositional.VF ⊬ ⊤ ⭤ ∼∼⊤ := by
  apply Sound.not_provable_of_countermodel (𝓜 := FMT.FrameClass.VF);
  apply FMT.not_validOnFrameClass_of_exists_model_world;
  let M : FMT.Model := {
    World := Fin 3,
    Rel φ x y :=
      match φ with
      | ∼∼⊤     => x ≤ y
      | ∼⊤      => x ≠ 2
      | _       => True
    ,
    root := 0,
    rooted := by grind
    Val _ _ := True
  };
  use M, 0
  constructor;
  . tauto;
  . suffices ∃ x y : M, x ≺[∼∼⊤] y ∧ ∀ (x : M), ¬y ≺[∼⊤] x by simpa [M] using this;
    use 1, 2;
    grind;

open Formula.FMT

end VF

open Formula.FMT in
open Entailment.Corsi in
instance : Propositional.VF ⪱ Propositional.WF := by
  constructor;
  . apply weakerThan_WF_VF_of_provable_axioms
    simp [Entailment.ProvableSet]
  . apply Entailment.not_weakerThan_iff.mpr;
    use (⊤ ➝ #0 ⋏ #1) ⭤ (⊤ ➝ #1 ⋏ #0);
    constructor;
    . exact ruleE equivId $ andIR K_comm K_comm
    . apply Sound.not_provable_of_countermodel (𝓜 := FMT.FrameClass.VF);
      apply FMT.not_validOnFrameClass_of_exists_model_world;
      use {
        World := Fin 3,
        Rel φ x y :=
          match φ with
          | ⊤ ➝ #1 ⋏ #0 => x ≤ y
          | ⊤ ➝ #0 ⋏ #1 => x ≠ 1
          | _       => True
        ,
        root := 0,
        rooted := by grind
        Val x a := x = 2 → a = 0
      }, 0;
      constructor;
      . tauto;
      . simp;
        grind;


end LO.Propositional
end
