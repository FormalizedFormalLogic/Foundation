module

public import Foundation.Propositional.FMT.Completeness
public import Foundation.Propositional.Hilbert.VF.Disjunctive

@[expose] public section

namespace LO.Propositional

open FMT


namespace FMT

abbrev trivialFrame : FMT.Frame where
  World := Unit
  Rel := λ _ _ _ => True
  root := ()
  rooted := by simp

end FMT


namespace HilbertVF.VF

open HilbertVF.FMT
open Formula.FMT

instance soundFMT : Sound HilbertVF.VF (Set.univ : FMT.FrameClass) := by
  apply instFrameClassSound;
  constructor;
  tauto;

instance : Entailment.Consistent (HilbertVF.VF : HilbertVF ℕ) := consistent_of_sound_frameclass (Set.univ : FMT.FrameClass) $ by
  use FMT.trivialFrame;
  simp;

instance completeFMT : Complete (HilbertVF.VF : HilbertVF ℕ) (Set.univ : FMT.FrameClass) := by
  constructor;
  intro φ h;
  apply FMT.provable_of_validOnHintikkaModel;
  apply h;
  tauto;

lemma unprovable_top_dntop : (HilbertVF.VF : HilbertVF ℕ) ⊬ ⊤ 🡘 ∼∼⊤ := by
  apply soundFMT.not_provable_of_countermodel;
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
  use M, 0;
  constructor;
  . tauto;
  . suffices ∃ x y : M, x ≺[∼∼⊤] y ∧ ∀ (x : M), ¬y ≺[∼⊤] x by simpa [M] using this;
    use 1, 2;
    grind;

end HilbertVF.VF

open Formula.FMT in
open Entailment.Corsi in
instance : (HilbertVF.VF : HilbertVF ℕ) ⪱ HilbertWF.WF := by
  constructor;
  . apply weakerThan_WF_VF_of_provable_axioms
    tauto;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (⊤ 🡒 #0 ⋏ #1) 🡘 (⊤ 🡒 #1 ⋏ #0);
    constructor;
    . exact ruleE equivId $ andIR K_comm K_comm
    . apply HilbertVF.VF.soundFMT.not_provable_of_countermodel;
      apply FMT.not_validOnFrameClass_of_exists_model_world;
      use {
        World := Fin 3,
        Rel φ x y :=
          match φ with
          | ⊤ 🡒 #1 ⋏ #0 => x ≤ y
          | ⊤ 🡒 #0 ⋏ #1 => x ≠ 1
          | _       => True
        ,
        root := 0,
        rooted := by grind
        Val a x := x = 2 → a = 0
      }, 0;
      constructor;
      . tauto;
      . apply Forces.not_def_iff.mpr;
        refine Or.inl ⟨1, trivial, ?_, ?_⟩;
        · -- 1 ⊩ ⊤ 🡒 #0 ⋏ #1  (vacuous: 1 ≺[·] · reduces to 1 ≠ 1)
          apply Forces.def_imp.mpr;
          intro z hz;
          exact absurd rfl hz;
        · -- 1 ⊮ ⊤ 🡒 #1 ⋏ #0  (witnessed at world 2, where #1 fails)
          intro hψ;
          have h2 := Forces.def_imp.mp hψ (y := 2) (show (1 : Fin 3) ≤ 2 by decide) Forces.def_top;
          have ha := (Forces.def_and.mp h2).1;
          rw [Forces.def_atom] at ha;
          simp at ha;

end LO.Propositional
end
