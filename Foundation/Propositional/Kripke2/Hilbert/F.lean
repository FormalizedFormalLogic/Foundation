module

public import Foundation.Propositional.Kripke2.Hilbert.Basic
public import Foundation.Propositional.Hilbert.F.Disjunctive

@[expose] public section

namespace LO.Propositional

open Kripke2


namespace Kripke2

protected abbrev FrameClass.F : Kripke2.FrameClass := Set.univ

abbrev trivialFrame : Kripke2.Frame where
  World := Unit
  Rel _ _ := True
  root := ()
  rooted := by simp

end Kripke2


namespace HilbertF.F

open Kripke2

instance soundKripke2 : Sound (HilbertF.F : HilbertF ℕ) (Set.univ : Kripke2.FrameClass) := by
  apply instFrameClassSound;
  constructor;
  tauto;

instance : Entailment.Consistent (HilbertF.F : HilbertF ℕ) := consistent_of_sound_frameclass soundKripke2 $ by
  use Kripke2.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  simp;

open Formula.Kripke2 in
lemma unprovable_noncontradiction : (HilbertF.F ⊬ ∼((.atom 0) ⋏ ∼(.atom 0))) := by
  apply soundKripke2.not_provable_of_countermodel;
  apply Kripke2.not_validOnFrameClass_of_exists_frame;
  use ⟨Fin 2, (λ x y => x = 0), 0, by omega⟩;
  constructor;
  . tauto;
  . apply ValidOnFrame.not_of_exists_valuation_world;
    use (λ _ _ => True), 0;
    simp [Satisfies, Frame.Rel'];

end HilbertF.F

end LO.Propositional
end
