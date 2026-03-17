module

public import Foundation.Propositional.Hilbert.F.Basic
public import Foundation.Propositional.Hilbert.WF.Basic

@[expose] public section

namespace LO.Propositional

open Entailment.Corsi

lemma weakerThan_WF_Corsi_of_provable_axioms {Hf : HilbertF α} {Hw : HilbertWF α}
  (h : Hf ⊢* Hw) : Hw ⪯ Hf := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ hφ;
  induction hφ with
  | axm => apply h; assumption;
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | _ => grind;

end LO.Propositional
end
