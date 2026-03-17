module

public import Foundation.Propositional.Hilbert.WF.Basic
public import Foundation.Propositional.Hilbert.VF.Basic

@[expose] public section

namespace LO.Propositional

lemma weakerThan_WF_VF_of_provable_axioms {Hw : HilbertWF α} {Hv : HilbertVF α}
  (h : Hw ⊢* Hv) : Hv ⪯ Hw := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ hφ;
  induction hφ with
  | axm => apply h; assumption;
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | _ => grind;

end LO.Propositional

end
