module

public import Foundation.Propositional.Kripke3.Basic

@[expose] public section

namespace LO.Propositional

variable {κ α : Type*} [Nonempty κ]

namespace KripkeModel

variable {M : KripkeModel κ α} [IsTrans _ M.rel]
         {φ ψ χ : Formula α}

@[simp, grind .]
lemma validates_axiomTra₁ : M ⊧ Axioms.Tra1 φ ψ χ :=
  fun _ y _ hyφψ z Ryz _ w Rzw hzφ =>
  hyφψ w (IsTrans.trans y z w Ryz Rzw) hzφ

@[simp, grind .]
lemma validates_axiomTra₂ : M ⊧ Axioms.Tra2 φ ψ χ :=
  fun _ y _ hyφψ z Ryz hzψχ w Rzw hwφ =>
  hzψχ w Rzw $ hyφψ w (IsTrans.trans y z w Ryz Rzw) hwφ

end KripkeModel

end LO.Propositional

end
