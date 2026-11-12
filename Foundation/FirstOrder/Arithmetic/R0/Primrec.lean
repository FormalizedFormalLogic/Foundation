module

public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# Primitive recursion for term evaluation

Evaluation of an arithmetical term, with variables read off a list, is primitive recursive.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

@[primrec]
lemma primrec_termVal {α : Type*} [Primcodable α] {l : α → List ℕ} (hl : Primrec l) :
    (t : ArithmeticTerm ℕ) → Primrec fun a ↦ Semiterm.val ![] ((l a).getD · 0) t
  | #x => x.elim0
  | &x => by simpa using (Primrec.list_getD 0).comp hl (Primrec.const x)
  | .func Language.Zero.zero _ => by simpa using Primrec.const 0
  | .func Language.One.one _ => by simpa using Primrec.const 1
  | .func Language.Add.add v => by
    simpa [Semiterm.val_func] using
      Primrec.nat_add.comp (primrec_termVal hl (v 0)) (primrec_termVal hl (v 1))
  | .func Language.Mul.mul v => by
    simpa [Semiterm.val_func] using
      Primrec.nat_mul.comp (primrec_termVal hl (v 0)) (primrec_termVal hl (v 1))

end FFL.FirstOrder.Arithmetic
