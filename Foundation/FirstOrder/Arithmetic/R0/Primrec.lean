module

public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# Primitive recursion for truth of $\Delta_0$ formulas

Truth of a $\Delta_0$ formula, evaluated on a `List.Vector`, is a primitive recursive predicate.

## References

- [HP98, Theorem 0.35]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {ξ : Type*} (ε : ξ → ℕ)

@[primrec]
lemma bounded_primrec_vec :
    (k : ℕ) → (φ : ArithmeticSemiformula ξ k) → ℬ[<, ℒₒᵣ].Closure φ →
      PrimrecPred fun v : List.Vector ℕ k ↦ φ.Eval v.get ε
  | _, _, Bounding.Closure.verum _ => by simpa using PrimrecPred.const True
  | _, _, Bounding.Closure.falsum _ => by simpa using PrimrecPred.const False
  | _, _, Bounding.Closure.rel Language.Eq.eq v => by
    simpa [← Matrix.fun_eq_vec_two]
      using Primrec.eq.comp (term_primrec (v 0)) (term_primrec (v 1))
  | _, _, Bounding.Closure.nrel Language.Eq.eq v => by
    simpa [← Matrix.fun_eq_vec_two]
      using (Primrec.eq.comp (term_primrec (v 0)) (term_primrec (v 1))).not
  | _, _, Bounding.Closure.rel Language.LT.lt v => by
    simpa [← Matrix.fun_eq_vec_two]
      using Primrec.nat_lt.comp (term_primrec (v 0)) (term_primrec (v 1))
  | _, _, Bounding.Closure.nrel Language.LT.lt v => by
    simpa [← Matrix.fun_eq_vec_two]
      using (Primrec.nat_lt.comp (term_primrec (v 0)) (term_primrec (v 1))).not
  | _, _, Bounding.Closure.and hφ hψ => by
    simpa using (bounded_primrec_vec _ _ hφ).and (bounded_primrec_vec _ _ hψ)
  | _, _, Bounding.Closure.or hφ hψ => by
    simpa using (bounded_primrec_vec _ _ hφ).or (bounded_primrec_vec _ _ hψ)
  | n, _, Bounding.Closure.ball (φ := φ) hR pt hφ => by
    obtain rfl := Set.mem_singleton_iff.mp hR
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    have h : PrimrecRel fun (x : ℕ) (v : List.Vector ℕ n) ↦ φ.Eval (x ::ᵥ v).get ε :=
      (bounded_primrec_vec _ _ hφ).comp Primrec.vector_cons
    simpa [List.Vector.cons_get] using (PrimrecRel.forall_lt' h).comp (term_primrec t) .id
  | n, _, Bounding.Closure.bexs (φ := φ) hR pt hφ => by
    obtain rfl := Set.mem_singleton_iff.mp hR
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    have h : PrimrecRel fun (x : ℕ) (v : List.Vector ℕ n) ↦ φ.Eval (x ::ᵥ v).get ε :=
      (bounded_primrec_vec _ _ hφ).comp Primrec.vector_cons
    simpa [List.Vector.cons_get] using (PrimrecRel.exists_lt' h).comp (term_primrec t) .id

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
