import Logic.FirstOrder.Arith.PAminus

namespace Matrix

lemma fun_eq_vec₃ {v : Fin 3 → α} : v = ![v 0, v 1, v 2] := by
  funext x
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]

lemma fun_eq_vec₄ {v : Fin 4 → α} : v = ![v 0, v 1, v 2, v 3] := by
  funext x
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]
  rfl

end Matrix

namespace LO

namespace FirstOrder

namespace Rew

variable {L :Language} {μ μ₁ μ₂ : Type*} {n n₁ n₂} (ω : Rew L μ₁ n₁ μ₂ n₂)

@[simp] protected lemma qfree {p : Semiformula L μ₁ n₁} : (ω.hom p).qfree ↔ p.qfree := by
  induction p using Semiformula.rec' <;> try simp [Rew.rel, Rew.nrel, *]

end Rew

namespace Semiformula

@[simp] lemma univClosure_inj {p q : Semiformula L μ n} : ∀* p = ∀* q ↔ p = q := by
  induction n <;> simp [*]

@[simp] lemma exClosure_inj {p q : Semiformula L μ n} : ∃* p = ∃* q ↔ p = q := by
  induction n <;> simp [*]

variable {L : Language} [L.Eq] [L.LT]

@[simp] lemma eq_qfree (t u : Semiterm L μ n) : (“!!t = !!u”).qfree := by simp [Operator.operator, Operator.Eq.sentence_eq]

@[simp] lemma lt_qfree (t u : Semiterm L μ n) : (“!!t < !!u”).qfree := by simp [Operator.operator, Operator.LT.sentence_eq]

@[simp] lemma le_qfree (t u : Semiterm L μ n) : (“!!t ≤ !!u”).qfree := by
  simp [Operator.operator, Operator.LE.sentence_eq, Operator.Eq.sentence_eq, Operator.LT.sentence_eq]

end Semiformula

end FirstOrder

end LO
