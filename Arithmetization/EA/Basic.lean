import Arithmetization.IDeltaZero.Exponential
import Arithmetization.IDeltaZero.Bit
import Logic.FirstOrder.Arith.EA.Basic

namespace LO.FirstOrder

namespace Arith

noncomputable section

namespace Model.EA

variable {M : Type} [Nonempty M] [Zero M] [One M] [Add M] [Mul M] [Exp M] [LT M]

section Exp

variable [M ⊧ₘ* 𝐏𝐀⁻] [M ⊧ₘ* 𝐄𝐗𝐏]

@[simp] lemma exp_zero : exp (0 : M) = 1 := by
  simpa[models_iff] using ModelsTheory.models M Theory.Exponential.zero

lemma exp_succ : ∀ a : M, exp (a + 1) = 2 * exp a := by
  simpa[models_iff] using ModelsTheory.models M Theory.Exponential.succ

end Exp

variable [M ⊧ₘ* 𝐄𝐀]

instance : M ⊧ₘ* 𝐈𝚺₀ := models_iSigmaZero_of_models_elementaryArithmetic M

instance exp_definable_oRingExp : DefinableFunction₁ ℒₒᵣ(exp) 𝚺 0 (Exp.exp : M → M) where
  definable := ⟨⟨“#0 = exp #1”, by simp⟩, by intro _; simp⟩

instance exp_bounded_oRingExp : Bounded₁ ℒₒᵣ(exp) (Exp.exp : M → M) where
  bounded := ⟨ᵀ“exp #0”, by intro _; simp⟩

@[elab_as_elim] lemma induction_EA
    {P : M → Prop} (hP : DefinablePred ℒₒᵣ(exp) 𝚺 0 P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := induction_h 𝚺 0 hP zero succ

lemma exponential_exp (a : M) : Exponential a (exp a) := by
  induction a using induction_EA
  · definability
  case zero => simp
  case succ a ih =>
    simp [exp_succ, Exponential.exponential_succ_mul_two, ih]

lemma exponential_graph {a b : M} : a = exp b ↔ Exponential b a :=
  ⟨by rintro rfl; exact exponential_exp b, fun h ↦ Exponential.uniq h (exponential_exp b)⟩

alias ⟨_, exp_of_exponential⟩ := exponential_graph

@[simp] lemma exp_pow2 (a : M) : Pow2 (exp a) := (exponential_exp a).range_pow2

@[simp] lemma exp_monotone {a b : M} : exp a < exp b ↔ a < b :=
  Iff.symm <| Exponential.monotone_iff (exponential_exp a) (exponential_exp b)

@[simp] lemma exp_monotone_le {a b : M} : exp a ≤ exp b ↔ a ≤ b :=
  Iff.symm <| Exponential.monotone_le_iff (exponential_exp a) (exponential_exp b)

@[simp] lemma lt_exp (a : M) : a < exp a := (exponential_exp a).lt

@[simp] lemma exp_pos (a : M) : 0 < exp a := (exponential_exp a).range_pos

@[simp] lemma one_le_exp (a : M) : 1 ≤ exp a := pos_iff_one_le.mp (by simp)

lemma exp_inj : Function.Injective (Exp.exp : M → M) := λ a _ H ↦
  (exponential_exp a).inj (exponential_graph.mp H)

instance : Structure.Monotone ℒₒᵣ(exp) M := ⟨
  fun {k} f v₁ v₂ h ↦
  match k, f with
  | 0, Language.Zero.zero => by rfl
  | 0, Language.One.one   => by rfl
  | 2, Language.Add.add   => add_le_add (h 0) (h 1)
  | 2, Language.Mul.mul   => mul_le_mul (h 0) (h 1) (by simp) (by simp)
  | 1, Language.Exp.exp   => by simpa using h 0⟩

@[elab_as_elim] lemma order_induction
    {P : M → Prop} (hP : DefinablePred ℒₒᵣ(exp) 𝚺 0 P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  order_induction_h 𝚺 0 hP ind

lemma least_number {P : M → Prop} (hP : DefinablePred ℒₒᵣ 𝚺 0 P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  least_number_h 𝚺 0 hP h

@[elab_as_elim] lemma hierarchy_polynomial_induction_oRing_pi₁ [M ⊧ₘ* 𝐈𝚷₁] {P : M → Prop} (hP : DefinablePred ℒₒᵣ 𝚷 1 P)
    (zero : P 0) (even : ∀ x > 0, P x → P (2 * x)) (odd : ∀ x, P x → P (2 * x + 1)) : ∀ x, P x :=
  hierarchy_polynomial_induction 𝚷 1 hP zero even odd

@[simp] lemma log_exponential (a : M) : log (exp a) = a := (exponential_exp a).log_eq_of_exp

lemma exp_log_le_self {a : M} (pos : 0 < a) : exp (log a) ≤ a := by
  rcases log_pos pos with ⟨_, _, H, _⟩
  rcases H.uniq (exponential_exp (log a))
  assumption

lemma lt_two_mul_exponential_log {a : M} (pos : 0 < a) : a < 2 * exp (log a) := by
  rcases log_pos pos with ⟨_, _, H, _⟩
  rcases H.uniq (exponential_exp (log a))
  assumption

@[simp] lemma length_exponential (a : M) : ‖exp a‖ = a + 1 := by
  simp [length_of_pos (exp_pos a)]

lemma exp_add (a b : M) : exp (a + b) = exp a * exp b :=
  Eq.symm <| exp_of_exponential (Exponential.add_mul (exponential_exp a) (exponential_exp b))

lemma log_mul_exp_add_of_lt {a b : M} (pos : 0 < a) (i : M) (hb : b < exp i) : log (a * exp i + b) = log a + i := by
  simp [log_mul_pow2_add_of_lt pos (exp_pow2 i) hb]

lemma log_mul_exp {a : M} (pos : 0 < a) (i : M) : log (a * exp i) = log a + i := by
  simp [log_mul_pow2 pos (exp_pow2 i)]

lemma length_mul_exp_add_of_lt {a b : M} (pos : 0 < a) (i : M) (hb : b < exp i) : ‖a * exp i + b‖ = ‖a‖ + i := by
  simp [length_mul_pow2_add_of_lt pos (exp_pow2 i) hb]

lemma length_mul_exp {a : M} (pos : 0 < a) (i : M) : ‖a * exp i‖ = ‖a‖ + i := by
  simp [length_mul_pow2 pos (exp_pow2 i)]

lemma exp_le_iff_le_log {i a : M} (pos : 0 < a) : exp i ≤ a ↔ i ≤ log a :=
  ⟨by intro h; simpa using log_monotone h, fun h ↦ le_trans (exp_monotone_le.mpr h) (exp_log_le_self pos)⟩

@[elab_as_elim] lemma polynomial_induction {P : M → Prop} (hP : DefinablePred ℒₒᵣ(exp) 𝚺 0 P)
    (zero : P 0) (even : ∀ x > 0, P x → P (2 * x)) (odd : ∀ x, P x → P (2 * x + 1)) : ∀ x, P x :=
  hierarchy_polynomial_induction 𝚺 0 hP zero even odd

end Model.EA

end

end Arith

end LO.FirstOrder
