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

instance exp_definable_oRingExp : DefinableFunction₁ ℒₒᵣ(exp) Σ 0 (Exp.exp : M → M) where
  definable := ⟨⟨“#0 = exp #1”, by simp⟩, by intro _; simp⟩

instance exp_bounded_oRingExp : Bounded₁ ℒₒᵣ(exp) (Exp.exp : M → M) where
  bounded := ⟨ᵀ“exp #0”, by intro _; simp⟩

@[elab_as_elim] lemma induction_EA
    {P : M → Prop} (hP : DefinablePred ℒₒᵣ(exp) Σ 0 P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := induction_h Σ 0 hP zero succ

lemma exponential_exp (a : M) : Exponential a (exp a) := by
  induction a using induction_EA
  · definability
  case zero => simp
  case succ a ih =>
    simp [exp_succ, Exponential.exponential_succ_mul_two, ih]

lemma exponential_graph {a b : M} : a = exp b ↔ Exponential b a :=
  ⟨by rintro rfl; exact exponential_exp b, fun h ↦ Exponential.uniq h (exponential_exp b)⟩

@[simp] lemma exp_monotone {a b : M} : exp a < exp b ↔ a < b :=
  Iff.symm <| Exponential.monotone_iff (exponential_exp a) (exponential_exp b)

@[simp] lemma exp_monotone_le {a b : M} : exp a ≤ exp b ↔ a ≤ b :=
  Iff.symm <| Exponential.monotone_le_iff (exponential_exp a) (exponential_exp b)

instance : Structure.Monotone ℒₒᵣ(exp) M := ⟨
  fun {k} f v₁ v₂ h ↦
  match k, f with
  | 0, Language.Zero.zero => by rfl
  | 0, Language.One.one   => by rfl
  | 2, Language.Add.add   => add_le_add (h 0) (h 1)
  | 2, Language.Mul.mul   => mul_le_mul (h 0) (h 1) (by simp) (by simp)
  | 1, Language.Exp.exp   => by simpa using h 0⟩

@[elab_as_elim] lemma order_induction
    {P : M → Prop} (hP : DefinablePred ℒₒᵣ(exp) Σ 0 P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  order_induction_h Σ 0 hP ind

lemma least_number {P : M → Prop} (hP : DefinablePred ℒₒᵣ Σ 0 P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  least_number_h Σ 0 hP h

example : 4 + 5 * 9 = 49 := by simp

/-
namespace ArithmetizedTerm

variable (L : Language) [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)]

variable (M)

class ArithmetizedLanguage where
  isFunc : Δ₀(exp)-Sentence 2
  isFunc_spec : DefinedRel ℒₒᵣ(exp) Σ 0 (fun (k' f' : M) ↦ ∃ (k : ℕ) (f : L.Func k), k' = k ∧ f' = Encodable.encode f) isFunc
  isRel : Δ₀(exp)-Sentence 2
  isRel_spec : DefinedRel ℒₒᵣ(exp) Σ 0 (fun (k' r' : M) ↦ ∃ (k : ℕ) (r : L.Rel k), k' = k ∧ r' = Encodable.encode r) isRel

variable {M L}

def bvar (x : M) : M := ⟪0, ⟪0, x⟫⟫

def fvar (x : M) : M := ⟪0, ⟪1, x⟫⟫

def func : {k : ℕ} → (f : L.Func k) → M
  | k, f => ⟪k, ⟪2, Encodable.encode f⟫⟫

end ArithmetizedTerm
-/

end Model.EA

end

end Arith

end LO.FirstOrder
