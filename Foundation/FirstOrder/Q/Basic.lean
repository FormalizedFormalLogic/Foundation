import Foundation.FirstOrder.Arithmetic.Basic
import Foundation.FirstOrder.R0.Basic

/-!
# Robinson's theory $\mathsf{Q}$
-/

noncomputable section

namespace LO

open FirstOrder FirstOrder.Arithmetic

inductive RobinsonQ : ArithmeticTheory
  | equal      : ∀ φ ∈ 𝐄𝐐, RobinsonQ φ
  | succNeZero : RobinsonQ   “a | a + 1 ≠ 0”
  | succInj    : RobinsonQ “a b | a + 1 = b + 1 → a = b”
  | addZero    : RobinsonQ   “a | a + 0 = a”
  | addSucc    : RobinsonQ “a b | a + (b + 1) = (a + b) + 1”
  | mulZero    : RobinsonQ   “a | a * 0 = 0”
  | mulSucc    : RobinsonQ “a b | a * (b + 1) = a * b + a”
  | zeroAddOne : RobinsonQ “0 + 1 = 1”

notation "𝐐" => RobinsonQ

namespace RobinsonQ

open ORingStruc

@[simp] instance : ℕ ⊧ₘ* 𝐐 := ⟨by
  intro σ h
  rcases h <;> simp [models_def, add_assoc, mul_add]
  case equal h =>
    have : ℕ ⊧ₘ* (𝐄𝐐 : ArithmeticTheory) := inferInstance
    exact modelsTheory_iff.mp this h⟩

instance : 𝐄𝐐 ⪯ 𝐐 := Entailment.WeakerThan.ofSubset <| fun φ hp ↦ equal φ hp

variable {M : Type*} [ORingStruc M] [M ⊧ₘ* 𝐐]

@[simp] protected lemma succ_ne_zero (a : M) : a + 1 ≠ 0 := by
  simpa [models_iff] using ModelsTheory.models M RobinsonQ.succNeZero (fun _ ↦ a)

lemma succ_inj {a b : M} : a + 1 = b + 1 → a = b := by
  simpa [models_iff] using ModelsTheory.models M RobinsonQ.succInj (a :>ₙ fun _ ↦ b)

@[simp] protected lemma add_zero (a : M) : a + 0 = a := by
  simpa [models_iff] using ModelsTheory.models M RobinsonQ.addZero (fun _ ↦ a)

protected lemma add_succ (a b : M) : a + (b + 1) = a + b + 1 := by
  simpa [models_iff] using ModelsTheory.models M RobinsonQ.addSucc (a :>ₙ fun _ ↦ b)

@[simp] protected lemma mul_zero (a : M) : a * 0 = 0 := by
  simpa [models_iff] using ModelsTheory.models M RobinsonQ.mulZero (fun _ ↦ a)

protected lemma mul_succ (a b : M) : a * (b + 1) = a * b + a := by
  simpa [models_iff] using ModelsTheory.models M RobinsonQ.mulSucc (a :>ₙ fun _ ↦ b)

@[simp] protected lemma zero_add_one : (0 + 1 : M) = 1 := by
  simpa [models_iff] using ModelsTheory.models M RobinsonQ.zeroAddOne (fun _ ↦ 0)

@[simp] lemma numeral_zero_add (n : ℕ) : 0 + (numeral n : M) = numeral n := by
  match n with
  |     0 => simp
  |     1 => simp
  | n + 2 => simp [ORingStruc.numeral, RobinsonQ.add_succ, numeral_zero_add (n + 1)]

@[simp] lemma zero_mul_one : (0 : M) * 1 = 0 := calc
   (0 : M) * 1 = 0 * (0 + 1) := by simp
    _          = 0 * 0 + 0   := by rw [RobinsonQ.mul_succ]
    _          = 0           := by simp

@[simp] lemma numeral_zero_mul (n : ℕ) : 0 * (numeral n : M) = 0 := by
  match n with
  |     0 => simp
  |     1 => simp
  | n + 2 => calc
    (0 : M) * numeral (n + 2) = 0 * (numeral (n + 1) + 1) := rfl
    _                         = 0 * numeral (n + 1) + 0   := by rw [RobinsonQ.mul_succ]
    _                         = 0                         := by simp [numeral_zero_mul (n + 1)]

@[simp] lemma one_mul_one : (1 : M) * 1 = 1 := calc
  (1 : M) * 1 = 1 * (0 + 1) := by simp
  _           = 1 * 0 + 1   := by rw [RobinsonQ.mul_succ]
  _           = 1           := by simp

@[simp] lemma mul_one (n : ℕ) : (numeral n : M) * 1 = numeral n := calc
  (numeral n : M) * 1 = numeral n * (0 + 1)       := by simp
  _                   = numeral n * 0 + numeral n := by rw [RobinsonQ.mul_succ]
  _                   = numeral n                 := by simp

lemma numeral_add_one (n : ℕ) : (numeral n : M) + 1 = numeral (n + 1) := by
  match n with
  |     0 => simp
  | n + 1 => rfl

lemma numeral_add (n m : ℕ) : (numeral n : M) + numeral m = numeral (n + m) := by
  match m with
  |     0 => simp
  |     1 => simp [numeral_add_one]
  | m + 2 => calc
    (numeral n : M) + (numeral (m + 1) + 1) = (numeral n + numeral (m + 1)) + 1 := RobinsonQ.add_succ _ _
    _                                       = numeral (n + (m + 1)) + 1         := by rw [numeral_add n (m + 1)]
    _                                       = numeral (n + (m + 2))             := by simp [←add_assoc]; rfl

lemma numeral_mul (n m : ℕ) : (numeral n : M) * numeral m = numeral (n * m) := by
  match m with
  |     0 => simp
  |     1 => simp
  | m + 2 => calc
    (numeral n : M) * (numeral (m + 1) + 1) = numeral n * numeral (m + 1) + numeral n := by rw [RobinsonQ.mul_succ]
    _                                       = numeral (n * (m + 1)) + numeral n       := by rw [numeral_mul n (m + 1)]
    _                                       = numeral (n * (m + 2))                   := by simp [numeral_add, mul_add, mul_two, ←add_assoc]

@[simp] lemma zero_ne_one : (0 : M) ≠ 1 := calc
  (0 : M) ≠ 0 + 1 := Ne.symm <| RobinsonQ.succ_ne_zero 0
  _       = 1     := by simp

lemma numeral_succ_ne {n : ℕ} : (numeral n : M) ≠ numeral (n + 1) := by
  match n with
  |     0 => simp
  |     1 => calc
    (1 : M) = 0 + 1 := by simp
    _       ≠ 1 + 1 := fun e ↦ zero_ne_one (RobinsonQ.succ_inj e)
  | n + 2 =>
    intro e
    exact numeral_succ_ne (RobinsonQ.succ_inj e)

lemma numeral_zero_succ_ne {n : ℕ} : (numeral 0 : M) ≠ (numeral (n + 1))  := by
  apply Ne.symm;
  simp [←numeral_add];

lemma exists_numeral_of_ne_zero {n : ℕ} (h : n ≠ 0) : ∃ m, (numeral n : M) = (numeral (m + 1)) := by
  match n with
  |     0 => contradiction
  |     1 => use 0;
  | n + 2 =>
    obtain ⟨m, hm⟩ := exists_numeral_of_ne_zero (n := n + 1) (by omega);
    use m + 1;
    calc
      numeral (n + 2) = numeral (n + 1 + 1)               := by simp;
                    _ = numeral (n + 1) + numeral 1       := by simp [numeral_add_one];
                    _ = numeral (m + 1) + numeral 1       := by rw [hm];

lemma numeral_ne_of_ne_zero {n : ℕ} (h : m ≠ 0) : (numeral n : M) ≠ numeral (n + m)  := by
  match m with
  | 0 => contradiction
  | 1 => apply numeral_succ_ne;
  | m + 2 =>
    by_contra e;
    sorry;
  /-
  | 1 => apply numeral_succ_ne
  | m + 2 =>
    by_contra e;

    sorry;
  -/

lemma numeral_succ_inj {n m : ℕ} (h : (numeral (n + 1) : M) = numeral (m + 1)) : (numeral n : M) = (numeral m : M) := by
  rw [←numeral_add_one, ←numeral_add_one] at h;
  apply succ_inj h;

lemma numeral_ne_of_ne {n m : ℕ} (h : n ≠ m) : (numeral n : M) ≠ numeral m := by
  match n, m with
  | 0, m =>
    obtain ⟨k, hk⟩ := exists_numeral_of_ne_zero (M := M) h.symm;
    rw [hk];
    exact numeral_zero_succ_ne;
  | n + 1, 0 =>
    apply Ne.symm;
    exact numeral_zero_succ_ne;
  | n + 1, m + 1 =>
    have := numeral_ne_of_ne (n := n) (m := m) (by omega);
    contrapose! this;
    apply numeral_succ_inj this;

instance : M ⊧ₘ* 𝐑₀ := modelsTheory_iff.mpr <| by
  intro φ h
  rcases h
  case equal h =>
    have : M ⊧ₘ* (𝐄𝐐 : ArithmeticTheory) := inferInstance
    exact modelsTheory_iff.mp this h
  case Ω₁ n m => simp [models_iff, numeral_add]
  case Ω₂ n m => simp [models_iff, numeral_mul]
  case Ω₃ n m h => simp [models_iff, numeral_ne_of_ne h];
  case Ω₄ n =>
    suffices ∀ (x : M), x < numeral n ↔ ∃ i < n, x = numeral i by simpa [models_iff];
    intro x;
    constructor;
    . intro hx;
      rcases eq_nat_of_lt_nat hx with ⟨x, rfl⟩;
      sorry;
    . rintro ⟨i, hi, rfl⟩;
      sorry;

instance : 𝐑₀ ⪯ 𝐐 := oRing_weakerThan_of.{0} _ _ fun _ _ _ ↦ inferInstance

instance : 𝐑₀ ⪱ 𝐐 :=
  Entailment.StrictlyWeakerThan.of_unprovable_provable
    R0.unprovable_addZero (Entailment.by_axm _ RobinsonQ.addZero)

end RobinsonQ
