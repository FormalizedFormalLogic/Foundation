import Foundation.FirstOrder.Arithmetic.Basic
import Foundation.FirstOrder.R0.Basic

/-!
# Robinson's theory $\mathsf{Q}$
-/

noncomputable section

namespace LO

open FirstOrder FirstOrder.Arithmetic

inductive RobinsonQ : ArithmeticTheory
  | equal : ∀ φ ∈ 𝐄𝐐, RobinsonQ φ
  | succNeZero : RobinsonQ “a | a + 1 ≠ 0”
  | succInj : RobinsonQ “a b | a + 1 = b + 1 → a = b”
  | addZero : RobinsonQ “a | a + 0 = a”
  | addSucc : RobinsonQ “a b | a + (b + 1) = (a + b) + 1”
  | mulZero : RobinsonQ “a | a * 0 = 0”
  | mulSucc : RobinsonQ “a b | a * (b + 1) = a * b + a”
  | zeroAddOne : RobinsonQ “0 + 1 = 1”

notation "𝐐" => RobinsonQ

namespace RobinsonQ

open ORingStruc

set_option linter.flexible false in
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

/-
instance : M ⊧ₘ* 𝐑₀ := modelsTheory_iff.mpr <| by
  intro φ h
  rcases h
  case equal h =>
    have : M ⊧ₘ* (𝐄𝐐 : ArithmeticTheory) := inferInstance
    exact modelsTheory_iff.mp this h
  case Ω₁ n m => simp [models_iff, numeral_add]
  case Ω₂ n m => simp [models_iff, numeral_mul]
  case Ω₃ n m h =>
    simp [models_iff]
  case Ω₄ n =>
    suffices ∀ x : M, x < ↑n ↔ ∃ i < n, x = ↑i by simpa [models_iff, numeral_eq_natCast];
    intro x
    constructor
    · intro hx; rcases eq_nat_of_lt_nat hx with ⟨x, rfl⟩; exact ⟨x, by simpa using hx, by simp⟩
    · rintro ⟨i, hi, rfl⟩; simp [hi]
-/



namespace Countermodel

abbrev OmegaAddOne := Option ℕ

namespace OmegaAddOne

variable {a b : OmegaAddOne} {m n : ℕ}

instance : NatCast OmegaAddOne := ⟨fun i ↦ .some i⟩

instance (n : ℕ) : OfNat OmegaAddOne n := ⟨.some n⟩

instance : Top OmegaAddOne := ⟨.none⟩

instance : ORingStruc OmegaAddOne where
  add a b :=
    match a, b with
    | .some n, .some m => some (n + m)
    |   .none,       _ => ⊤
    |       _,   .none => ⊤
  mul a b :=
    match a, b with
    | .some n, .some m => some (n * m)
    | .some 0, .none   => some 0
    | .none  , .some 0 => some 0
    | _      , _       => ⊤
  lt a b :=
    match a, b with
    | .some n, .some m => n < m
    |   .none,       _ => False
    | .some _,   .none => True

@[simp] lemma coe_zero : (↑(0 : ℕ) : OmegaAddOne) = 0 := rfl
@[simp] lemma coe_one : (↑(1 : ℕ) : OmegaAddOne) = 1 := rfl

@[simp] lemma coe_add (a b : ℕ) : ↑(a + b) = ((↑a + ↑b) : OmegaAddOne) := rfl


@[simp] lemma add_nat_nat {m n : ℕ} : (some m : OmegaAddOne) + (some n) = some (m + n) := by rfl;
@[simp] lemma add_nat_one : (some m : OmegaAddOne) + 1 = some (m + 1) := add_nat_nat

@[simp] lemma add_nat_zero : a + 0 = a := by match a with | ⊤ | .some n => rfl
@[simp] lemma add_nat_top : a + (⊤ : OmegaAddOne) = ⊤ := by match a with | ⊤ | .some n => rfl
@[simp] lemma add_top_nat : (⊤ : OmegaAddOne) + a = ⊤ := by match a with | ⊤ | .some n => rfl


@[simp] lemma mul_zero_top : (some 0) * (⊤ : OmegaAddOne) = some 0 := by rfl;
@[simp] lemma mul_succ_top : (some (n + 1) : OmegaAddOne) * ⊤ = ⊤ := by rfl;

@[simp] lemma mul_top_zero : (⊤ : OmegaAddOne) * 0 = 0 := by rfl;
@[simp] lemma mul_top_succ : (⊤ : OmegaAddOne) * (some (n + 1)) = ⊤ := by rfl;

@[simp] lemma mul_top_top : (⊤ : OmegaAddOne) * ⊤ = ⊤ := by rfl;

@[simp]
lemma mul_nat_nat : (some m : OmegaAddOne) * (some n) = some (m * n) := by
  match m, n with | 0, 0 | 0, n + 1 | m + 1, 0 | m + 1, n + 1 => rfl;

@[simp]
lemma mul_zero {n : OmegaAddOne} : n * 0 = 0 := by match n with | ⊤ | .some 0 | .some (n + 1) => rfl;

end OmegaAddOne

set_option linter.flexible false in
instance : OmegaAddOne ⊧ₘ* 𝐐 := ⟨by
  intro σ h;
  rcases h <;> simp [models_def];
  case equal h =>
    have : OmegaAddOne ⊧ₘ* (𝐄𝐐 : ArithmeticTheory) := inferInstance
    exact modelsTheory_iff.mp this h
  case zeroAddOne => rfl;
  case addSucc =>
    intro f;
    generalize f 0 = m;
    generalize f 1 = n;
    match m, n with
    | ⊤, _ | _, ⊤ => simp;
    | .some m, .some n => rfl;
  case mulSucc =>
    intro f;
    generalize f 0 = m;
    generalize f 1 = n;
    match m, n with
    | ⊤, ⊤ | some 0, ⊤ | ⊤, some 0 | some (m + 1), ⊤ | ⊤, some (n + 1) => simp;
    | .some m, .some n => simp; tauto;
  case succNeZero =>
    intro f;
    generalize f 0 = m;
    match m with
    | ⊤       => simp;
    | .some m => apply Option.mem_some_iff.not.mpr; simp;
  case succInj =>
    intro f;
    generalize f 0 = m;
    generalize f 1 = n;
    match m, n with
    | .some m, ⊤ | ⊤, .some n | ⊤, ⊤ => simp;
    | .some m, .some n => simp;
⟩

lemma unprovable_neSucc : 𝐐 ⊬ “x | x + 1 ≠ x” := unprovable_of_countermodel (M := OmegaAddOne) (fun x ↦ ⊤) _ (by simp)

end Countermodel

end RobinsonQ

end LO
