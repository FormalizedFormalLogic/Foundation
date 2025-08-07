import Foundation.FirstOrder.Arithmetic.Basic
import Foundation.FirstOrder.R0.Basic
import Mathlib.Data.ENat.Basic

/-!
# Robinson's theory $\mathsf{Q}$
-/

noncomputable section

namespace LO

open FirstOrder FirstOrder.Arithmetic

inductive RobinsonQ : ArithmeticTheory
  | equal          : ∀ φ ∈ 𝐄𝐐, RobinsonQ φ
  | succNeZero     : RobinsonQ   “a | a + 1 ≠ 0”
  | succInj        : RobinsonQ “a b | a + 1 = b + 1 → a = b”
  | zeroOrSucc     : RobinsonQ   “a | a = 0 ∨ ∃ b, a = b + 1”
  | addZero        : RobinsonQ   “a | a + 0 = a”
  | addSucc        : RobinsonQ “a b | a + (b + 1) = (a + b) + 1”
  | mulZero        : RobinsonQ   “a | a * 0 = 0”
  | mulSucc        : RobinsonQ “a b | a * (b + 1) = a * b + a”
  | ltDef          : RobinsonQ “a b | a < b ↔ ∃ c, a + (c + 1) = b”

notation "𝐐" => RobinsonQ

namespace RobinsonQ

open ORingStruc

@[simp] instance : ℕ ⊧ₘ* 𝐐 := ⟨by
  intro σ h
  rcases h <;> simp [models_def, add_assoc, mul_add]
  case ltDef =>
    intro f;
    constructor;
    . intro h;
      use (f 1 - f 0 - 1);
      omega;
    . rintro ⟨c, hc⟩;
      simp [←hc];
  case zeroOrSucc => omega;
  case equal h =>
    have : ℕ ⊧ₘ* (𝐄𝐐 : ArithmeticTheory) := inferInstance
    exact modelsTheory_iff.mp this h⟩

instance : 𝐄𝐐 ⪯ 𝐐 := Entailment.WeakerThan.ofSubset <| fun φ hp ↦ equal φ hp

variable {M : Type*} [ORingStruc M] [M ⊧ₘ* 𝐐]

@[simp] protected lemma succ_ne_zero (a : M) : a + 1 ≠ 0 := by
  simpa [models_iff] using ModelsTheory.models M RobinsonQ.succNeZero (fun _ ↦ a)

lemma succ_inj {a b : M} : a + 1 = b + 1 → a = b := by
  simpa [models_iff] using ModelsTheory.models M RobinsonQ.succInj (a :>ₙ fun _ ↦ b)

@[simp] protected lemma add_zero {a : M} : a + 0 = a := by
  simpa [models_iff] using ModelsTheory.models M RobinsonQ.addZero (fun _ ↦ a)

protected lemma add_succ (a b : M) : a + (b + 1) = a + b + 1 := by
  simpa [models_iff] using ModelsTheory.models M RobinsonQ.addSucc (a :>ₙ fun _ ↦ b)

@[simp] protected lemma mul_zero (a : M) : a * 0 = 0 := by
  simpa [models_iff] using ModelsTheory.models M RobinsonQ.mulZero (fun _ ↦ a)

protected lemma mul_succ (a b : M) : a * (b + 1) = a * b + a := by
  simpa [models_iff] using ModelsTheory.models M RobinsonQ.mulSucc (a :>ₙ fun _ ↦ b)

lemma zero_or_succ {a : M} : a = 0 ∨ ∃ b : M, a = b + 1 := by
  simpa [models_iff] using ModelsTheory.models M RobinsonQ.zeroOrSucc (λ _ ↦ a);

lemma exists_succ_of_ne_zero {a : M} (ha : a ≠ 0) : ∃ b : M, a = b + 1 := by
  have := zero_or_succ (a := a);
  tauto;

lemma exists_succ_of_ne_zero' {a : M} (ha : a ≠ 0) : ∃ b : M, b + 1 = a := by
  obtain ⟨b, rfl⟩ := exists_succ_of_ne_zero ha;
  use b;

protected lemma lt_def {a b : M} : a < b ↔ ∃ c : M, a + (c + 1) = b := by
  simpa [models_iff] using ModelsTheory.models M RobinsonQ.ltDef (a :>ₙ fun _ ↦ b)

@[simp]
lemma one_ne_zero : (1 : M) ≠ 0 := by
  by_contra h;
  apply RobinsonQ.succ_ne_zero (M := M) (a := 0);
  rw [h];
  apply RobinsonQ.add_zero;

@[simp]
lemma one_add_zero : (1 : M) + 0 = 1 := by simp;

@[simp]
lemma zero_add_one : (0 : M) + 1 = 1 := by
  obtain ⟨a, ha⟩ := exists_succ_of_ne_zero' (M := M) one_ne_zero;
  convert ha;
  by_contra;
  obtain ⟨b, rfl⟩ := exists_succ_of_ne_zero' (M := M) (a := a) (by tauto);
  apply RobinsonQ.succ_ne_zero (M := M) (a := (0 + b));
  apply succ_inj;
  calc
    0 + b + 1 + 1 = 0 + (b + 1) + 1 := by rw [RobinsonQ.add_succ (a := 0) (b := b)];
    _             = 0 + (b + 1 + 1) := by rw [RobinsonQ.add_succ (a := 0) (b := (b + 1))];
    _             = 0 + 1           := by rw [ha];

lemma succ_inj_zero {a : M} : a + 1 = 1 → a = 0 := by
  nth_rw 2 [←zero_add_one];
  apply succ_inj;

@[simp]
lemma one_mul_one : (1 : M) * 1 = 1 := calc
  (1 : M) * 1 = 1 * (0 + 1) := by simp
  _           = 1 * 0 + 1   := by rw [RobinsonQ.mul_succ]
  _           = 1           := by simp

@[simp]
lemma zero_mul_one : (0 : M) * 1 = 0 := calc
   (0 : M) * 1 = 0 * (0 + 1) := by simp
    _          = 0 * 0 + 0   := by rw [RobinsonQ.mul_succ]
    _          = 0           := by simp

@[simp] lemma numeral_zero_add (n : ℕ) : 0 + (numeral n : M) = numeral n := by
  match n with
  |     0 => simp
  |     1 => simp
  | n + 2 => simp [ORingStruc.numeral, RobinsonQ.add_succ, numeral_zero_add (n + 1)]

lemma numeral_add_one (n : ℕ) : (numeral n : M) + 1 = numeral (n + 1) := by
  match n with
  |     0 => simp;
  | n + 1 => rfl

lemma numeral_add (n m : ℕ) : (numeral n : M) + numeral m = numeral (n + m) := by
  match m with
  |     0 => simp
  |     1 => simp [numeral_add_one]
  | m + 2 => calc
    (numeral n : M) + (numeral (m + 1) + 1) = (numeral n + numeral (m + 1)) + 1 := RobinsonQ.add_succ _ _
    _                                       = numeral (n + (m + 1)) + 1         := by rw [numeral_add n (m + 1)]
    _                                       = numeral (n + (m + 2))             := by simp [←add_assoc]; rfl


lemma numeral_zero_mul {n : ℕ} : 0 * (numeral n : M) = 0 := by
  match n with
  |     0 => simp
  |     1 => simp
  | n + 2 => calc
    (0 : M) * numeral (n + 2) = 0 * (numeral (n + 1) + 1) := rfl
    _                         = 0 * numeral (n + 1) + 0   := by rw [RobinsonQ.mul_succ]
    _                         = 0                         := by simp [numeral_zero_mul]

lemma numeral_mul_one {n : ℕ} : (numeral n : M) * 1 = numeral n := calc
  (numeral n : M) * 1 = numeral n * (0 + 1)       := by simp
  _                   = numeral n * 0 + numeral n := by rw [RobinsonQ.mul_succ]
  _                   = numeral n                 := by simp

lemma numeral_mul {n m : ℕ} : (numeral n : M) * numeral m = numeral (n * m) := by
  match m with
  |     0 => simp
  |     1 => simp [numeral_mul_one]
  | m + 2 => calc
    (numeral n : M) * (numeral (m + 1) + 1) = numeral n * numeral (m + 1) + numeral n := by rw [RobinsonQ.mul_succ]
    _                                       = numeral (n * (m + 1)) + numeral n       := by rw [numeral_mul]
    _                                       = numeral (n * (m + 2))                   := by simp [numeral_add, mul_add, mul_two, ←add_assoc]

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

lemma numeral_zero_succ_ne {n : ℕ} : (numeral 0 : M) ≠ (numeral (n + 1))  := by
  apply Ne.symm;
  simp [←numeral_add];


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

@[simp]
lemma not_le_zero {a : M} : ¬a < 0 := by
  apply RobinsonQ.lt_def.not.mpr;
  push_neg;
  intro b;
  calc
    a + (b + 1) = (a + b) + 1 := RobinsonQ.add_succ _ _
    _           ≠ 0           := by simp;

lemma eq_zero_of_eq_add_zero {a b : M} (h : a + b = 0) : a = 0 ∧ b = 0 := by
  set_option push_neg.use_distrib true in contrapose! h;
  rcases h with ha | hb;
  . obtain ⟨c, rfl⟩ := exists_succ_of_ne_zero (M := M) ha;
    by_cases hb0 : b = 0;
    . subst hb0; rwa [RobinsonQ.add_zero]
    . obtain ⟨d, rfl⟩ := exists_succ_of_ne_zero (M := M) hb0;
      rw [RobinsonQ.add_succ (a := c + 1) (b := d)];
      apply RobinsonQ.succ_ne_zero;
  . obtain ⟨c, rfl⟩ := exists_succ_of_ne_zero' (M := M) hb;
    rw [RobinsonQ.add_succ];
    simp;

lemma lt_of_not_zero {a b : M} (ha : b ≠ 0) : a < a + b := by
  apply RobinsonQ.lt_def.mpr;
  obtain ⟨b, rfl⟩ := exists_succ_of_ne_zero (M := M) ha;
  use b;

@[simp]
lemma iff_le_one_eq_zero {a : M} : a < 1 ↔ a = 0 := by
  constructor;
  . rw [RobinsonQ.lt_def];
    rintro ⟨b, hb⟩;
    apply eq_zero_of_eq_add_zero (b := b) ?_ |>.1;
    apply succ_inj_zero;
    rwa [RobinsonQ.add_succ] at hb;
  . rintro rfl;
    apply RobinsonQ.lt_def.mpr;
    use 0;
    simp;

lemma eq_numeral_add_one : (numeral m) + 1 = numeral (m + 1) := by simp;

lemma numeral_lt_of_lt {n m : ℕ} (h : n < m) : (numeral n : M) < numeral m := by
  apply RobinsonQ.lt_def.mpr;
  obtain ⟨k, rfl, hk⟩ := RobinsonQ.lt_def.mp h;
  use (numeral k : M);
  calc
    (numeral n + (numeral k + 1) : M) = numeral n + (numeral k + numeral 1) := by simp;
                                    _ = numeral n + (numeral (k + 1))       := by rw [numeral_add];
                                    _ = numeral (n + (k + 1))               := by rw [numeral_add];

lemma numeral_lt_add {n m : ℕ} (hm : m ≠ 0) : (numeral n : M) < numeral n + numeral m := by
  rw [numeral_add];
  apply numeral_lt_of_lt;
  omega;

@[simp]
lemma numeral_lt_succ {n : ℕ} : (numeral n : M) < numeral n + numeral 1 := numeral_lt_add $ by omega;

lemma numeral_lt_add' {n : ℕ} {b : M} (hm : b ≠ 0) : (numeral n : M) < numeral n + b := by
  apply RobinsonQ.lt_def.mpr;
  obtain ⟨b, rfl⟩ := exists_succ_of_ne_zero (M := M) hm;
  use b;

lemma iff_lt_numeral_exists_numeral {n : ℕ} {x : M} : x < numeral n ↔ ∃ m < n, x = numeral m := by
  match n with
  | 0 => simp;
  | 1 => simp;
  | n + 2 =>
    constructor;
    . intro h;
      obtain ⟨a, ha⟩ := RobinsonQ.lt_def.mp h;
      by_cases ha0 : a = 0;
      . use n + 1;
        subst ha0;
        constructor;
        . omega;
        . apply succ_inj;
          simpa using ha;
      . obtain ⟨m, hm, rfl⟩ := iff_lt_numeral_exists_numeral (x := x) (n := n + 1) |>.mp $ by
          have ha : x + a = numeral (n + 1) := succ_inj $ by rwa [RobinsonQ.add_succ] at ha;
          rw [←ha];
          apply lt_of_not_zero ha0;
        use m;
        constructor;
        . omega;
        . rfl;
    . rintro ⟨m, hm, rfl⟩;
      apply numeral_lt_of_lt;
      exact hm;

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
    apply iff_lt_numeral_exists_numeral;

instance : 𝐑₀ ⪯ 𝐐 := oRing_weakerThan_of.{0} _ _ fun _ _ _ ↦ inferInstance

instance : 𝐑₀ ⪱ 𝐐 :=
  Entailment.StrictlyWeakerThan.of_unprovable_provable
    R0.unprovable_addZero (Entailment.by_axm _ RobinsonQ.addZero)

end RobinsonQ

end LO
