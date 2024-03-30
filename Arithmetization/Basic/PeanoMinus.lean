import Arithmetization.Definability.Definability

namespace LO.FirstOrder

namespace Arith

noncomputable section

variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐏𝐀⁻]

namespace Model

variable {a b c : M}

section sub

lemma sub_existsUnique (a b : M) : ∃! c, (a ≥ b → a = b + c) ∧ (a < b → c = 0) := by
  have : b ≤ a ∨ a < b := le_or_lt b a
  rcases this with (hxy | hxy) <;> simp [hxy]
  have : ∃ c, a = b + c := exists_add_of_le hxy
  rcases this with ⟨c, rfl⟩
  exact ExistsUnique.intro c rfl (fun a h => (add_left_cancel h).symm)

def sub (a b : M) : M := Classical.choose! (sub_existsUnique a b)

instance : Sub M := ⟨sub⟩

lemma sub_spec_of_ge (h : a ≥ b) : a = b + (a - b) := (Classical.choose!_spec (sub_existsUnique a b)).1 h

lemma sub_spec_of_lt (h : a < b) : a - b = 0 := (Classical.choose!_spec (sub_existsUnique a b)).2 h

lemma sub_eq_iff : c = a - b ↔ ((a ≥ b → a = b + c) ∧ (a < b → c = 0)) := Classical.choose!_eq_iff (sub_existsUnique a b)

@[simp] lemma sub_le_self (a b : M) : a - b ≤ a := by
  have : b ≤ a ∨ a < b := le_or_lt b a
  rcases this with (hxy | hxy) <;> simp[hxy]
  · simpa [← sub_spec_of_ge hxy] using show a - b ≤ b + (a - b) from le_add_self
  · simp[sub_spec_of_lt hxy]

open Definability

def subDef : Δ₀-Sentence 3 :=
  ⟨“(#2 ≤ #1 → #1 = #2 + #0) ∧ (#1 < #2 → #0 = 0)”, by simp[Hierarchy.pi_zero_iff_sigma_zero]⟩

lemma sub_defined : Δ₀-Function₂ ((· - ·) : M → M → M) via subDef := by
  intro v; simp [subDef, sub_eq_iff]

instance sub_definable (Γ s) : DefinableFunction₂ ℒₒᵣ Γ s ((· - ·) : M → M → M) := defined_to_with_param₀ subDef sub_defined

instance sub_polybounded : PolyBounded₂ ℒₒᵣ ((· - ·) : M → M → M) := ⟨#0, λ _ ↦ by simp⟩

@[simp] lemma sub_self (a : M) : a - a = 0 :=
  add_right_eq_self.mp (sub_spec_of_ge (a := a) (b := a) (by rfl)).symm

lemma sub_spec_of_le (h : a ≤ b) : a - b = 0 := by
  rcases lt_or_eq_of_le h with (lt | rfl) <;> simp [sub_spec_of_lt, *]

lemma sub_add_self_of_le (h : b ≤ a) : a - b + b = a := by symm; rw [add_comm]; exact sub_spec_of_ge h

lemma add_tsub_self_of_le (h : b ≤ a) : b + (a - b) = a := by symm; exact sub_spec_of_ge h

@[simp] lemma add_sub_self : (a + b) - b = a := by
  symm; simpa [add_comm b] using sub_spec_of_ge (@le_add_self _ _ b a)

@[simp] lemma add_sub_self' : (b + a) - b = a := by simp [add_comm]

@[simp] lemma zero_sub (a : M) : 0 - a = 0 := sub_spec_of_le (by simp)

@[simp] lemma sub_zero (a : M) : a - 0 = a := by
  simpa using sub_add_self_of_le (show 0 ≤ a from zero_le a)

lemma sub_remove_left (e : a = b + c) : a - c = b := by simp[e]

lemma sub_sub : a - b - c = a - (b + c) := by
  by_cases ha : b + c ≤ a
  · exact sub_remove_left <| sub_remove_left <| by
      simp [add_assoc, show c + b = b + c from add_comm _ _, sub_add_self_of_le, ha]
  · simp [sub_spec_of_lt (show a < b + c from not_le.mp ha)]
    by_cases hc : c ≤ a - b
    · by_cases hb : b ≤ a
      · have : a < a := calc
          a < b + c       := not_le.mp ha
          _ ≤ b + (a - b) := by simp[hc]
          _ = a           := add_tsub_self_of_le hb
        simp at this
      · simp [show a - b = 0 from sub_spec_of_lt (not_le.mp hb)]
    · exact sub_spec_of_lt (not_le.mp hc)

@[simp] lemma pos_sub_iff_lt : 0 < a - b ↔ b < a :=
  ⟨by contrapose; simp; exact sub_spec_of_le,
   by intro h; by_contra hs
      simp at hs
      have : a = b := by simpa [hs] using sub_spec_of_ge (show b ≤ a from LT.lt.le h)
      simp [this] at h⟩

@[simp] lemma sub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b :=
  not_iff_not.mp (by simp [←pos_iff_ne_zero])

instance : OrderedSub M where
  tsub_le_iff_right := by
    intro a b c
    by_cases h : b ≤ a
    · calc
        a - b ≤ c ↔ (a - b) + b ≤ c + b := by simp
        _         ↔ a ≤ c + b           := by rw [sub_add_self_of_le h]
    · simp [sub_spec_of_lt (show a < b from by simpa using h)]
      exact le_trans (le_of_lt $ show a < b from by simpa using h) (by simp)

lemma zero_or_succ (a : M) : a = 0 ∨ ∃ a', a = a' + 1 := by
  rcases zero_le a with (rfl | pos)
  · simp
  · right; exact ⟨a - 1, by rw [sub_add_self_of_le]; simp [pos_iff_one_le.mp pos]⟩

lemma pred_lt_self_of_pos (h : 0 < a) : a - 1 < a := by
  rcases zero_or_succ a with (rfl | ⟨a, rfl⟩)
  · simp_all
  · simp

lemma tsub_lt_iff_left (h : b ≤ a) : a - b < c ↔ a < c + b := AddLECancellable.tsub_lt_iff_right (add_le_cancel b) h

lemma sub_mul (h : b ≤ a) : (a - b) * c = a * c - b * c := by
  have : a = (a - b) + b := (tsub_eq_iff_eq_add_of_le h).mp rfl
  calc
    (a - b) * c = (a - b) * c + b * c - b * c := by simp
    _           = (a - b + b) * c - b * c     := by simp [add_mul]
    _           = a * c - b * c               := by simp [sub_add_self_of_le h]

lemma mul_sub (h : b ≤ a) : c * (a - b) = c * a - c * b := by simp [mul_comm c, sub_mul, h]

lemma add_sub_of_le (h : c ≤ b) (a : M) : a + b - c = a + (b - c) := add_tsub_assoc_of_le h a

end sub

section Dvd

lemma le_mul_self_of_pos_left (hy : 0 < b) : a ≤ b * a := by
  have : 1 * a ≤ b * a := mul_le_mul_of_nonneg_right (one_le_of_zero_lt b hy) (by simp)
  simpa using this

lemma le_mul_self_of_pos_right (hy : 0 < b) : a ≤ a * b := by
  simpa [mul_comm a b] using le_mul_self_of_pos_left hy

lemma dvd_iff_bounded {a b : M} : a ∣ b ↔ ∃ c ≤ b, b = a * c := by
  by_cases hx : a = 0
  · simp[hx]; rintro rfl; exact ⟨0, by simp⟩
  · constructor
    · rintro ⟨c, rfl⟩; exact ⟨c, le_mul_self_of_pos_left (pos_iff_ne_zero.mpr hx), rfl⟩
    · rintro ⟨c, hz, rfl⟩; exact dvd_mul_right a c

def dvdDef : Δ₀-Sentence 2 := ⟨“∃[#0 < #2 + 1] #2 = #1 * #0”, by simp⟩

lemma dvd_defined : Δ₀-Relation (λ a b : M ↦ a ∣ b) via dvdDef :=
  λ v ↦ by simp[dvd_iff_bounded, Matrix.vecHead, Matrix.vecTail, le_iff_lt_succ, dvdDef]

instance dvd_definable (Γ s) : DefinableRel ℒₒᵣ Γ s ((· ∣ ·) : M → M → Prop) := defined_to_with_param₀ _ dvd_defined

end Dvd

lemma le_of_dvd (h : 0 < b) : a ∣ b → a ≤ b := by
  rintro ⟨c, rfl⟩
  exact le_mul_self_of_pos_right
    (pos_iff_ne_zero.mpr (show c ≠ 0 from by rintro rfl; simp at h))

lemma not_dvd_of_lt (pos : 0 < b) : b < a → ¬a ∣ b := by
  intro hb h; exact not_le.mpr hb (le_of_dvd pos h)

lemma dvd_antisymm : a ∣ b → b ∣ a → a = b := by
  intro hx hy
  rcases show a = 0 ∨ 0 < a from eq_zero_or_pos a with (rfl | ltx)
  · simp [show b = 0 from by simpa using hx]
  · rcases show b = 0 ∨ 0 < b from eq_zero_or_pos b with (rfl | lty)
    · simp [show a = 0 from by simpa using hy]
    · exact le_antisymm (le_of_dvd lty hx) (le_of_dvd ltx hy)

lemma dvd_one_iff : a ∣ 1 ↔ a = 1 := ⟨by { intro hx; exact dvd_antisymm hx (by simp) }, by rintro rfl; simp⟩

theorem units_eq_one (u : Mˣ) : u = 1 :=
  Units.ext <| dvd_one_iff.mp ⟨u.inv, u.val_inv.symm⟩

@[simp] lemma unit_iff_eq_one {a : M} : IsUnit a ↔ a = 1 :=
  ⟨by rintro ⟨u, rfl⟩; simp [units_eq_one u], by rintro rfl; simp⟩

section Prime

lemma eq_one_or_eq_of_dvd_of_prime {p a : M} (pp : Prime p) (hxp : a ∣ p) : a = 1 ∨ a = p := by
  have : p ∣ a ∨ a ∣ 1 := pp.left_dvd_or_dvd_right_of_dvd_mul (show a ∣ p * 1 from by simpa using hxp)
  rcases this with (hx | hx)
  · right; exact dvd_antisymm hxp hx
  · left; exact dvd_one_iff.mp hx

/-
lemma irreducible_iff_bounded {a : M} : Irreducible a ↔ 1 < a ∧ ∀ b ≤ a, (b ∣ a → b = 1 ∨ b = a) := by
  constructor
  · intro ha
    have : 1 < a := by
      by_contra A
      simp [Irreducible.ne_one ha, Irreducible.ne_zero ha, le_one_iff_eq_zero_or_one] at A
    exact ⟨this, by {  }⟩

lemma prime_iff_bounded {a : M} : Prime a ↔ 1 < a ∧ ∀ b ≤ a, (b ∣ a → b = 1 ∨ b = a) := by
  constructor
  · intro prim
    have : 1 < a := by
      by_contra A; simp at A
      rcases le_one_iff_eq_zero_or_one.mp A with (rfl | rfl)
      · exact not_prime_zero prim
      · exact not_prime_one prim
    exact ⟨this, fun b hy hyx ↦ eq_one_or_eq_of_dvd_of_prime prim hyx⟩
  · intro H; constructor
    · sorry
    · constructor
      · sorry
      · intro b c h
-/

def IsPrime (a : M) : Prop := 1 < a ∧ ∀ b ≤ a, (b ∣ a → b = 1 ∨ b = a)
-- TODO: prove IsPrime a ↔ Prime a

def isPrimedef : Δ₀-Sentence 1 :=
  ⟨“1 < #0” ⋏ (∀[“#0 < #1 + 1”] dvdDef/[#0, #1] ⟶ “#0 = 1 ∨ #0 = #1”), by simp [Hierarchy.pi_zero_iff_sigma_zero]⟩

lemma isPrime_defined : Δ₀-Predicate (λ a : M ↦ IsPrime a) via isPrimedef := by
  intro v
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.vecHead, Matrix.constant_eq_singleton,
    IsPrime, isPrimedef, le_iff_lt_succ, dvd_defined.pval]

end Prime

end Model

end

end Arith

end LO.FirstOrder
