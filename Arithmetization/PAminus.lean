import Arithmetization.Definability
import Logic.FirstOrder.Arith.PAminus
import Mathlib.Algebra.GCDMonoid.Basic

namespace LO.FirstOrder

namespace Arith

noncomputable section

variable {M : Type} [Inhabited M] [DecidableEq M] [ORingSymbol M]
  [Structure ℒₒᵣ M] [Structure.ORing ℒₒᵣ M]
  [𝐏𝐀⁻.Mod M]

namespace Model

variable {a b c : M}

lemma lt_iff_succ_le : a < b ↔ a + 1 ≤ b := by simp [le_iff_lt_succ]

lemma pos_iff_one_le : 0 < a ↔ 1 ≤ a := by simp [lt_iff_succ_le]

lemma one_lt_iff_two_le : 1 < a ↔ 2 ≤ a := by simp [lt_iff_succ_le, one_add_one_eq_two]

@[simp] lemma not_nonpos (a : M) : ¬a < 0 := by simp

lemma lt_two_iff_le_one : a < 2 ↔ a ≤ 1 := by
  simp [lt_iff_succ_le,
    show a + 1 ≤ 2 ↔ a ≤ 1 from by
      rw[show (2 : M) = 1 + 1 from one_add_one_eq_two.symm]; exact add_le_add_iff_right 1]

@[simp] lemma lt_one_iff_eq_zero : a < 1 ↔ a = 0 := ⟨by
  intro hx
  have : a ≤ 0 := by exact le_iff_lt_succ.mpr (show a < 0 + 1 from by simpa using hx)
  exact nonpos_iff_eq_zero.mp this,
  by rintro rfl; exact zero_lt_one⟩

lemma le_one_iff_eq_zero_or_one : a ≤ 1 ↔ a = 0 ∨ a = 1 :=
  ⟨by intro h; rcases h with (rfl | ltx)
      · simp
      · simp [show a = 0 from by simpa using ltx],
   by rintro (rfl | rfl) <;> simp⟩

lemma le_two_iff_eq_zero_or_one_or_two : a ≤ 2 ↔ a = 0 ∨ a = 1 ∨ a = 2 :=
  ⟨by intro h; rcases h with (rfl | lt)
      · simp
      · rcases lt_two_iff_le_one.mp lt with (rfl | lt)
        · simp
        · simp [show a = 0 from by simpa using lt],
   by rintro (rfl | rfl | rfl) <;> simp [one_le_two]⟩

lemma le_three_iff_eq_zero_or_one_or_two_or_three : a ≤ 3 ↔ a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 :=
  ⟨by intro h; rcases h with (rfl | lt)
      · simp
      · have : a ≤2 := by simpa [←le_iff_lt_succ, ←two_add_one_eq_three] using lt
        rcases this with (rfl| lt)
        · simp
        · rcases lt_two_iff_le_one.mp lt with (rfl | lt)
          · simp
          · simp [show a = 0 from by simpa using lt],
   by rintro (rfl | rfl | rfl | rfl) <;> simp [one_le_two, ←two_add_one_eq_three]⟩

lemma two_mul_two_eq_four : 2 * 2 = (4 : M) := by
  rw [←one_add_one_eq_two, mul_add, add_mul, mul_one, ←add_assoc,
    one_add_one_eq_two, two_add_one_eq_three, three_add_one_eq_four]

lemma two_pow_two_eq_four : 2 ^ 2 = (4 : M) := by
  simp [sq, two_mul_two_eq_four]

@[simp] lemma le_mul_self (a : M) : a ≤ a * a := by
  have : 0 ≤ a := by exact zero_le a
  rcases this with (rfl | pos) <;> simp [*, ←pos_iff_one_le]

@[simp] lemma le_sq (a : M) : a ≤ a^2 := by simp [sq]

lemma sq_le_sq_iff : a ≤ b ↔ a^2 ≤ b^2 := by simp [sq]; apply mul_self_le_mul_self_iff <;> simp

lemma sq_lt_sq_iff : a < b ↔ a^2 < b^2 := by simp [sq]; apply mul_self_lt_mul_self_iff <;> simp

lemma le_mul_of_pos_right (h : 0 < b) : a ≤ a * b := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp h)

lemma le_mul_of_pos_left (h : 0 < b) : a ≤ b * a := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp h)

@[simp] lemma le_two_mul_left : a ≤ 2 * a := le_mul_of_pos_left (by simp)

lemma lt_mul_of_pos_of_one_lt_right (pos : 0 < a) (h : 1 < b) : a < a * b := _root_.lt_mul_of_one_lt_right pos h

lemma lt_mul_of_pos_of_one_lt_left (pos : 0 < a) (h : 1 < b) : a < b * a := _root_.lt_mul_of_one_lt_left pos h

lemma mul_le_mul_left (h : b ≤ c) : a * b ≤ a * c := mul_le_mul_of_nonneg_left h (by simp)

lemma mul_le_mul_right (h : b ≤ c) : b * a ≤ c * a := mul_le_mul_of_nonneg_right h (by simp)

theorem lt_of_mul_lt_mul_left (h : a * b < a * c) : b < c := lt_of_mul_lt_mul_of_nonneg_left h (by simp)

theorem lt_of_mul_lt_mul_right (h : b * a < c * a) : b < c := lt_of_mul_lt_mul_of_nonneg_right h (by simp)

lemma pow_three (x : M) : x^3 = x * x * x := by simp [← two_add_one_eq_three, pow_add, sq]

lemma pow_four (x : M) : x^4 = x * x * x * x := by simp [← three_add_one_eq_four, pow_add, pow_three]

lemma pow_four_eq_sq_sq (x : M) : x^4 = (x^2)^2 := by simp [pow_four, sq, mul_assoc]

instance : CovariantClass M M (· * ·) (· ≤ ·) := ⟨by intro; exact mul_le_mul_left⟩

@[simp] lemma one_lt_mul_self_iff {a : M} : 1 < a * a ↔ 1 < a :=
  ⟨(fun h ↦ by push_neg at h ⊢; exact mul_le_one' h h).mtr, fun h ↦ one_lt_mul'' h h⟩

@[simp] lemma one_lt_sq_iff {a : M} : 1 < a^2 ↔ 1 < a := by simp [sq]

@[simp] lemma mul_self_eq_one_iff {a : M} : a * a = 1 ↔ a = 1 :=
  not_iff_not.mp (by simp [ne_iff_lt_or_gt])

@[simp] lemma sq_eq_one_iff {a : M} : a^2 = 1 ↔ a = 1 := by simp [sq]

section msub

lemma msub_existsUnique (a b : M) : ∃! c, (a ≥ b → a = b + c) ∧ (a < b → c = 0) := by
  have : b ≤ a ∨ a < b := le_or_lt b a
  rcases this with (hxy | hxy) <;> simp[hxy]
  · simp [show ¬a < b from not_lt.mpr hxy]
    have : ∃ c, a = b + c := exists_add_of_le hxy
    rcases this with ⟨c, rfl⟩
    exact ExistsUnique.intro c rfl (fun a h => (add_left_cancel h).symm)
  · simp [show ¬b ≤ a from not_le.mpr hxy]

def msub (a b : M) : M := Classical.choose! (msub_existsUnique a b)

infixl:65 " ∸ " => msub

lemma msub_spec_of_ge (h : a ≥ b) : a = b + (a ∸ b) := (Classical.choose!_spec (msub_existsUnique a b)).1 h

lemma msub_spec_of_lt (h : a < b) : a ∸ b = 0 := (Classical.choose!_spec (msub_existsUnique a b)).2 h

lemma msub_eq_iff : c = a ∸ b ↔ ((a ≥ b → a = b + c) ∧ (a < b → c = 0)) := Classical.choose!_eq_iff _

def msubdef : Σᴬ[0] 3 :=
  ⟨“(#2 ≤ #1 → #1 = #2 + #0) ∧ (#1 < #2 → #0 = 0)”, by simp[Hierarchy.pi_zero_iff_sigma_zero]⟩

lemma msub_defined : Σᴬ[0]-Function₂ (λ a b : M ↦ a ∸ b) msubdef := by
  intro v; simp [msubdef, msub_eq_iff]

@[simp] lemma msub_le_self (a b : M) : a ∸ b ≤ a := by
  have : b ≤ a ∨ a < b := le_or_lt b a
  rcases this with (hxy | hxy) <;> simp[hxy]
  · simpa [← msub_spec_of_ge hxy] using show a ∸ b ≤ b + (a ∸ b) from le_add_self
  · simp[msub_spec_of_lt hxy]

lemma msub_polybounded : PolyBounded₂ (λ a b : M ↦ a ∸ b) #0 := λ _ ↦ by simp

@[simp] lemma msub_self (a : M) : a ∸ a = 0 :=
  add_right_eq_self.mp (msub_spec_of_ge (a := a) (b := a) (by rfl)).symm

lemma msub_spec_of_le (h : a ≤ b) : a ∸ b = 0 := by
  rcases lt_or_eq_of_le h with (lt | rfl) <;> simp [msub_spec_of_lt, *]

lemma msub_add_self_of_le (h : b ≤ a) : a ∸ b + b = a := by symm; rw [add_comm]; exact msub_spec_of_ge h

lemma add_tmsub_self_of_le (h : b ≤ a) : b + (a ∸ b) = a := by symm; exact msub_spec_of_ge h

@[simp] lemma add_msub_self : (a + b) ∸ b = a := by
  symm; simpa [add_comm b] using msub_spec_of_ge (@le_add_self _ _ b a)

@[simp] lemma add_msub_self' : (b + a) ∸ b = a := by simp [add_comm]

@[simp] lemma zero_msub (a : M) : 0 ∸ a = 0 := msub_spec_of_le (by simp)

@[simp] lemma msub_zero (a : M) : a ∸ 0 = a := by
  simpa using msub_add_self_of_le (show 0 ≤ a from zero_le a)

lemma msub_remove_left (e : a = b + c) : a ∸ c = b := by simp[e]

lemma msub_msub : a ∸ b ∸ c = a ∸ (b + c) := by
  by_cases ha : b + c ≤ a
  · exact msub_remove_left <| msub_remove_left <| by
      simp [add_assoc, show c + b = b + c from add_comm _ _, msub_add_self_of_le, ha]
  · simp [msub_spec_of_lt (show a < b + c from not_le.mp ha)]
    by_cases hc : c ≤ a ∸ b
    · by_cases hb : b ≤ a
      · have : a < a := calc
          a < b + c       := not_le.mp ha
          _ ≤ b + (a ∸ b) := by simp[hc]
          _ = a           := add_tmsub_self_of_le hb
        simp at this
      · simp [show a ∸ b = 0 from msub_spec_of_lt (not_le.mp hb)]
    · exact msub_spec_of_lt (not_le.mp hc)

@[simp] lemma pos_msub_iff_lt : 0 < a ∸ b ↔ b < a :=
  ⟨by contrapose; simp; exact msub_spec_of_le,
   by intro h; by_contra hs
      simp at hs
      have : a = b := by simpa [hs] using msub_spec_of_ge (show b ≤ a from LT.lt.le h)
      simp [this] at h⟩

@[simp] lemma msub_eq_zero_iff_le : a ∸ b = 0 ↔ a ≤ b :=
  not_iff_not.mp (by simp [←pos_iff_ne_zero])

end msub

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

def dvddef : Σᴬ[0] 2 := ⟨“∃[#0 < #2 + 1] #2 = #1 * #0”, by simp⟩

lemma dvd_defined : Σᴬ[0]-Relation (λ a b : M ↦ a ∣ b) dvddef :=
  λ v ↦ by simp[dvd_iff_bounded, Matrix.vecHead, Matrix.vecTail, le_iff_lt_succ, dvddef]

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

def isPrimedef : Σᴬ[0] 1 :=
  ⟨“1 < #0” ⋏ (∀[“#0 < #1 + 1”] dvddef/[#0, #1] ⟶ “#0 = 1 ∨ #0 = #1”), by simp [Hierarchy.pi_zero_iff_sigma_zero]⟩

lemma isPrime_defined : Σᴬ[0]-Predicate (λ a : M ↦ IsPrime a) isPrimedef := by
  intro v
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.vecHead, Matrix.constant_eq_singleton,
    IsPrime, isPrimedef, le_iff_lt_succ, dvd_defined.pval]

end Prime

section IsPow2

def IsPow2 (a : M) : Prop := 0 < a ∧ ∀ r ≤ a, 1 < r → r ∣ a → 2 ∣ r

def pow2def : Σᴬ[0] 1 :=
  ⟨“0 < #0 ∧ ∀[#0 < #1 + 1] (1 < #0 →  !dvddef [#0, #1] → !dvddef [2, #0])”, by simp [Hierarchy.pi_zero_iff_sigma_zero]⟩

lemma pow2_defined : Σᴬ[0]-Predicate (IsPow2 : M → Prop) pow2def := by
  intro v
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.vecHead, Matrix.constant_eq_singleton,
    IsPow2, pow2def, le_iff_lt_succ, dvd_defined.pval]

lemma IsPow2.pos {a : M} (h : IsPow2 a) : 0 < a := h.1

lemma IsPow2.dvd {a : M} (h : IsPow2 a) {r} (hr : r ≤ a) : 1 < r → r ∣ a → 2 ∣ r := h.2 r hr

@[simp] lemma pow2_one : IsPow2 (1 : M) := ⟨by simp, by
  intro r hr hhr hd
  rcases show r = 0 ∨ r = 1 from le_one_iff_eq_zero_or_one.mp hr with (rfl | rfl)
  · simp
  · simp at hhr⟩

@[simp] lemma not_pow2_zero : ¬IsPow2 (0 : M) := by
  intro h; have := h.pos; simp at this

lemma IsPow2.two_dvd {a : M} (h : IsPow2 a) (lt : 1 < a) : 2 ∣ a := h.dvd (le_refl _) lt (by simp)

lemma IsPow2.two_dvd' {a : M} (h : IsPow2 a) (lt : a ≠ 1) : 2 ∣ a :=
  h.dvd (le_refl _) (by
    by_contra A; simp [le_one_iff_eq_zero_or_one] at A
    rcases A with (rfl | rfl) <;> simp at h lt)
    (by simp)

lemma IsPow2.of_dvd {a b : M} (h : b ∣ a) : IsPow2 a → IsPow2 b := by
  intro ha
  have : 0 < b := by
    by_contra e
    have : a = 0 := by simpa [show b = 0 from by simpa using e] using h
    rcases this with rfl
    simpa using ha.pos
  exact ⟨this, fun r hr ltr hb ↦
    ha.dvd (show r ≤ a from le_trans hr (le_of_dvd ha.pos h)) ltr (dvd_trans hb h)⟩

end IsPow2

end Model

end

end Arith

end LO.FirstOrder
