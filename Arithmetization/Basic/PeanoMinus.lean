import Arithmetization.Definability.Absoluteness

namespace LO.Arith

open FirstOrder FirstOrder.Arith

noncomputable section

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐏𝐀⁻]

variable {a b c : V}

section sub

lemma sub_existsUnique (a b : V) : ∃! c, (a ≥ b → a = b + c) ∧ (a < b → c = 0) := by
  have : b ≤ a ∨ a < b := le_or_lt b a
  rcases this with (hxy | hxy) <;> simp [hxy]
  have : ∃ c, a = b + c := exists_add_of_le hxy
  rcases this with ⟨c, rfl⟩
  exact ExistsUnique.intro c rfl (fun a h => (add_left_cancel h).symm)

def sub (a b : V) : V := Classical.choose! (sub_existsUnique a b)

instance : Sub V := ⟨sub⟩

lemma sub_spec_of_ge (h : a ≥ b) : a = b + (a - b) := (Classical.choose!_spec (sub_existsUnique a b)).1 h

lemma sub_spec_of_lt (h : a < b) : a - b = 0 := (Classical.choose!_spec (sub_existsUnique a b)).2 h

lemma sub_eq_iff : c = a - b ↔ ((a ≥ b → a = b + c) ∧ (a < b → c = 0)) := Classical.choose!_eq_iff (sub_existsUnique a b)

@[simp] lemma sub_le_self (a b : V) : a - b ≤ a := by
  have : b ≤ a ∨ a < b := le_or_lt b a
  rcases this with (hxy | hxy) <;> simp[hxy]
  · simpa [← sub_spec_of_ge hxy] using show a - b ≤ b + (a - b) from le_add_self
  · simp[sub_spec_of_lt hxy]

open FirstOrder.Arith.HierarchySymbol.Boldface

def _root_.LO.FirstOrder.Arith.subDef : 𝚺₀.Semisentence 3 :=
  .mkSigma “z x y | (x ≥ y → x = y + z) ∧ (x < y → z = 0)” (by simp[Hierarchy.pi_zero_iff_sigma_zero])

lemma sub_defined : 𝚺₀-Function₂ ((· - ·) : V → V → V) via subDef := by
  intro v; simp [FirstOrder.Arith.subDef, sub_eq_iff]

@[simp] lemma sub_defined_iff (v) :
    Semiformula.Evalbm V v subDef.val ↔ v 0 = v 1 - v 2 := sub_defined.df.iff v

instance sub_definable (ℌ : HierarchySymbol) : ℌ.BoldfaceFunction₂ ((· - ·) : V → V → V) := sub_defined.to_definable₀

instance sub_polybounded : Bounded₂ ((· - ·) : V → V → V) := ⟨#0, λ _ ↦ by simp⟩

@[simp] lemma sub_self (a : V) : a - a = 0 :=
  add_right_eq_self.mp (sub_spec_of_ge (a := a) (b := a) (by rfl)).symm

lemma sub_spec_of_le (h : a ≤ b) : a - b = 0 := by
  rcases lt_or_eq_of_le h with (lt | rfl) <;> simp [sub_spec_of_lt, *]

lemma sub_add_self_of_le (h : b ≤ a) : a - b + b = a := by symm; rw [add_comm]; exact sub_spec_of_ge h

lemma add_tsub_self_of_le (h : b ≤ a) : b + (a - b) = a := by symm; exact sub_spec_of_ge h

@[simp] lemma add_sub_self : (a + b) - b = a := by
  symm; simpa [add_comm b] using sub_spec_of_ge (@le_add_self _ _ b a)

@[simp] lemma add_sub_self' : (b + a) - b = a := by simp [add_comm]

@[simp] lemma zero_sub (a : V) : 0 - a = 0 := sub_spec_of_le (by simp)

@[simp] lemma sub_zero (a : V) : a - 0 = a := by
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

instance : OrderedSub V where
  tsub_le_iff_right := by
    intro a b c
    by_cases h : b ≤ a
    · calc
        a - b ≤ c ↔ (a - b) + b ≤ c + b := by simp
        _         ↔ a ≤ c + b           := by rw [sub_add_self_of_le h]
    · simp [sub_spec_of_lt (show a < b from by simpa using h)]
      exact le_trans (le_of_lt $ show a < b from by simpa using h) (by simp)

lemma zero_or_succ (a : V) : a = 0 ∨ ∃ a', a = a' + 1 := by
  rcases zero_le a with (rfl | pos)
  · simp
  · right; exact ⟨a - 1, by rw [sub_add_self_of_le]; exact pos_iff_one_le.mp pos⟩

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

lemma add_sub_of_le (h : c ≤ b) (a : V) : a + b - c = a + (b - c) := add_tsub_assoc_of_le h a

lemma sub_succ_add_succ {x y : V} (h : y < x) (z) : x - (y + 1) + (z + 1) = x - y + z := calc
  x - (y + 1) + (z + 1) = x - (y + 1) + 1 + z := by simp [add_assoc, add_comm]
  _                     = x - y - 1 + 1 + z   := by simp [sub_sub]
  _                     = x - y + z           := by simp; rw [sub_add_self_of_le (one_le_of_zero_lt _ (pos_sub_iff_lt.mpr h))]

lemma le_sub_one_of_lt {a b : V} (h : a < b) : a ≤ b - 1 := by
  have : 1 ≤ b := one_le_of_zero_lt _ (pos_of_gt h)
  simp [le_iff_lt_succ, sub_add_self_of_le this, h]

end sub

section Dvd

lemma le_mul_self_of_pos_left (hy : 0 < b) : a ≤ b * a := by
  have : 1 * a ≤ b * a := mul_le_mul_of_nonneg_right (one_le_of_zero_lt b hy) (by simp)
  simpa using this

lemma le_mul_self_of_pos_right (hy : 0 < b) : a ≤ a * b := by
  simpa [mul_comm a b] using le_mul_self_of_pos_left hy

lemma dvd_iff_bounded {a b : V} : a ∣ b ↔ ∃ c ≤ b, b = a * c := by
  by_cases hx : a = 0
  · simp[hx]; rintro rfl; exact ⟨0, by simp⟩
  · constructor
    · rintro ⟨c, rfl⟩; exact ⟨c, le_mul_self_of_pos_left (pos_iff_ne_zero.mpr hx), rfl⟩
    · rintro ⟨c, hz, rfl⟩; exact dvd_mul_right a c

def _root_.LO.FirstOrder.Arith.dvd : 𝚺₀.Semisentence 2 :=
  .mkSigma “x y | ∃ z <⁺ y, y = x * z” (by simp)

lemma dvd_defined : 𝚺₀-Relation (fun a b : V ↦ a ∣ b) via dvd :=
  fun v ↦ by simp [dvd_iff_bounded, Matrix.vecHead, Matrix.vecTail, dvd]

@[simp] lemma dvd_defined_iff (v) :
    Semiformula.Evalbm V v dvd.val ↔ v 0 ∣ v 1 := dvd_defined.df.iff v

instance dvd_definable (ℌ : HierarchySymbol) : ℌ.BoldfaceRel ((· ∣ ·) : V → V → Prop) := dvd_defined.to_definable₀

section

syntax:45 first_order_term:45 " ∣ " first_order_term:0 : first_order_formula

macro_rules
  | `(“ $binders* | $t:first_order_term ∣ $u:first_order_term ”) => `(“ $binders* | !dvd.val $t $u”)

end

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

theorem units_eq_one (u : Vˣ) : u = 1 :=
  Units.ext <| dvd_one_iff.mp ⟨u.inv, u.val_inv.symm⟩

@[simp] lemma unit_iff_eq_one {a : V} : IsUnit a ↔ a = 1 :=
  ⟨by rintro ⟨u, rfl⟩; simp [units_eq_one u], by rintro rfl; simp⟩

section Prime

lemma eq_one_or_eq_of_dvd_of_prime {p a : V} (pp : Prime p) (hxp : a ∣ p) : a = 1 ∨ a = p := by
  have : p ∣ a ∨ a ∣ 1 := pp.left_dvd_or_dvd_right_of_dvd_mul (show a ∣ p * 1 from by simpa using hxp)
  rcases this with (hx | hx)
  · right; exact dvd_antisymm hxp hx
  · left; exact dvd_one_iff.mp hx

/-
lemma irreducible_iff_bounded {a : V} : Irreducible a ↔ 1 < a ∧ ∀ b ≤ a, (b ∣ a → b = 1 ∨ b = a) := by
  constructor
  · intro ha
    have : 1 < a := by
      by_contra A
      simp [Irreducible.ne_one ha, Irreducible.ne_zero ha, le_one_iff_eq_zero_or_one] at A
    exact ⟨this, by {  }⟩

lemma prime_iff_bounded {a : V} : Prime a ↔ 1 < a ∧ ∀ b ≤ a, (b ∣ a → b = 1 ∨ b = a) := by
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

def IsPrime (a : V) : Prop := 1 < a ∧ ∀ b ≤ a, b ∣ a → b = 1 ∨ b = a
-- TODO: prove IsPrime a ↔ Prime a

def _root_.LO.FirstOrder.Arith.isPrime : 𝚺₀.Semisentence 1 :=
  .mkSigma “x | 1 < x ∧ ∀ y <⁺ x, !dvd.val y x → y = 1 ∨ y = x” (by simp [Hierarchy.pi_zero_iff_sigma_zero])

lemma isPrime_defined : 𝚺₀-Predicate (λ a : V ↦ IsPrime a) via isPrime := by
  intro v
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.vecHead, Matrix.constant_eq_singleton,
    IsPrime, isPrime]

end Prime

section min

def _root_.LO.FirstOrder.Arith.min : 𝚺₀.Semisentence 3 :=
  .mkSigma “z x y | (x ≤ y → z = x) ∧ (x ≥ y → z = y)” (by simp)

lemma min_defined : 𝚺₀-Function₂ (min : V → V → V) via min := by
  intro v; simp [FirstOrder.Arith.min]
  rcases le_total (v 1) (v 2) with (h | h) <;> simp [h]
  · intro h₀₁ h₂₁
    exact le_antisymm (by simpa [h₀₁] using h) (by simpa [h₀₁] using h₂₁)
  · intro h₀₂ h₁₂
    exact le_antisymm (by simpa [h₀₂] using h) (by simpa [h₀₂] using h₁₂)

@[simp] lemma eval_minDef (v) :
    Semiformula.Evalbm V v min.val ↔ v 0 = min (v 1) (v 2) := min_defined.df.iff v

instance min_definable (ℌ) : ℌ-Function₂ (min : V → V → V) := HierarchySymbol.Defined.to_definable₀ min_defined

instance min_polybounded : Bounded₂ (min : V → V → V) := ⟨#0, λ _ ↦ by simp⟩

end min

section max

def _root_.LO.FirstOrder.Arith.max : 𝚺₀.Semisentence 3 :=
  .mkSigma “z x y | (x ≥ y → z = x) ∧ (x ≤ y → z = y)” (by simp)

lemma max_defined : 𝚺₀-Function₂ (max : V → V → V) via max := by
  intro v; simp [Arith.max]
  rcases le_total (v 1) (v 2) with (h | h) <;> simp [h]
  · intro h₀₂ h₂₁
    exact le_antisymm (by simpa [h₀₂] using h₂₁) (by simpa [h₀₂] using h)
  · intro h₀₁ h₁₂
    exact le_antisymm (by simpa [h₀₁] using h₁₂) (by simpa [h₀₁] using h)

@[simp] lemma eval_maxDef (v) :
    Semiformula.Evalbm V v max.val ↔ v 0 = max (v 1) (v 2) := max_defined.df.iff v

instance max_definable (Γ) : Γ-Function₂ (max : V → V → V) := HierarchySymbol.Defined.to_definable₀ max_defined

instance max_polybounded : Bounded₂ (max : V → V → V) := ⟨‘#0 + #1’, λ v ↦ by simp⟩

end max

end

end LO.Arith
