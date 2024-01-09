import Arithmetization.Definability
import Logic.FirstOrder.Arith.PAminus

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

@[simp] lemma le_mul_self (a : M) : a ≤ a * a := by
  have : 0 ≤ a := by exact zero_le a
  rcases this with (rfl | pos) <;> simp [*, ←pos_iff_one_le]

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

def msubDefinition : Σᴬ[0] 3 :=
  ⟨“(#2 ≤ #1 → #1 = #2 + #0) ∧ (#1 < #2 → #0 = 0)”, by simp[Hierarchy.pi_zero_iff_sigma_zero]⟩

lemma msub_definable : Σᴬ[0]-Function₂ (λ a b : M ↦ a ∸ b) msubDefinition := by
  intro v; simp [msubDefinition, msub_eq_iff]

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

lemma pos_msub_iff_lt : 0 < a ∸ b ↔ b < a :=
  ⟨by contrapose; simp; exact msub_spec_of_le,
   by intro h; by_contra hs
      simp at hs
      have : a = b := by simpa [hs] using msub_spec_of_ge (show b ≤ a from LT.lt.le h)
      simp [this] at h⟩

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

def dvdDefinition : Σᴬ[0] 2 := ⟨“∃[#0 < #2 + 1] #2 = #1 * #0”, by simp⟩

lemma dvd_definable : Σᴬ[0]-Relation (λ a b : M ↦ a ∣ b) dvdDefinition :=
  λ v ↦ by simp[dvd_iff_bounded, Matrix.vecHead, Matrix.vecTail, le_iff_lt_succ, dvdDefinition]

end Dvd

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

lemma le_of_dvd (h : 0 < b) : a ∣ b → a ≤ b := by
  rintro ⟨c, rfl⟩
  exact le_mul_self_of_pos_right
    (pos_iff_ne_zero.mpr (show c ≠ 0 from by rintro rfl; simp at h))

lemma dvd_antisymm : a ∣ b → b ∣ a → a = b := by
  intro hx hy
  rcases show a = 0 ∨ 0 < a from eq_zero_or_pos a with (rfl | ltx)
  · simp [show b = 0 from by simpa using hx]
  · rcases show b = 0 ∨ 0 < b from eq_zero_or_pos b with (rfl | lty)
    · simp [show a = 0 from by simpa using hy]
    · exact le_antisymm (le_of_dvd lty hx) (le_of_dvd ltx hy)

lemma dvd_one : a ∣ 1 ↔ a = 1 := ⟨by { intro hx; exact dvd_antisymm hx (by simp) }, by rintro rfl; simp⟩

section Prime

lemma eq_one_or_eq_of_dvd_of_prime {p a : M} (pp : Prime p) (hxp : a ∣ p) : a = 1 ∨ a = p := by
  have : p ∣ a ∨ a ∣ 1 := pp.left_dvd_or_dvd_right_of_dvd_mul (show a ∣ p * 1 from by simpa using hxp)
  rcases this with (hx | hx)
  · right; exact dvd_antisymm hxp hx
  · left; exact dvd_one.mp hx

/-
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

def isPrimeDefinition : Σᴬ[0] 1 :=
  ⟨“1 < #0” ⋏ (∀[“#0 < #1 + 1”] dvdDefinition/[#0, #1] ⟶ “#0 = 1 ∨ #0 = #1”), by simp [Hierarchy.pi_zero_iff_sigma_zero]⟩

lemma isPrime_definable : Σᴬ[0]-Predicate (λ a : M ↦ IsPrime a) isPrimeDefinition := by
  intro v
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.vecHead, Matrix.constant_eq_singleton,
    IsPrime, isPrimeDefinition, le_iff_lt_succ, dvd_definable.pval]

end Prime

section Pow2

def Pow2 (a : M) : Prop := 0 < a ∧ ∀ r ≤ a, 1 < r → r ∣ a → 2 ∣ r

def pow2Definition : Σᴬ[0] 1 :=
  ⟨“0 < #0 ∧ ∀[#0 < #1 + 1] (1 < #0 →  !dvdDefinition [#0, #1] → !dvdDefinition [2, #0])”, by simp [Hierarchy.pi_zero_iff_sigma_zero]⟩

lemma pow2_definable : Σᴬ[0]-Predicate (Pow2 : M → Prop) pow2Definition := by
  intro v
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.vecHead, Matrix.constant_eq_singleton,
    Pow2, pow2Definition, le_iff_lt_succ, dvd_definable.pval]

end Pow2

end Model

end

end Arith

end LO.FirstOrder
