import Arithmetization.Vorspiel.Vorspiel
import Logic.FirstOrder.Arith.PAminus

namespace LO.FirstOrder

namespace Arith

noncomputable section

variable {M : Type} [Inhabited M] [DecidableEq M] [ORingSymbol M]
  [Structure ℒₒᵣ M] [Structure.ORing ℒₒᵣ M]
  [𝐏𝐀⁻.Mod M]

namespace PAminus.Model

variable {x y z : M}

lemma lt_iff_succ_le : x < y ↔ x + 1 ≤ y := by simp [← le_of_lt_succ]

lemma le_iff_lt_succ : x ≤ y ↔ x < y + 1 := by simp [le_of_lt_succ]

section msub

lemma msub_existsUnique (x y : M) : ∃! z, (x ≥ y → x = y + z) ∧ (x < y → z = 0) := by
  have : y ≤ x ∨ x < y := le_or_lt y x
  rcases this with (hxy | hxy) <;> simp[hxy]
  · simp [show ¬x < y from not_lt.mpr hxy]
    have : ∃ z, x = y + z := exists_add_of_le hxy
    rcases this with ⟨z, rfl⟩
    exact ExistsUnique.intro z rfl (fun x h => (add_left_cancel h).symm)
  · simp [show ¬y ≤ x from not_le.mpr hxy]

def msub (x y : M) : M := Classical.choose! (msub_existsUnique x y)

infix:65 " -̇ " => msub

lemma msub_spec_of_ge (h : x ≥ y) : x = y + (x -̇ y) := (Classical.choose!_spec (msub_existsUnique x y)).1 h

lemma msub_spec_of_lt (h : x < y) : x -̇ y = 0 := (Classical.choose!_spec (msub_existsUnique x y)).2 h

lemma msub_eq_iff : z = x -̇ y ↔ ((x ≥ y → x = y + z) ∧ (x < y → z = 0)) := Classical.choose!_eq_iff _

lemma msub_definable : Σᴬ[0]-Function₂ (λ x y : M ↦ x -̇ y) :=
  ⟨“(#2 ≤ #1 → #1 = #2 + #0) ∧ (#1 < #2 → #0 = 0)”,
    by simp[Hierarchy.pi_zero_iff_sigma_zero], by intro v; simp[msub_eq_iff]; rfl⟩

@[simp] lemma msub_le_self (x y : M) : x -̇ y ≤ x := by
  have : y ≤ x ∨ x < y := le_or_lt y x
  rcases this with (hxy | hxy) <;> simp[hxy]
  · simpa [← msub_spec_of_ge hxy] using show x -̇ y ≤ y + (x -̇ y) from le_add_self
  · simp[msub_spec_of_lt hxy]

lemma msub_polybounded : PolyBounded₂ (λ x y : M ↦ x -̇ y) := ⟨#0, λ _ ↦ by simp⟩

@[simp] lemma msub_self (x : M) : x -̇ x = 0 :=
  add_right_eq_self.mp (msub_spec_of_ge (x := x) (y := x) (by rfl)).symm

lemma msub_spec_of_le (h : x ≤ y) : x -̇ y = 0 := by
  rcases lt_or_eq_of_le h with (lt | rfl) <;> simp [msub_spec_of_lt, *]

lemma msub_add_right (h : y ≤ x) : x -̇ y + y = x := by symm; rw [add_comm]; exact msub_spec_of_ge h

lemma msub_add_left (h : y ≤ x) : y + (x -̇ y) = x := by symm; exact msub_spec_of_ge h

end msub

section Dvd

lemma le_mul_self_of_pos_left (hy : 0 < y) : x ≤ y * x := by
  have : 1 * x ≤ y * x := mul_le_mul_of_nonneg_right (one_le_of_zero_lt y hy) (by simp)
  simpa using this

lemma le_mul_self_of_pos_right (hy : 0 < y) : x ≤ x * y := by
  simpa [mul_comm x y] using le_mul_self_of_pos_left hy

lemma dvd_iff_bounded {x y : M} : x ∣ y ↔ ∃ z ≤ y, y = x * z := by
  by_cases hx : x = 0
  · simp[hx]; rintro rfl; exact ⟨0, by simp⟩
  · constructor
    · rintro ⟨z, rfl⟩; exact ⟨z, le_mul_self_of_pos_left (pos_iff_ne_zero.mpr hx), rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact dvd_mul_right x z

lemma dvd_definable : Σᴬ[0]-Relation (λ x y : M ↦ x ∣ y) :=
  ⟨∃[“#0 < #2 + 1”] “#2 = #1 * #0”, by simp,
  λ v ↦ by simp[dvd_iff_bounded, Matrix.vecHead, Matrix.vecTail, le_of_lt_succ]⟩

end Dvd

@[simp] lemma lt_one_iff_eq_zero : x < 1 ↔ x = 0 := ⟨by
  intro hx
  have : x ≤ 0 := by exact le_of_lt_succ.mp (show x < 0 + 1 from by simpa using hx)
  exact nonpos_iff_eq_zero.mp this,
  by rintro rfl; exact zero_lt_one⟩

lemma le_one_iff_eq_zero_or_one : x ≤ 1 ↔ x = 0 ∨ x = 1 :=
  ⟨by intro h; rcases h with (rfl | ltx)
      · simp
      · simp [show x = 0 from by simpa using ltx],
   by rintro (rfl | rfl) <;> simp⟩

lemma le_of_dvd (h : 0 < y) : x ∣ y → x ≤ y := by
  rintro ⟨z, rfl⟩
  exact le_mul_self_of_pos_right
    (pos_iff_ne_zero.mpr (show z ≠ 0 from by rintro rfl; simp at h))

lemma dvd_antisymm : x ∣ y → y ∣ x → x = y := by
  intro hx hy
  rcases show x = 0 ∨ 0 < x from eq_zero_or_pos x with (rfl | ltx)
  · simp [show y = 0 from by simpa using hx]
  · rcases show y = 0 ∨ 0 < y from eq_zero_or_pos y with (rfl | lty)
    · simp [show x = 0 from by simpa using hy]
    · exact le_antisymm (le_of_dvd lty hx) (le_of_dvd ltx hy)

lemma dvd_one : x ∣ 1 ↔ x = 1 := ⟨by { intro hx; exact dvd_antisymm hx (by simp) }, by rintro rfl; simp⟩

section Prime

lemma eq_one_or_eq_of_dvd_of_prime {p x : M} (pp : Prime p) (hxp : x ∣ p) : x = 1 ∨ x = p := by
  have : p ∣ x ∨ x ∣ 1 := pp.left_dvd_or_dvd_right_of_dvd_mul (show x ∣ p * 1 from by simpa using hxp)
  rcases this with (hx | hx)
  · right; exact dvd_antisymm hxp hx
  · left; exact dvd_one.mp hx

/-
lemma prime_iff_bounded {x : M} : Prime x ↔ 1 < x ∧ ∀ y ≤ x, (y ∣ x → y = 1 ∨ y = x) := by
  constructor
  · intro prim
    have : 1 < x := by
      by_contra A; simp at A
      rcases le_one_iff_eq_zero_or_one.mp A with (rfl | rfl)
      · exact not_prime_zero prim
      · exact not_prime_one prim
    exact ⟨this, fun y hy hyx ↦ eq_one_or_eq_of_dvd_of_prime prim hyx⟩
  · intro H; constructor
    · sorry
    · constructor
      · sorry
      · intro y z h
-/

def IsPrime (x : M) : Prop := 1 < x ∧ ∀ y ≤ x, (y ∣ x → y = 1 ∨ y = x)
-- TODO: prove IsPrime x ↔ Prime x

lemma isPrime_definable : Σᴬ[0]-Predicate (λ x : M ↦ IsPrime x) := by
  have : Σᴬ[0]-Relation (λ x y : M ↦ x ∣ y) := dvd_definable
  rcases this with ⟨dvd, hdvd, sdvd⟩
  let prime : Semisentence ℒₒᵣ 1 := “1 < #0” ⋏ (∀[“#0 < #1 + 1”] dvd/[#0, #1] ⟶ “#0 = 1 ∨ #0 = #1”)
  exact ⟨prime, by simp[prime, hdvd, Hierarchy.pi_zero_iff_sigma_zero],
    fun v ↦ by
      simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.vecHead, Matrix.constant_eq_singleton,
        IsPrime, ← sdvd, le_of_lt_succ]⟩

end Prime

section Pow2

def Pow2 (x : M) : Prop := 1 < x ∧ ∀ p ≤ x, IsPrime p → p ∣ x  → p = 2

end Pow2

end PAminus.Model

end

end Arith

end LO.FirstOrder
