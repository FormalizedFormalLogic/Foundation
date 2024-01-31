import Arithmetization.Ind
import Mathlib.Logic.Nonempty

namespace LO.FirstOrder

namespace Arith

noncomputable section

variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [𝐏𝐀⁻.Mod M]

namespace Model

section IOpen

variable [𝐈open.Mod M]

@[elab_as_elim]
lemma open_induction {P : M → Prop}
    (hP : ∃ p : Semiformula ℒₒᵣ M 1, p.Open ∧ ∀ x, P x ↔ Semiformula.Eval! M ![x] id p)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  induction (C := Semiformula.Open)
    (by rcases hP with ⟨p, hp, hhp⟩
        haveI : Inhabited M := Classical.inhabited_of_nonempty'
        exact ⟨p.fvEnumInv', (Rew.rewriteMap p.fvEnum').hom p, by simp[hp],
          by  intro x; simp [Semiformula.eval_rewriteMap, hhp]
              exact Semiformula.eval_iff_of_funEqOn p (by intro z hz; simp [Semiformula.fvEnumInv'_fvEnum' _ hz])⟩) zero succ

lemma open_leastNumber {P : M → Prop}
    (hP : ∃ p : Semiformula ℒₒᵣ M 1, p.Open ∧ ∀ x, P x ↔ Semiformula.Eval! M ![x] id p)
    (zero : P 0) {a} (counterex : ¬P a) : ∃ x, P x ∧ ¬P (x + 1) := by
  by_contra A
  have : ∀ x, P x := by
    intro x; induction x using open_induction
    · exact hP
    case zero => exact zero
    case succ n ih =>
      simp at A
      exact A n ih
  have : P a := this a
  contradiction

lemma div_exists_unique_pos (a : M) {b} (pos : 0 < b) : ∃! u, b * u ≤ a ∧ a < b * (u + 1) := by
  have : ∃ u, b * u ≤ a ∧ a < b * (u + 1) := by
    have : a < b * (a + 1) → ∃ u, b * u ≤ a ∧ a < b * (u + 1) := by
      simpa using open_leastNumber (P := λ u ↦ b * u ≤ a) ⟨“&b * #0 ≤ &a”, by simp, by intro x; simp⟩
    simp at this
    have hx : a < b * (a + 1) := by
      have : a + 0 < b * a + b :=
        add_lt_add_of_le_of_lt (le_mul_self_of_pos_left pos) pos
      simpa [mul_add] using this
    exact this hx
  rcases this with ⟨u, hu⟩
  exact ExistsUnique.intro u hu (by
    intro u' hu'
    by_contra ne
    wlog lt : u < u'
    · exact this a pos u' hu' u hu (Ne.symm ne) (Ne.lt_of_le ne $ by simpa using lt)
    have : a < a := by calc
      a < b * (u + 1) := hu.2
      _ ≤ b * u'      := (_root_.mul_le_mul_left pos).mpr (lt_iff_succ_le.mp lt)
      _ ≤ a           := hu'.1
    exact LT.lt.false this)

/-
lemma mod (a : M) {b} (pos : 0 < b) : ∃! u, ∃ v < b, a = b * u + v := by
  have : ∃! u, b * u ≤ a ∧ a < b * (u + 1) := by
    have : ∃ u, b * u ≤ a ∧ a < b * (u + 1) := by
      have : a < b * (a + 1) → ∃ u, b * u ≤ a ∧ a < b * (u + 1) := by
        simpa using open_leastNumber (P := λ u ↦ b * u ≤ a) ⟨“&b * #0 ≤ &a”, by simp, by intro x; simp⟩
      simp at this
      have hx : a < b * (a + 1) := by
        have : a + 0 < b * a + b :=
          add_lt_add_of_le_of_lt (le_mul_self_of_pos_left pos) pos
        simpa [mul_add] using this
      exact this hx
    rcases this with ⟨u, hu⟩
    exact ExistsUnique.intro u hu (by
      intro u' hu'
      by_contra ne
      wlog lt : u < u'
      · exact this a pos u' hu' u hu (Ne.symm ne) (Ne.lt_of_le ne $ by simpa using lt)
      have : a < a := by calc
        a < b * (u + 1) := hu.2
        _ ≤ b * u'      := (_root_.mul_le_mul_left pos).mpr (lt_iff_succ_le.mp lt)
        _ ≤ a           := hu'.1
      exact LT.lt.false this)
  have iff : ∀ u, (∃ v < b, a = b * u + v) ↔ (b * u ≤ a ∧ a < b * (u + 1)) := by
    intro u; constructor
    · rintro ⟨v, hv, rfl⟩
      simp [mul_add, hv]
    · intro h
      let v := a - b * u
      have e : a = b*u + v := by simp [add_tsub_self_of_le h.1]
      have : v < b := by
        by_contra hyv
        have hyv : b ≤ v := by simpa using hyv
        have : a < a := by calc
          a < b * (u + 1) := h.2
          _ ≤ b * u + v   := by simpa [mul_add] using hyv
          _ = a           := e.symm
        exact LT.lt.false this
      exact ⟨v, this, e⟩
  exact (exists_unique_congr iff).mpr this
-/

section div

lemma div_exists_unique (a b : M) : ∃! u, (0 < b → b * u ≤ a ∧ a < b * (u + 1)) ∧ (b = 0 → u = 0) := by
  have : 0 ≤ b := by exact zero_le b
  rcases this with (rfl | pos) <;> simp [*]
  · simpa [pos_iff_ne_zero.mp pos] using div_exists_unique_pos a pos

instance : Div M := ⟨fun a b ↦ Classical.choose! (div_exists_unique a b)⟩

lemma mul_div_le_pos (a : M) (h : 0 < b) : b * (a / b) ≤ a := ((Classical.choose!_spec (div_exists_unique a b)).1 h).1

lemma lt_mul_div_succ (a : M) (h : 0 < b) : a < b * (a / b + 1) := ((Classical.choose!_spec (div_exists_unique a b)).1 h).2

lemma eq_mul_div_add_of_pos (a : M) {b} (hb : 0 < b) : ∃ r < b, a = b * (a / b) + r := by
  let r := a - b * (a / b)
  have e : a = b * (a / b) + r := by simp [add_tsub_self_of_le (mul_div_le_pos a hb)]
  exact ⟨r, by
    by_contra A
    have hyv : b ≤ r := by simpa using A
    have : a < a := by calc
          a < b * (a / b + 1) := lt_mul_div_succ a hb
          _ ≤ b * (a / b) + r := by simpa [mul_add] using hyv
          _ = a               := e.symm
    simp at this, e⟩

@[simp] lemma div_spec_zero (a : M) : a / 0 = 0 := (Classical.choose!_spec (div_exists_unique a 0)).2 (by simp)

lemma div_graph {a b c : M} : c = a / b ↔ ((0 < b → b * c ≤ a ∧ a < b * (c + 1)) ∧ (b = 0 → c = 0)) :=
  Classical.choose!_eq_iff _

def divdef : Σᴬ[0] 3 :=
  ⟨“(0 < #2 → #2 * #0 ≤ #1 ∧ #1 < #2 * (#0 + 1)) ∧ (#2 = 0 → #0 = 0)”, by simp[Hierarchy.pi_zero_iff_sigma_zero]⟩

lemma div_defined : Σᴬ[0]-Function₂ ((· / ·) : M → M → M) divdef := by
  intro v; simp[div_graph, divdef, Matrix.vecHead, Matrix.vecTail]

lemma div_spec_of_pos' (a : M) (h : 0 < b) : ∃ v < b, a = (a / b) * b + v := by
  simpa [mul_comm] using eq_mul_div_add_of_pos a h

lemma div_eq_of {b : M} (hb : b * c ≤ a) (ha : a < b * (c + 1)) : a / b = c := by
  have pos : 0 < b := pos_of_mul_pos_left (pos_of_gt ha) (by simp)
  exact (div_exists_unique_pos a pos).unique ⟨mul_div_le_pos a pos, lt_mul_div_succ a pos⟩ ⟨hb, ha⟩

lemma div_mul_add (a b : M) {r} (hr : r < b) : (a * b + r) / b = a :=
  div_eq_of (by simp [mul_comm]) (by simp [mul_comm b a, mul_add, hr])

lemma div_mul_add' (a b : M) {r} (hr : r < b) : (b * a + r) / b = a := by simpa [mul_comm] using div_mul_add a b hr

@[simp] lemma zero_div (a : M) : 0 / a = 0 := by
  rcases zero_le a with (rfl | pos)
  · simp
  · exact div_eq_of (by simp) (by simpa)

lemma div_mul (a b c : M) : a / (b * c) = a / b / c := by
  rcases zero_le b with (rfl | hb)
  · simp
  rcases zero_le c with (rfl | hc)
  · simp
  exact div_eq_of
    (by calc
          b * c * (a / b / c) ≤ b * (a / b) := by simp [mul_assoc]; exact mul_le_mul_left (mul_div_le_pos (a / b) hc)
          _                   ≤ a := mul_div_le_pos a hb)
    (by calc
          a < b * (a / b + 1)         := lt_mul_div_succ a hb
          _ ≤ b * c * (a / b / c + 1) := by simp [mul_assoc]; exact mul_le_mul_left (lt_iff_succ_le.mp <| lt_mul_div_succ (a / b) hc))

@[simp] lemma mul_div_le (a b : M) : b * (a / b) ≤ a := by
  have : 0 ≤ b := by exact zero_le b
  rcases this with (rfl | pos) <;> simp [*]
  rcases eq_mul_div_add_of_pos a pos with ⟨v, _, e⟩
  simpa [← e] using show b * (a / b) ≤ b * (a / b) + v from le_self_add

@[simp] lemma div_le (a b : M) : a / b ≤ a := by
  have : 0 ≤ b := zero_le b
  rcases this with (rfl | pos) <;> simp [*]
  have : 1 * (a / b) ≤ b * (a / b) := mul_le_mul_of_nonneg_right (le_iff_lt_succ.mpr (by simp[pos])) (by simp)
  simpa using le_trans this (mul_div_le a b)

instance div_polybounded : PolyBounded₂ ((· / ·) : M → M → M) := ⟨#0, λ _ ↦ by simp⟩

instance : DefinableFunction₂ b s ((· / ·) : M → M → M) := defined_to_with_param₀ _ div_defined

@[simp] lemma div_mul_le (a b : M) : a / b * b ≤ a := by rw [mul_comm]; exact mul_div_le _ _

lemma lt_mul_div (a : M) {b} (pos : 0 < b) : a < b * (a / b + 1) := by
  rcases eq_mul_div_add_of_pos a pos with ⟨v, hv, e⟩
  calc a = b * (a / b) + v := e
       _ < b * (a / b + 1) := by simp [mul_add, hv]

@[simp] lemma div_one (a : M) : a / 1 = a :=
  le_antisymm (by simp) (le_iff_lt_succ.mpr $ by simpa using lt_mul_div a one_pos)

lemma div_add_mul_self (a c : M) {b} (pos : 0 < b) : (a + c * b) / b = a / b + c := by
  rcases div_spec_of_pos' a pos with ⟨r, hr, ex⟩
  simpa [add_mul, add_right_comm, ← ex] using div_mul_add (a / b + c) _ hr

lemma div_add_mul_self' (a c : M) {b} (pos : 0 < b) : (a + b * c) / b = a / b + c := by
  simpa [mul_comm] using div_add_mul_self a c pos

lemma div_mul_add_self (a c : M) {b} (pos : 0 < b) : (a * b + c) / b = a + c / b := by
  simp [div_add_mul_self, pos, add_comm]

lemma div_mul_add_self' (a c : M) {b} (pos : 0 < b) : (b * a + c) / b = a + c / b := by
  simp [mul_comm b a, div_mul_add_self, pos]

@[simp] lemma div_mul_left (a : M) {b} (pos : 0 < b) : (a * b) / b = a := by
  simpa using div_mul_add a _ pos

@[simp] lemma div_mul_right (a : M) {b} (pos : 0 < b) : (b * a) / b = a := by
  simpa [mul_comm] using div_mul_add a _ pos

@[simp] lemma div_eq_zero_of_lt (b : M) {a} (h : a < b) : a / b = 0 := by
  simpa using div_mul_add 0 b h

@[simp] lemma div_sq (a : M) : a^2 / a = a := by
  rcases zero_le a with (rfl | pos)
  · simp
  · simp [sq, pos]

@[simp] lemma div_self {a : M} (hx : 0 < a) : a / a = 1 := by
  simpa using div_mul_left 1 hx

@[simp] lemma div_mul' (a : M) {b} (pos : 0 < b) : (b * a) / b = a := by simp [mul_comm, pos]

@[simp] lemma div_add_self_left {a} (pos : 0 < a) (b : M) : (a + b) / a = 1 + b / a := by
  simpa using div_mul_add_self 1 b pos

@[simp] lemma div_add_self_right (a : M) {b} (pos : 0 < b) : (a + b) / b = a / b + 1 := by
  simpa using div_add_mul_self a 1 pos

lemma mul_div_self_of_dvd {a b : M} : a * (b / a) = b ↔ a ∣ b := by
  rcases zero_le a with (rfl | pos)
  · simp[eq_comm]
  · constructor
    · intro e; rw [←e]; simp
    · rintro ⟨r, rfl⟩; simp [pos]

lemma div_lt_of_pos_of_one_lt {a b : M} (ha : 0 < a) (hb : 1 < b) : a / b < a := by
  rcases zero_le (a / b) with (e | lt)
  · simp [←e, ha]
  · exact lt_of_lt_of_le (lt_mul_of_one_lt_left lt hb) (mul_div_le a b)

lemma le_two_mul_div_two_add_one (a : M) : a ≤ 2 * (a / 2) + 1 := by
  have : a < 2 * (a / 2 + 1) := lt_mul_div_succ a (show 0 < 2 from by simp)
  exact le_iff_lt_succ.mpr (by simpa [add_assoc, one_add_one_eq_two, mul_add] using this)

lemma div_monotone {a b : M} (h : a ≤ b) (c : M) : a / c ≤ b / c := by
  rcases zero_le c with (rfl | pos)
  · simp
  by_contra A
  have : b / c + 1 ≤ a / c := succ_le_iff_lt.mpr (by simpa using A)
  have : a < a := calc
    a ≤ b               := h
    _ < c * (b / c + 1) := lt_mul_div b pos
    _ ≤ c * (a / c)     := mul_le_mul_left this
    _ ≤ a               := mul_div_le a c
  simp_all

lemma div_lt_of_lt_mul {a b c : M} (h : a < b * c) : a / c < b := by
  by_contra hb
  simp at hb
  have : a < a := calc
    a < b * c     := h
    _ ≤ a / c * c := mul_le_mul_right hb
    _ ≤ a         := by simp
  simp_all

end div

section mod

def rem (a b : M) : M := a - b * (a / b)

instance : Mod M := ⟨rem⟩

lemma mod_def (a b : M) : a % b = a - b * (a / b) := rfl

def remdef : Σᴬ[0] 3 :=
  ⟨“∃[#0 < #2 + 1] (!divdef [#0, #2, #3] ∧ !subdef [#1, #2, #3 * #0])”, by simp⟩

lemma rem_graph (a b c : M) : a = b % c ↔ ∃ x ≤ b, (x = b / c ∧ a = b - c * x) := by
  simp [mod_def]; constructor
  · rintro rfl; exact ⟨b / c, by simp, rfl, by rfl⟩
  · rintro ⟨_, _, rfl, rfl⟩; simp

lemma rem_defined : Σᴬ[0]-Function₂ ((· % ·) : M → M → M) remdef := by
  intro v; simp [Matrix.vecHead, Matrix.vecTail, remdef,
    rem_graph, Semiformula.eval_substs, div_defined.pval, sub_defined.pval, le_iff_lt_succ]

instance : DefinableFunction₂ b s ((· % ·) : M → M → M) := defined_to_with_param₀ _ rem_defined

lemma div_add_mod (a b : M) : b * (a / b) + (a % b) = a :=
  add_tsub_self_of_le (mul_div_le a b)

@[simp] lemma mod_zero (a : M) : a % 0 = a := by simp [mod_def]

@[simp] lemma zero_mod (a : M) : 0 % a = 0 := by simp [mod_def]

@[simp] lemma mod_self (a : M) : a % a = 0 := by
  rcases zero_le a with (rfl | h)
  · simp
  · simp [mod_def, h]

lemma mod_mul_add_of_lt (a b : M) {r} (hr : r < b) : (a * b + r) % b = r := by
  simp [mod_def, div_mul_add a b hr, mul_comm]

@[simp] lemma mod_mul_add (a c : M) (pos : 0 < b) : (a * b + c) % b = c % b := by
  simp [mod_def, div_mul_add_self, pos, mul_add, ←sub_sub, show b * a = a * b from mul_comm _ _]

@[simp] lemma mod_add_mul (a b : M) (pos : 0 < c) : (a + b * c) % c = a % c := by
  simp [add_comm a (b * c), pos]

@[simp] lemma mod_add_mul' (a b : M) (pos : 0 < c) : (a + c * b) % c = a % c := by
  simp [mul_comm c b, pos]

@[simp] lemma mod_mul_add' (a c : M) (pos : 0 < b) : (b * a + c) % b = c % b := by
  simp [mul_comm b a, pos]

@[simp] lemma mod_mul_self_left (a b : M) : (a * b) % b = 0 := by
  rcases zero_le b with (rfl | h)
  · simp
  · simpa using mod_mul_add_of_lt a b h

@[simp] lemma mod_mul_self_right (a b : M) : (b * a) % b = 0 := by
  simp [mul_comm]

@[simp] lemma mod_eq_self_of_lt {a b : M} (h : a < b) : a % b = a := by
  simpa using mod_mul_add_of_lt 0 b h

@[simp] lemma mod_lt (a : M) {b} (pos : 0 < b) : a % b < b := by
  rcases div_spec_of_pos' a pos with ⟨r, hr, ha⟩
  have : ((a / b) * b + r) % b = r := mod_mul_add_of_lt _ _ hr
  have : a % b = r := by simpa [←ha] using this
  simp [this, hr]

@[simp] lemma mod_le (a b : M) : a % b ≤ a := by
  simp [mod_def]

instance mod_polybounded : PolyBounded₂ ((· % ·) : M → M → M) := ⟨#0, by intro v; simp⟩

lemma mod_eq_zero_iff_dvd {a b : M} : b % a = 0 ↔ a ∣ b := by
  simp [mod_def]
  constructor
  · intro H; exact mul_div_self_of_dvd.mp (le_antisymm (mul_div_le b a) H)
  · intro H; simp [mul_div_self_of_dvd.mpr H]

@[simp] lemma mod_add_remove_right {a b : M} (pos : 0 < b) : (a + b) % b = a % b := by
  simpa using mod_add_mul a 1 pos

lemma mod_add_remove_right_of_dvd {a b m : M} (h : m ∣ b) (pos : 0 < m) : (a + b) % m = a % m := by
  rcases h with ⟨b, rfl⟩; simp [pos]

@[simp] lemma mod_add_remove_left {a b : M} (pos : 0 < a) : (a + b) % a = b % a := by
  simpa using mod_mul_add 1 b pos

lemma mod_add_remove_left_of_dvd {a b m : M} (h : m ∣ a) (pos : 0 < m) : (a + b) % m = b % m := by
  rcases h with ⟨b, rfl⟩; simp [pos]

lemma mod_add {a b m : M} (pos : 0 < m) : (a + b) % m = (a % m + b % m) % m := calc
  (a + b) % m = ((m * (a / m) + a % m) + (m * (b / m) + b % m)) % m := by simp [div_add_mod]
  _           = (m * (a / m) + m * (b / m) + (a % m) + (b % m)) % m := by simp [←add_assoc, add_right_comm]
  _           = (a % m + b % m) % m                                 := by simp [add_assoc, pos]

lemma mod_mul {a b m : M} (pos : 0 < m) : (a * b) % m = ((a % m) * (b % m)) % m := calc
  (a * b) % m = ((m * (a / m) + (a % m)) * (m * (b / m) + b % m)) % m := by simp [div_add_mod]
  _           = ((a % m) * (b % m)) % m                               := by simp [add_mul, mul_add, pos, mul_left_comm _ m, add_assoc, mul_assoc]

@[simp] lemma mod_div (a b : M) : a % b / b = 0 := by
  rcases zero_le b with (rfl | pos)
  · simp
  · exact div_eq_zero_of_lt b (by simp [pos])

@[simp] lemma mod_one (a : M) : a % 1 = 0 := lt_one_iff_eq_zero.mp <| mod_lt a (by simp)

lemma mod_two (a : M) : a % 2 = 0 ∨ a % 2 = 1 :=
  le_one_iff_eq_zero_or_one.mp <| lt_two_iff_le_one.mp <| mod_lt a (b := 2) (by simp)

@[simp] lemma mod_two_not_zero_iff {a : M} : ¬a % 2 = 0 ↔ a % 2 = 1 := by
  rcases mod_two a with (h | h) <;> simp [*]

@[simp] lemma mod_two_not_one_iff {a : M} : ¬a % 2 = 1 ↔ a % 2 = 0 := by
  rcases mod_two a with (h | h) <;> simp [*]

end mod

lemma two_dvd_mul {a b : M} : 2 ∣ a * b → 2 ∣ a ∨ 2 ∣ b := by
  intro H; by_contra A
  simp [not_or] at A
  have ha : a % 2 = 1 := by
    have : a % 2 = 0 ∨ a % 2 = 1 := mod_two a
    simpa [show a % 2 ≠ 0 from by simpa [←mod_eq_zero_iff_dvd] using A.1] using this
  have hb : b % 2 = 1 := by
    have : b % 2 = 0 ∨ b % 2 = 1 :=
      le_one_iff_eq_zero_or_one.mp <| lt_two_iff_le_one.mp <| mod_lt b (b := 2) (by simp)
    simpa [show b % 2 ≠ 0 from by simpa [←mod_eq_zero_iff_dvd] using A.2] using this
  have : a * b % 2 = 1 := by simp [mod_mul, ha, hb]; exact mod_eq_self_of_lt one_lt_two
  have : ¬2 ∣ a * b := by simp [←mod_eq_zero_iff_dvd, this]
  contradiction

lemma even_or_odd (a : M) : ∃ x, a = 2 * x ∨ a = 2 * x + 1 :=
  ⟨a / 2, by
    have : 2 * (a / 2) + (a % 2) = a := div_add_mod a 2
    rcases mod_two a with (e | e) <;> { simp[e] at this; simp [this] }⟩

lemma even_or_odd' (a : M) : a = 2 * (a / 2) ∨ a = 2 * (a / 2) + 1 := by
  have : 2 * (a / 2) + (a % 2) = a := div_add_mod a 2
  rcases mod_two a with (e | e) <;>  simp [e] at this <;> simp [*]

lemma two_prime : Prime (2 : M) := ⟨by simp, by simp, by intro a b h; exact two_dvd_mul h⟩

section sqrt

lemma sqrt_exists_unique (a : M) : ∃! x, x * x ≤ a ∧ a < (x + 1) * (x + 1) := by
  have : ∃ x, x * x ≤ a ∧ a < (x + 1) * (x + 1) := by
    have : a < (a + 1) * (a + 1) → ∃ x, x * x ≤ a ∧ a < (x + 1) * (x + 1) := by
      simpa using open_leastNumber (P := λ x ↦ x * x ≤ a) ⟨“#0 * #0 ≤ &a”, by simp, by simp⟩
    have hn : a < (a + 1) * (a + 1) := calc
      a ≤ a * a             := le_mul_self a
      _ < a * a + 1         := lt_add_one (a * a)
      _ ≤ (a + 1) * (a + 1) := by simp [add_mul_self_eq]
    exact this hn
  rcases this with ⟨x, hx⟩
  exact ExistsUnique.intro x hx (by
    intro y hy
    by_contra ne
    wlog lt : x < y
    · exact this a y hy x hx (Ne.symm ne) (Ne.lt_of_le ne $ by simpa using lt)
    have : a < a := calc
      a < (x + 1) * (x + 1) := hx.2
      _ ≤ y * y             := mul_self_le_mul_self (by simp) (lt_iff_succ_le.mp lt)
      _ ≤ a                 := hy.1
    simp at this)

def sqrt (a : M) : M := Classical.choose! (sqrt_exists_unique a)

prefix:75 "√" => sqrt

@[simp] lemma sqrt_spec_le (a : M) : √a * √a ≤ a := (Classical.choose!_spec (sqrt_exists_unique a)).1

@[simp] lemma sqrt_spec_lt (a : M) : a < (√a + 1) * (√a + 1) := (Classical.choose!_spec (sqrt_exists_unique a)).2

lemma sqrt_graph {a b : M} : b = √a ↔ b * b ≤ a ∧ a < (b + 1) * (b + 1) := Classical.choose!_eq_iff _

def sqrtdef : Σᴬ[0] 2 :=
  ⟨“#0 * #0 ≤ #1 ∧ #1 < (#0 + 1) * (#0 + 1)”, by simp[Hierarchy.pi_zero_iff_sigma_zero]⟩

lemma sqrt_defined : Σᴬ[0]-Function₁ (λ a : M ↦ √a) sqrtdef := by
  intro v; simp[sqrt_graph, sqrtdef, Matrix.vecHead, Matrix.vecTail]

instance : DefinableFunction₁ b s ((√·) : M → M) := defined_to_with_param₀ _ sqrt_defined

lemma eq_sqrt (x a : M) : x * x ≤ a ∧ a < (x + 1) * (x + 1) → x = √a := Classical.choose_uniq (sqrt_exists_unique a)

lemma sqrt_eq_of_le_of_lt {x a : M} (le : x * x ≤ a) (lt : a < (x + 1) * (x + 1)) : √a = x :=
  Eq.symm <| eq_sqrt x a ⟨le, lt⟩

lemma sqrt_eq_of_le_of_le {x a : M} (le : x * x ≤ a) (h : a ≤ x * x + 2 * x) : √a = x :=
  sqrt_eq_of_le_of_lt le (by simp [add_mul_self_eq]; exact le_iff_lt_succ.mp h)

@[simp] lemma sq_sqrt_le (a : M) : (√a) ^ 2 ≤ a := by simp [sq]

@[simp] lemma sqrt_lt_sq (a : M) : a < (√a + 1) ^ 2 := by simp [sq]

@[simp] lemma sqrt_mul_self (a : M) : √(a * a) = a :=
  Eq.symm <| eq_sqrt a (a * a) (by simp; exact mul_self_lt_mul_self (by simp) (by simp))

@[simp] lemma sqrt_sq (a : M) : √(a^2) = a := by simp [sq]

@[simp] lemma sqrt_zero : √(0 : M) = 0 := by simpa using sqrt_mul_self (0 : M)

@[simp] lemma sqrt_one : √(1 : M) = 1 := by simpa using sqrt_mul_self (1 : M)

lemma sqrt_two : √(2 : M) = 1 :=
  Eq.symm <| eq_sqrt 1 2 (by simp [one_le_two, one_add_one_eq_two, one_lt_two])

lemma sqrt_three : √(3 : M) = 1 :=
  Eq.symm <| eq_sqrt 1 3 (by
    simp [one_add_one_eq_two, two_mul_two_eq_four]
    constructor
    · simp [←two_add_one_eq_three]
    · simp [←three_add_one_eq_four])

@[simp] lemma sqrt_four : √(4 : M) = 2 := by
  simp [←two_mul_two_eq_four]

@[simp] lemma two_ne_square (a : M) : 2 ≠ a^2 := by
  intro h
  rcases show a = √2 from by rw [h]; simp with rfl
  simp [sqrt_two] at h

@[simp] lemma sqrt_le_add (a : M) : a ≤ √a * √a + 2 * √a :=
  le_iff_lt_succ.mpr (by have := sqrt_spec_lt a; rw [add_mul_self_eq] at this; simpa using this)

@[simp] lemma sqrt_le_self (a : M) : √a ≤ a := by
  by_contra A
  have : a < a := calc
    a ≤ a^2    := le_sq a
    _ < (√a)^2 := by simpa [sq] using mul_self_lt_mul_self (by simp) (by simpa using A)
    _ ≤ a      := sq_sqrt_le a
  simp_all

instance : PolyBounded₁ ((√·) : M → M) := ⟨#0, by intro v; simp⟩

lemma sqrt_lt_self_of_one_lt {a : M} (h : 1 < a) : √a < a := by
  by_contra A
  have : a * a ≤ √a * √a := mul_self_le_mul_self (by simp) (by simpa using A)
  have : a * a ≤ a := le_trans this (sqrt_spec_le a)
  exact not_lt.mpr this (lt_mul_self h)

lemma sqrt_le_of_le_sq {a b : M} : a ≤ b^2 → √a ≤ b := by
  intro h; by_contra A
  have : a < a := calc
    a ≤ b^2    := h
    _ < (√a)^2 := sq_lt_sq.mpr (by simpa using A)
    _ ≤ a      := by simp
  simp_all

lemma sq_lt_of_lt_sqrt {a b : M} : a < √b → a^2 < b := by
  intro h; by_contra A
  exact not_le.mpr h (sqrt_le_of_le_sq $ show b ≤ a^2 from by simpa using A)

end sqrt

section pair

open Classical

-- https://github.com/leanprover-community/mathlib4/blob/b075cdd0e6ad8b5a3295e7484b2ae59e9b2ec2a7/Mathlib/Data/Nat/Pairing.lean#L37
def pair (a b : M) : M := if a < b then b * b + a else a * a + a + b

notation "⟪" a ", " b "⟫" => pair a b

lemma pair_graph {a b c : M} :
    c = ⟪a, b⟫ ↔ (a < b ∧ c = b * b + a) ∨ (b ≤ a ∧ c = a * a + a + b) := by
  simp [pair]
  by_cases h : a < b
  · simp [h, show ¬b ≤ a from by simpa using h]
  · simp [h, show b ≤ a from by simpa using h]

def pairdef : Σᴬ[0] 3 := ⟨“(#1 < #2 ∧ #0 = #2 * #2 + #1) ∨ (#2 ≤ #1 ∧ #0 = #1 * #1 + #1 + #2)”, by simp⟩

lemma pair_defined : Σᴬ[0]-Function₂ (λ a b : M ↦ ⟪a, b⟫) pairdef := by
  intro v; simp [pair_graph, pairdef]

instance {b s} : DefinableFunction₂ b s (pair : M → M → M) := defined_to_with_param₀ _ pair_defined

instance : PolyBounded₂ (pair : M → M → M) :=
  ⟨ᵀ“(#1 * #1 + #0) + (#0 * #0 + #0 + #1)”, by intro v; simp [pair]; split_ifs <;> try simp [pair, *]⟩

def unpair (a : M) : M × M := if a - √a * √a < √a then (a - √a * √a, √a) else (√a, a - √a * √a - √a)

abbrev pi₁ (a : M) : M := (unpair a).1

abbrev pi₂ (a : M) : M := (unpair a).2

prefix: 80 "π₁" => pi₁

prefix: 80 "π₂" => pi₂

@[simp] lemma pair_unpair (a : M) : ⟪π₁ a, π₂ a⟫ = a := by
  simp [pi₁, pi₂, unpair]
  split_ifs with h
  · simp [pair, h]
  · simp; simp [pair, h]
    have : a - √a * √a - √a ≤ √a := by simp [add_comm (2 * √a), ←two_mul]
    simp [not_lt.mpr this]
    have :√a ≤ a - √a * √a := by simpa using h
    calc
      √a * √a + √a + (a - √a * √a - √a) = √a * √a + (a - √a * √a) := by simp [add_assoc]
                                                                        rw [add_tsub_self_of_le, add_tsub_self_of_le] <;> simp [this]
      _                                 = a                       := add_tsub_self_of_le (by simp)

@[simp] lemma unpair_pair (a b : M) : unpair ⟪a, b⟫ = (a, b) := by
  simp [pair]; split_ifs with h
  · have : √(b * b + a) = b := sqrt_eq_of_le_of_le (by simp) (by simp; exact le_trans (le_of_lt h) (by simp))
    simp [unpair, this, show ¬b ≤ a from by simpa using h]
  · have : √(a * a + (a + b)) = a :=
      sqrt_eq_of_le_of_le (by simp [add_assoc]) (by simp [add_assoc, two_mul, show b ≤ a from by simpa using h])
    simp [unpair, this, add_assoc]

@[simp] lemma pi₁_pair (a b : M) : π₁ ⟪a, b⟫ = a := by simp [pi₁]

@[simp] lemma pi₂_pair (a b : M) : π₂ ⟪a, b⟫ = b := by simp [pi₂]

def pairEquiv : M × M ≃ M := ⟨Function.uncurry pair, unpair, fun ⟨a, b⟩ => unpair_pair a b, pair_unpair⟩

@[simp] lemma pi₁_le_self (a : M) : π₁ a ≤ a := by simp [pi₁, unpair]; split_ifs <;> simp

@[simp] lemma pi₂_le_self (a : M) : π₂ a ≤ a := by simp [pi₂, unpair]; split_ifs <;> simp [add_assoc]

instance : PolyBounded₁ (pi₁ : M → M) := ⟨ᵀ“#0”, by intro v; simp⟩

instance : PolyBounded₁ (pi₂ : M → M) := ⟨ᵀ“#0”, by intro v; simp⟩

def pi₁def : Σᴬ[0] 2 := ⟨“∃[#0 < #2 + 1] !pairdef [#2, #1, #0]”, by simp⟩

def pi₂def : Σᴬ[0] 2 := ⟨“∃[#0 < #2 + 1] !pairdef [#2, #0, #1]”, by simp⟩

lemma pi₁_defined : Σᴬ[0]-Function₁ (pi₁ : M → M) pi₁def := by
  intro v; simp [pi₁def, pair_defined.pval]
  constructor
  · intro h; exact ⟨π₂ v 1, by simp [←le_iff_lt_succ],  by simp [h]⟩
  · rintro ⟨a, _, e⟩; simp [e]

instance {b s} : DefinableFunction₁ b s (pi₁ : M → M) := defined_to_with_param₀ _ pi₁_defined

lemma pi₂_defined : Σᴬ[0]-Function₁ (pi₂ : M → M) pi₂def := by
  intro v; simp [pi₂def, pair_defined.pval]
  constructor
  · intro h; exact ⟨π₁ v 1, by simp [←le_iff_lt_succ], by simp [h]⟩
  · rintro ⟨a, _, e⟩; simp [e]

instance {b s} : DefinableFunction₁ b s (pi₂ : M → M) := defined_to_with_param₀ _ pi₂_defined

end pair

end IOpen

@[elab_as_elim]
lemma hierarchy_polynomial_induction (b : VType) (s : ℕ) [(𝐈𝚪 b s).Mod M] {P : M → Prop} (hP : DefinablePred b s P)
    (zero : P 0) (even : ∀ x > 0, P x → P (2 * x)) (odd : ∀ x, P x → P (2 * x + 1)) : ∀ x, P x := by
  haveI : 𝐈open.Mod M := mod_IOpen_of_mod_IHierarchy b s
  intro x; induction x using hierarchy_order_induction
  · exact b
  · exact s
  · exact hP
  case inst => exact inferInstance
  case ind x IH =>
    rcases zero_le x with (rfl | pos)
    · exact zero
    · have : x / 2 < x := div_lt_of_pos_of_one_lt pos one_lt_two
      rcases even_or_odd' x with (hx | hx)
      · simpa [←hx] using even (x / 2) (by by_contra A; simp at A; simp [show x = 0 from by simpa [A] using hx] at pos) (IH (x / 2) this)
      · simpa [←hx] using odd (x / 2) (IH (x / 2) this)

@[elab_as_elim] lemma hierarchy_polynomial_induction_sigma₀ [𝐈𝚺₀.Mod M] {P : M → Prop} (hP : DefinablePred Σ 0 P)
    (zero : P 0) (even : ∀ x > 0, P x → P (2 * x)) (odd : ∀ x, P x → P (2 * x + 1)) : ∀ x, P x :=
  hierarchy_polynomial_induction Σ 0 hP zero even odd

@[elab_as_elim] lemma hierarchy_polynomial_induction_sigma₁ [𝐈𝚺₁.Mod M] {P : M → Prop} (hP : DefinablePred Σ 1 P)
    (zero : P 0) (even : ∀ x > 0, P x → P (2 * x)) (odd : ∀ x, P x → P (2 * x + 1)) : ∀ x, P x :=
  hierarchy_polynomial_induction Σ 1 hP zero even odd

@[elab_as_elim] lemma hierarchy_polynomial_induction_pi₁ [𝐈𝚷₁.Mod M] {P : M → Prop} (hP : DefinablePred Π 1 P)
    (zero : P 0) (even : ∀ x > 0, P x → P (2 * x)) (odd : ∀ x, P x → P (2 * x + 1)) : ∀ x, P x :=
  hierarchy_polynomial_induction Π 1 hP zero even odd

end Model

end

end Arith

end LO.FirstOrder
