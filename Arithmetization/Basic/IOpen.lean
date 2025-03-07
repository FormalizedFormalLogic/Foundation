import Arithmetization.Basic.Ind
import Mathlib.Logic.Nonempty

namespace LO.Arith

open FirstOrder FirstOrder.Arith

noncomputable section

variable {V : Type*} [ORingStruc V]

section IOpen

variable [V ⊧ₘ* 𝐈open]

@[elab_as_elim]
lemma open_induction {P : V → Prop}
    (hP : ∃ p : Semiformula ℒₒᵣ V 1, p.Open ∧ ∀ x, P x ↔ Semiformula.Evalm V ![x] id p)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  induction (C := Semiformula.Open)
    (by rcases hP with ⟨p, hp, hhp⟩
        haveI : Inhabited V := Classical.inhabited_of_nonempty'
        exact ⟨p.fvarEnumInv, Rew.rewriteMap p.fvarEnum ▹ p, by simp[hp],
          by  intro x; simp [Semiformula.eval_rewriteMap, hhp]
              exact Semiformula.eval_iff_of_funEqOn p (by
                intro z hz
                simp [Semiformula.fvarEnumInv_fvarEnum (Semiformula.mem_fvarList_iff_fvar?.mpr hz)])⟩) zero succ

lemma open_leastNumber {P : V → Prop}
    (hP : ∃ p : Semiformula ℒₒᵣ V 1, p.Open ∧ ∀ x, P x ↔ Semiformula.Evalm V ![x] id p)
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

lemma div_exists_unique_pos (a : V) {b} (pos : 0 < b) : ∃! u, b * u ≤ a ∧ a < b * (u + 1) := by
  have : ∃ u, b * u ≤ a ∧ a < b * (u + 1) := by
    have : a < b * (a + 1) → ∃ u, b * u ≤ a ∧ a < b * (u + 1) := by
      simpa using open_leastNumber (P := fun u ↦ b * u ≤ a) ⟨“x. &b * x ≤ &a”, by simp, by intro x; simp⟩
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

section div

lemma div_exists_unique (a b : V) : ∃! u, (0 < b → b * u ≤ a ∧ a < b * (u + 1)) ∧ (b = 0 → u = 0) := by
  have : 0 ≤ b := by exact zero_le b
  rcases this with (rfl | pos) <;> simp [*]
  · simpa [pos_iff_ne_zero.mp pos] using div_exists_unique_pos a pos

scoped instance : Div V := ⟨fun a b ↦ Classical.choose! (div_exists_unique a b)⟩

lemma mul_div_le_pos (a : V) (h : 0 < b) : b * (a / b) ≤ a := ((Classical.choose!_spec (div_exists_unique a b)).1 h).1

lemma lt_mul_div_succ (a : V) (h : 0 < b) : a < b * (a / b + 1) := ((Classical.choose!_spec (div_exists_unique a b)).1 h).2

lemma eq_mul_div_add_of_pos (a : V) {b} (hb : 0 < b) : ∃ r < b, a = b * (a / b) + r := by
  let r := a - b * (a / b)
  have e : a = b * (a / b) + r := by simp [r, add_tsub_self_of_le (mul_div_le_pos a hb)]
  exact ⟨r, by
    by_contra A
    have hyv : b ≤ r := by simpa using A
    have : a < a := by calc
          a < b * (a / b + 1) := lt_mul_div_succ a hb
          _ ≤ b * (a / b) + r := by simpa [mul_add] using hyv
          _ = a               := e.symm
    simp at this, e⟩

@[simp] lemma div_spec_zero (a : V) : a / 0 = 0 := (Classical.choose!_spec (div_exists_unique a 0)).2 (by simp)

lemma div_graph {a b c : V} : c = a / b ↔ ((0 < b → b * c ≤ a ∧ a < b * (c + 1)) ∧ (b = 0 → c = 0)) :=
  Classical.choose!_eq_iff _

def _root_.LO.FirstOrder.Arith.divDef : 𝚺₀.Semisentence 3 :=
  .mkSigma “c a b. (0 < b → b * c ≤ a ∧ a < b * (c + 1)) ∧ (b = 0 → c = 0)” (by simp[Hierarchy.pi_zero_iff_sigma_zero])

lemma div_defined : 𝚺₀-Function₂ ((· / ·) : V → V → V) via divDef := by
  intro v; simp[div_graph, divDef, Matrix.vecHead, Matrix.vecTail]

@[simp] lemma div_defined_iff (v) :
    Semiformula.Evalbm V v divDef.val ↔ v 0 = v 1 / v 2 := div_defined.df.iff v

lemma div_spec_of_pos' (a : V) (h : 0 < b) : ∃ v < b, a = (a / b) * b + v := by
  simpa [mul_comm] using eq_mul_div_add_of_pos a h

lemma div_eq_of {b : V} (hb : b * c ≤ a) (ha : a < b * (c + 1)) : a / b = c := by
  have pos : 0 < b := pos_of_mul_pos_left (pos_of_gt ha) (by simp)
  exact (div_exists_unique_pos a pos).unique ⟨mul_div_le_pos a pos, lt_mul_div_succ a pos⟩ ⟨hb, ha⟩

lemma div_mul_add (a b : V) {r} (hr : r < b) : (a * b + r) / b = a :=
  div_eq_of (by simp [mul_comm]) (by simp [mul_comm b a, mul_add, hr])

lemma div_mul_add' (a b : V) {r} (hr : r < b) : (b * a + r) / b = a := by simpa [mul_comm] using div_mul_add a b hr

@[simp] lemma zero_div (a : V) : 0 / a = 0 := by
  rcases zero_le a with (rfl | pos)
  · simp
  · exact div_eq_of (by simp) (by simpa)

lemma div_mul (a b c : V) : a / (b * c) = a / b / c := by
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

@[simp] lemma mul_div_le (a b : V) : b * (a / b) ≤ a := by
  have : 0 ≤ b := by exact zero_le b
  rcases this with (rfl | pos) <;> simp [*]
  rcases eq_mul_div_add_of_pos a pos with ⟨v, _, e⟩
  simpa [← e] using show b * (a / b) ≤ b * (a / b) + v from le_self_add

@[simp] lemma div_le (a b : V) : a / b ≤ a := by
  have : 0 ≤ b := zero_le b
  rcases this with (rfl | pos) <;> simp [*]
  have : 1 * (a / b) ≤ b * (a / b) := mul_le_mul_of_nonneg_right (le_iff_lt_succ.mpr (by simp[pos])) (by simp)
  simpa using le_trans this (mul_div_le a b)

instance div_polybounded : Bounded₂ ((· / ·) : V → V → V) := ⟨#0, λ _ ↦ by simp⟩

instance div_definable : 𝚺₀-Function₂ ((· / ·) : V → V → V) := div_defined.to_definable _

@[simp] lemma div_mul_le (a b : V) : a / b * b ≤ a := by rw [mul_comm]; exact mul_div_le _ _

lemma lt_mul_div (a : V) {b} (pos : 0 < b) : a < b * (a / b + 1) := by
  rcases eq_mul_div_add_of_pos a pos with ⟨v, hv, e⟩
  calc a = b * (a / b) + v := e
       _ < b * (a / b + 1) := by simp [mul_add, hv]

@[simp] lemma div_one (a : V) : a / 1 = a :=
  le_antisymm (by simp) (le_iff_lt_succ.mpr $ by simpa using lt_mul_div a one_pos)

lemma div_add_mul_self (a c : V) {b} (pos : 0 < b) : (a + c * b) / b = a / b + c := by
  rcases div_spec_of_pos' a pos with ⟨r, hr, ex⟩
  simpa [add_mul, add_right_comm, ← ex] using div_mul_add (a / b + c) _ hr

lemma div_add_mul_self' (a c : V) {b} (pos : 0 < b) : (a + b * c) / b = a / b + c := by
  simpa [mul_comm] using div_add_mul_self a c pos

lemma div_mul_add_self (a c : V) {b} (pos : 0 < b) : (a * b + c) / b = a + c / b := by
  simp [div_add_mul_self, pos, add_comm]

lemma div_mul_add_self' (a c : V) {b} (pos : 0 < b) : (b * a + c) / b = a + c / b := by
  simp [mul_comm b a, div_mul_add_self, pos]

@[simp] lemma div_mul_left (a : V) {b} (pos : 0 < b) : (a * b) / b = a := by
  simpa using div_mul_add a _ pos

@[simp] lemma div_mul_right (a : V) {b} (pos : 0 < b) : (b * a) / b = a := by
  simpa [mul_comm] using div_mul_add a _ pos

@[simp] lemma div_eq_zero_of_lt (b : V) {a} (h : a < b) : a / b = 0 := by
  simpa using div_mul_add 0 b h

@[simp] lemma div_sq (a : V) : a^2 / a = a := by
  rcases zero_le a with (rfl | pos)
  · simp
  · simp [sq, pos]

@[simp] lemma div_self {a : V} (hx : 0 < a) : a / a = 1 := by
  simpa using div_mul_left 1 hx

@[simp] lemma div_mul' (a : V) {b} (pos : 0 < b) : (b * a) / b = a := by simp [mul_comm, pos]

@[simp] lemma div_add_self_left {a} (pos : 0 < a) (b : V) : (a + b) / a = 1 + b / a := by
  simpa using div_mul_add_self 1 b pos

@[simp] lemma div_add_self_right (a : V) {b} (pos : 0 < b) : (a + b) / b = a / b + 1 := by
  simpa using div_add_mul_self a 1 pos

lemma mul_div_self_of_dvd {a b : V} : a * (b / a) = b ↔ a ∣ b := by
  rcases zero_le a with (rfl | pos)
  · simp[eq_comm]
  · constructor
    · intro e; rw [←e]; simp
    · rintro ⟨r, rfl⟩; simp [pos]

lemma div_lt_of_pos_of_one_lt {a b : V} (ha : 0 < a) (hb : 1 < b) : a / b < a := by
  rcases zero_le (a / b) with (e | lt)
  · simp [←e, ha]
  · exact lt_of_lt_of_le (lt_mul_of_one_lt_left lt hb) (mul_div_le a b)

lemma le_two_mul_div_two_add_one (a : V) : a ≤ 2 * (a / 2) + 1 := by
  have : a < 2 * (a / 2 + 1) := lt_mul_div_succ a (show 0 < 2 from by simp)
  exact le_iff_lt_succ.mpr (by simpa [add_assoc, one_add_one_eq_two, mul_add] using this)

lemma div_monotone {a b : V} (h : a ≤ b) (c : V) : a / c ≤ b / c := by
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

lemma div_lt_of_lt_mul {a b c : V} (h : a < b * c) : a / c < b := by
  by_contra hb
  simp at hb
  have : a < a := calc
    a < b * c     := h
    _ ≤ a / c * c := mul_le_mul_right hb
    _ ≤ a         := by simp
  simp_all

lemma div_cancel_left {c} (pos : 0 < c) (a b : V) : (c * a) / (c * b) = a / b := by simp [div_mul, pos]

lemma div_cancel_right {c} (pos : 0 < c) (a b : V) : (a * c) / (b * c) = a / b := by simp [mul_comm _ c, div_cancel_left pos]

@[simp] lemma two_mul_add_one_div_two (a : V) : (2 * a + 1) / 2 = a := by simp [div_mul_add_self', one_lt_two]

end div

section mod

def rem (a b : V) : V := a - b * (a / b)

scoped instance : Mod V := ⟨rem⟩

lemma mod_def (a b : V) : a % b = a - b * (a / b) := rfl

def _root_.LO.FirstOrder.Arith.remDef : 𝚺₀.Semisentence 3 :=
  .mkSigma “c a b. ∃ d <⁺ a, !divDef.val d a b ∧ !subDef.val c a (b * d)” (by simp)

lemma rem_graph (a b c : V) : a = b % c ↔ ∃ x ≤ b, (x = b / c ∧ a = b - c * x) := by
  simp [mod_def]; constructor
  · rintro rfl; exact ⟨b / c, by simp, rfl, by rfl⟩
  · rintro ⟨_, _, rfl, rfl⟩; simp

lemma rem_defined : 𝚺₀-Function₂ ((· % ·) : V → V → V) via remDef := by
  intro v; simp [Matrix.vecHead, Matrix.vecTail, remDef, rem_graph, Semiformula.eval_substs, le_iff_lt_succ]

@[simp] lemma rem_defined_iff (v) :
    Semiformula.Evalbm V v remDef.val ↔ v 0 = v 1 % v 2 := rem_defined.df.iff v

instance rem_definable : 𝚺₀-Function₂ ((· % ·) : V → V → V) := rem_defined.to_definable _

lemma div_add_mod (a b : V) : b * (a / b) + (a % b) = a :=
  add_tsub_self_of_le (mul_div_le a b)

@[simp] lemma mod_zero (a : V) : a % 0 = a := by simp [mod_def]

@[simp] lemma zero_mod (a : V) : 0 % a = 0 := by simp [mod_def]

@[simp] lemma mod_self (a : V) : a % a = 0 := by
  rcases zero_le a with (rfl | h)
  · simp
  · simp [mod_def, h]

lemma mod_mul_add_of_lt (a b : V) {r} (hr : r < b) : (a * b + r) % b = r := by
  simp [mod_def, div_mul_add a b hr, mul_comm]

@[simp] lemma mod_mul_add (a c : V) (pos : 0 < b) : (a * b + c) % b = c % b := by
  simp [mod_def, div_mul_add_self, pos, mul_add, ←sub_sub, show b * a = a * b from mul_comm _ _]

@[simp] lemma mod_add_mul (a b : V) (pos : 0 < c) : (a + b * c) % c = a % c := by
  simp [add_comm a (b * c), pos]

@[simp] lemma mod_add_mul' (a b : V) (pos : 0 < c) : (a + c * b) % c = a % c := by
  simp [mul_comm c b, pos]

@[simp] lemma mod_mul_add' (a c : V) (pos : 0 < b) : (b * a + c) % b = c % b := by
  simp [mul_comm b a, pos]

@[simp] lemma mod_mul_self_left (a b : V) : (a * b) % b = 0 := by
  rcases zero_le b with (rfl | h)
  · simp
  · simpa using mod_mul_add_of_lt a b h

@[simp] lemma mod_mul_self_right (a b : V) : (b * a) % b = 0 := by
  simp [mul_comm]

@[simp] lemma mod_eq_self_of_lt {a b : V} (h : a < b) : a % b = a := by
  simpa using mod_mul_add_of_lt 0 b h

@[simp] lemma mod_lt (a : V) {b} (pos : 0 < b) : a % b < b := by
  rcases div_spec_of_pos' a pos with ⟨r, hr, ha⟩
  have : ((a / b) * b + r) % b = r := mod_mul_add_of_lt _ _ hr
  have : a % b = r := by simpa [←ha] using this
  simp [this, hr]

@[simp] lemma mod_le (a b : V) : a % b ≤ a := by
  simp [mod_def]

instance mod_polybounded : Bounded₂ ((· % ·) : V → V → V) := ⟨#0, by intro v; simp⟩

lemma mod_eq_zero_iff_dvd {a b : V} : b % a = 0 ↔ a ∣ b := by
  simp [mod_def]
  constructor
  · intro H; exact mul_div_self_of_dvd.mp (le_antisymm (mul_div_le b a) H)
  · intro H; simp [mul_div_self_of_dvd.mpr H]

@[simp] lemma mod_add_remove_right {a b : V} (pos : 0 < b) : (a + b) % b = a % b := by
  simpa using mod_add_mul a 1 pos

lemma mod_add_remove_right_of_dvd {a b m : V} (h : m ∣ b) (pos : 0 < m) : (a + b) % m = a % m := by
  rcases h with ⟨b, rfl⟩; simp [pos]

@[simp] lemma mod_add_remove_left {a b : V} (pos : 0 < a) : (a + b) % a = b % a := by
  simpa using mod_mul_add 1 b pos

lemma mod_add_remove_left_of_dvd {a b m : V} (h : m ∣ a) (pos : 0 < m) : (a + b) % m = b % m := by
  rcases h with ⟨b, rfl⟩; simp [pos]

lemma mod_add {a b m : V} (pos : 0 < m) : (a + b) % m = (a % m + b % m) % m := calc
  (a + b) % m = ((m * (a / m) + a % m) + (m * (b / m) + b % m)) % m := by simp [div_add_mod]
  _           = (m * (a / m) + m * (b / m) + (a % m) + (b % m)) % m := by simp [←add_assoc, add_right_comm]
  _           = (a % m + b % m) % m                                 := by simp [add_assoc, pos]

lemma mod_mul {a b m : V} (pos : 0 < m) : (a * b) % m = ((a % m) * (b % m)) % m := calc
  (a * b) % m = ((m * (a / m) + (a % m)) * (m * (b / m) + b % m)) % m := by simp [div_add_mod]
  _           = ((a % m) * (b % m)) % m                               := by simp [add_mul, mul_add, pos, mul_left_comm _ m, add_assoc, mul_assoc]

@[simp] lemma mod_div (a b : V) : a % b / b = 0 := by
  rcases zero_le b with (rfl | pos)
  · simp
  · exact div_eq_zero_of_lt b (by simp [pos])

@[simp] lemma mod_one (a : V) : a % 1 = 0 := lt_one_iff_eq_zero.mp <| mod_lt a (by simp)

lemma mod_two (a : V) : a % 2 = 0 ∨ a % 2 = 1 :=
  le_one_iff_eq_zero_or_one.mp <| lt_two_iff_le_one.mp <| mod_lt a (b := 2) (by simp)

@[simp] lemma mod_two_not_zero_iff {a : V} : ¬a % 2 = 0 ↔ a % 2 = 1 := by
  rcases mod_two a with (h | h) <;> simp [*]

@[simp] lemma mod_two_not_one_iff {a : V} : ¬a % 2 = 1 ↔ a % 2 = 0 := by
  rcases mod_two a with (h | h) <;> simp [*]

end mod

lemma two_dvd_mul {a b : V} : 2 ∣ a * b → 2 ∣ a ∨ 2 ∣ b := by
  intro H; by_contra A
  simp [not_or] at A
  have ha : a % 2 = 1 := by
    have : a % 2 = 0 ∨ a % 2 = 1 := mod_two a
    simpa [show a % 2 ≠ 0 from by simpa [←mod_eq_zero_iff_dvd] using A.1] using this
  have hb : b % 2 = 1 := by
    have : b % 2 = 0 ∨ b % 2 = 1 :=
      le_one_iff_eq_zero_or_one.mp <| lt_two_iff_le_one.mp <| mod_lt b (b := 2) (by simp)
    simpa [show b % 2 ≠ 0 from by simpa [←mod_eq_zero_iff_dvd] using A.2] using this
  have : a * b % 2 = 1 := by simp [mod_mul, ha, hb]
  have : ¬2 ∣ a * b := by simp [←mod_eq_zero_iff_dvd, this]
  contradiction

lemma even_or_odd (a : V) : ∃ x, a = 2 * x ∨ a = 2 * x + 1 :=
  ⟨a / 2, by
    have : 2 * (a / 2) + (a % 2) = a := div_add_mod a 2
    rcases mod_two a with (e | e) <;> { simp[e] at this; simp [this] }⟩

lemma even_or_odd' (a : V) : a = 2 * (a / 2) ∨ a = 2 * (a / 2) + 1 := by
  have : 2 * (a / 2) + (a % 2) = a := div_add_mod a 2
  rcases mod_two a with (e | e) <;>  simp [e] at this <;> simp [*]

lemma two_prime : Prime (2 : V) := ⟨by simp, by simp, by intro a b h; exact two_dvd_mul h⟩

section sqrt

lemma sqrt_exists_unique (a : V) : ∃! x, x * x ≤ a ∧ a < (x + 1) * (x + 1) := by
  have : ∃ x, x * x ≤ a ∧ a < (x + 1) * (x + 1) := by
    have : a < (a + 1) * (a + 1) → ∃ x, x * x ≤ a ∧ a < (x + 1) * (x + 1) := by
      simpa using open_leastNumber (P := λ x ↦ x * x ≤ a) ⟨“x. x * x ≤ &a”, by simp, by simp⟩
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

def sqrt (a : V) : V := Classical.choose! (sqrt_exists_unique a)

prefix:75 "√" => sqrt

@[simp] lemma sqrt_spec_le (a : V) : √a * √a ≤ a := (Classical.choose!_spec (sqrt_exists_unique a)).1

@[simp] lemma sqrt_spec_lt (a : V) : a < (√a + 1) * (√a + 1) := (Classical.choose!_spec (sqrt_exists_unique a)).2

lemma sqrt_graph {a b : V} : b = √a ↔ b * b ≤ a ∧ a < (b + 1) * (b + 1) := Classical.choose!_eq_iff _

def _root_.LO.FirstOrder.Arith.sqrtDef : 𝚺₀.Semisentence 2 :=
  .mkSigma “b a. b * b ≤ a ∧ a < (b + 1) * (b + 1)” (by simp[Hierarchy.pi_zero_iff_sigma_zero])

lemma sqrt_defined : 𝚺₀-Function₁ (λ a : V ↦ √a) via sqrtDef := by
  intro v; simp[sqrt_graph, sqrtDef, Matrix.vecHead, Matrix.vecTail]

@[simp] lemma sqrt_defined_iff (v) :
    Semiformula.Evalbm V v sqrtDef.val ↔ v 0 = √(v 1) := sqrt_defined.df.iff v

instance sqrt_definable : 𝚺₀-Function₁ ((√·) : V → V) := sqrt_defined.to_definable

lemma eq_sqrt (x a : V) : x * x ≤ a ∧ a < (x + 1) * (x + 1) → x = √a := Classical.choose_uniq (sqrt_exists_unique a)

lemma sqrt_eq_of_le_of_lt {x a : V} (le : x * x ≤ a) (lt : a < (x + 1) * (x + 1)) : √a = x :=
  Eq.symm <| eq_sqrt x a ⟨le, lt⟩

lemma sqrt_eq_of_le_of_le {x a : V} (le : x * x ≤ a) (h : a ≤ x * x + 2 * x) : √a = x :=
  sqrt_eq_of_le_of_lt le (by simp [add_mul_self_eq]; exact le_iff_lt_succ.mp h)

@[simp] lemma sq_sqrt_le (a : V) : (√a) ^ 2 ≤ a := by simp [sq]

@[simp] lemma sqrt_lt_sq (a : V) : a < (√a + 1) ^ 2 := by simp [sq]

@[simp] lemma sqrt_mul_self (a : V) : √(a * a) = a :=
  Eq.symm <| eq_sqrt a (a * a) (by simp; exact mul_self_lt_mul_self (by simp) (by simp))

@[simp] lemma sqrt_sq (a : V) : √(a^2) = a := by simp [sq]

@[simp] lemma sqrt_zero : √(0 : V) = 0 := by simpa using sqrt_mul_self (0 : V)

@[simp] lemma sqrt_one : √(1 : V) = 1 := by simpa using sqrt_mul_self (1 : V)

lemma sqrt_two : √(2 : V) = 1 :=
  Eq.symm <| eq_sqrt 1 2 (by simp [one_le_two, one_add_one_eq_two, one_lt_two])

lemma sqrt_three : √(3 : V) = 1 :=
  Eq.symm <| eq_sqrt 1 3 <| by simp [one_add_one_eq_two, two_mul_two_eq_four, ←three_add_one_eq_four]

@[simp] lemma sqrt_four : √(4 : V) = 2 := by
  simp [←two_mul_two_eq_four]

@[simp] lemma two_ne_square (a : V) : 2 ≠ a^2 := by
  intro h
  rcases show a = √2 from by rw [h]; simp with rfl
  simp [sqrt_two] at h

@[simp] lemma sqrt_le_add (a : V) : a ≤ √a * √a + 2 * √a :=
  le_iff_lt_succ.mpr (by have := sqrt_spec_lt a; rw [add_mul_self_eq] at this; simpa using this)

@[simp] lemma sqrt_le_self (a : V) : √a ≤ a := by
  by_contra A
  have : a < a := calc
    a ≤ a^2    := le_sq a
    _ < (√a)^2 := by simpa [sq] using mul_self_lt_mul_self (by simp) (by simpa using A)
    _ ≤ a      := sq_sqrt_le a
  simp_all

instance : Bounded₁ ((√·) : V → V) := ⟨#0, by intro v; simp⟩

lemma sqrt_lt_self_of_one_lt {a : V} (h : 1 < a) : √a < a := by
  by_contra A
  have : a * a ≤ √a * √a := mul_self_le_mul_self (by simp) (by simpa using A)
  have : a * a ≤ a := le_trans this (sqrt_spec_le a)
  exact not_lt.mpr this (lt_mul_self h)

lemma sqrt_le_of_le_sq {a b : V} : a ≤ b^2 → √a ≤ b := by
  intro h; by_contra A
  have : a < a := calc
    a ≤ b^2    := h
    _ < (√a)^2 := sq_lt_sq.mpr (by simpa using A)
    _ ≤ a      := by simp
  simp_all

lemma sq_lt_of_lt_sqrt {a b : V} : a < √b → a^2 < b := by
  intro h; by_contra A
  exact not_le.mpr h (sqrt_le_of_le_sq $ show b ≤ a^2 from by simpa using A)

end sqrt

section pair

open Classical

-- https://github.com/leanprover-community/mathlib4/blob/b075cdd0e6ad8b5a3295e7484b2ae59e9b2ec2a7/Mathlib/Data/Nat/Pairing.lean#L37
def pair (a b : V) : V := if a < b then b * b + a else a * a + a + b

--notation "⟪" a ", " b "⟫" => pair a b

/-- `!⟪x, y, z, ...⟫` notation for `Seq` -/
syntax "⟪" term,* "⟫" : term

macro_rules
  | `(⟪$term:term, $terms:term,*⟫) => `(pair $term ⟪$terms,*⟫)
  | `(⟪$term:term⟫) => `($term)

@[app_unexpander pair]
def pairUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term $term2) => `(⟪$term, $term2⟫)
  | _ => throw ()

lemma pair_graph {a b c : V} :
    c = ⟪a, b⟫ ↔ (a < b ∧ c = b * b + a) ∨ (b ≤ a ∧ c = a * a + a + b) := by
  simp [pair]
  by_cases h : a < b
  · simp [h, show ¬b ≤ a from by simpa using h]
  · simp [h, show b ≤ a from by simpa using h]

def _root_.LO.FirstOrder.Arith.pairDef : 𝚺₀.Semisentence 3 :=
  .mkSigma “c a b. (a < b ∧ c = b * b + a) ∨ (b ≤ a ∧ c = a * a + a + b)” (by simp)

lemma pair_defined : 𝚺₀-Function₂ (λ a b : V ↦ ⟪a, b⟫) via pairDef := by
  intro v; simp [pair_graph, pairDef]

@[simp] lemma pair_defined_iff (v) :
    Semiformula.Evalbm V v pairDef.val ↔ v 0 = ⟪v 1, v 2⟫ := pair_defined.df.iff v

instance pair_definable : 𝚺₀-Function₂ (pair : V → V → V) := pair_defined.to_definable

instance : Bounded₂ (pair : V → V → V) :=
  ⟨‘x y. (y * y + x) + (x * x + x + y)’, by intro v; simp [pair]; split_ifs <;> try simp [pair, *]⟩

def unpair (a : V) : V × V := if a - √a * √a < √a then (a - √a * √a, √a) else (√a, a - √a * √a - √a)

abbrev pi₁ (a : V) : V := (unpair a).1

abbrev pi₂ (a : V) : V := (unpair a).2

prefix: 80 "π₁" => pi₁

prefix: 80 "π₂" => pi₂

@[simp] lemma pair_unpair (a : V) : ⟪π₁ a, π₂ a⟫ = a := by
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

@[simp] lemma unpair_pair (a b : V) : unpair ⟪a, b⟫ = (a, b) := by
  simp [pair]; split_ifs with h
  · have : √(b * b + a) = b := sqrt_eq_of_le_of_le (by simp) (by simp; exact le_trans (le_of_lt h) (by simp))
    simp [unpair, this, show ¬b ≤ a from by simpa using h]
  · have : √(a * a + (a + b)) = a :=
      sqrt_eq_of_le_of_le (by simp [add_assoc]) (by simp [add_assoc, two_mul, show b ≤ a from by simpa using h])
    simp [unpair, this, add_assoc]

@[simp] lemma pi₁_pair (a b : V) : π₁ ⟪a, b⟫ = a := by simp [pi₁]

@[simp] lemma pi₂_pair (a b : V) : π₂ ⟪a, b⟫ = b := by simp [pi₂]

def pairEquiv : V × V ≃ V := ⟨Function.uncurry pair, unpair, fun ⟨a, b⟩ => unpair_pair a b, pair_unpair⟩

@[simp] lemma pi₁_le_self (a : V) : π₁ a ≤ a := by simp [pi₁, unpair]; split_ifs <;> simp

@[simp] lemma pi₂_le_self (a : V) : π₂ a ≤ a := by simp [pi₂, unpair]; split_ifs <;> simp [add_assoc]

@[simp] lemma le_pair_left (a b : V) : a ≤ ⟪a, b⟫ := by simpa using pi₁_le_self ⟪a, b⟫

@[simp] lemma le_pair_right (a b : V) : b ≤ ⟪a, b⟫ := by simpa using pi₂_le_self ⟪a, b⟫

@[simp] lemma lt_pair_left_of_pos {a} (pos : 0 < a) (b : V) : a < ⟪a, b⟫ := by
  simp [pair]; split_ifs
  · simp; exact pos_iff_ne_zero.mp <| pos_of_gt (by assumption)
  · calc
      a < a * a + a     := lt_add_of_pos_left a (by simpa using (pos_iff_ne_zero.mp pos))
      _ ≤ a * a + a + b := by simp

instance : Bounded₁ (pi₁ : V → V) := ⟨#0, by intro v; simp⟩

instance : Bounded₁ (pi₂ : V → V) := ⟨#0, by intro v; simp⟩

def _root_.LO.FirstOrder.Arith.pi₁Def : 𝚺₀.Semisentence 2 :=
  .mkSigma “x p. ∃ y <⁺ p, !pairDef p x y” (by simp)

def _root_.LO.FirstOrder.Arith.pi₂Def : 𝚺₀.Semisentence 2 :=
  .mkSigma “y p. ∃ x <⁺ p, !pairDef p x y” (by simp)

lemma pi₁_defined : 𝚺₀-Function₁ (pi₁ : V → V) via pi₁Def := by
  intro v; simp [pi₁Def]
  constructor
  · intro h; exact ⟨π₂ v 1, by simp [←le_iff_lt_succ],  by simp [h]⟩
  · rintro ⟨a, _, e⟩; simp [show v 1 = ⟪v 0, a⟫ from e]

@[simp] lemma pi₁_defined_iff (v) :
    Semiformula.Evalbm V v pi₁Def.val ↔ v 0 = π₁ (v 1) := pi₁_defined.df.iff v

instance pi₁_definable : 𝚺₀-Function₁ (pi₁ : V → V) := pi₁_defined.to_definable₀

lemma pi₂_defined : 𝚺₀-Function₁ (pi₂ : V → V) via pi₂Def := by
  intro v; simp [pi₂Def]
  constructor
  · intro h; exact ⟨π₁ v 1, by simp [←le_iff_lt_succ], by simp [h]⟩
  · rintro ⟨a, _, e⟩; simp [show v 1 = ⟪a, v 0⟫ from e]

@[simp] lemma pi₂_defined_iff (v) :
    Semiformula.Evalbm V v pi₂Def.val ↔ v 0 = π₂ (v 1) := pi₂_defined.df.iff v

instance pi₂_definable : 𝚺₀-Function₁ (pi₂ : V → V) := pi₂_defined.to_definable₀

lemma pair_lt_pair_left {a₁ a₂ : V} (h : a₁ < a₂) (b) : ⟪a₁, b⟫ < ⟪a₂, b⟫ := by
  by_cases h₁ : a₁ < b <;> simp [pair, h₁]
  · by_cases h₂ : a₂ < b <;> simp [pair, h₂, h]
    calc
      b * b + a₁ < b * b + b        := by simpa using h₁
      _          ≤ a₂ * a₂ + a₂     := add_le_add (mul_le_mul (by simpa using h₂) (by simpa using h₂) (by simp) (by simp)) (by simpa using h₂)
      _          ≤ a₂ * a₂ + a₂ + b := by simp
  · simp[show ¬a₂ < b from by simp; exact le_trans (by simpa using h₁) (le_of_lt h)]
    apply _root_.add_lt_add (by simpa [←sq] using h) h

lemma pair_le_pair_left {a₁ a₂ : V} (h : a₁ ≤ a₂) (b) : ⟪a₁, b⟫ ≤ ⟪a₂, b⟫ := by
  rcases h with (rfl | lt)
  · simp
  · exact le_of_lt (pair_lt_pair_left lt b)

lemma pair_lt_pair_right (a : V) {b₁ b₂} (h : b₁ < b₂) : ⟪a, b₁⟫ < ⟪a, b₂⟫ := by
  by_cases h₁ : a < b₁ <;> simp [pair, h₁]
  · simpa [lt_trans h₁ h, ←sq] using h
  · by_cases h₂ : a < b₂ <;> simp [h₂, h]
    calc
      a * a + a + b₁ < (a + 1) * (a + 1) + b₁ := by simp [add_mul_self_eq]; apply lt_succ_iff_le.mpr; simp
      _              ≤ b₂ * b₂ + b₁           := by simpa [←sq, succ_le_iff_lt] using h₂
      _              ≤ b₂ * b₂ + a            := by simpa using h₁

lemma pair_le_pair_right (a : V) {b₁ b₂} (h : b₁ ≤ b₂) : ⟪a, b₁⟫ ≤ ⟪a, b₂⟫ := by
  rcases h with (rfl | lt)
  · simp
  · exact le_of_lt (pair_lt_pair_right a lt)

lemma pair_le_pair {a₁ a₂ b₁ b₂ : V} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) : ⟪a₁, b₁⟫ ≤ ⟪a₂, b₂⟫ :=
  calc
    ⟪a₁, b₁⟫ ≤ ⟪a₂, b₁⟫ := pair_le_pair_left ha b₁
    _        ≤ ⟪a₂, b₂⟫ := pair_le_pair_right a₂ hb

lemma pair_lt_pair {a₁ a₂ b₁ b₂ : V} (ha : a₁ < a₂) (hb : b₁ < b₂) : ⟪a₁, b₁⟫ < ⟪a₂, b₂⟫ :=
  calc
    ⟪a₁, b₁⟫ < ⟪a₂, b₁⟫ := pair_lt_pair_left ha b₁
    _        < ⟪a₂, b₂⟫ := pair_lt_pair_right a₂ hb

@[simp] lemma pair_polybound (a b : V) : ⟪a, b⟫ ≤ (a + b + 1)^2 := by
  by_cases h : a < b <;> simp [pair, h, sq, add_mul_self_eq, two_mul]
  · simp [←add_assoc, add_right_comm _ a]; simp [add_right_comm _ (b * b)]
  · simp [←add_assoc, add_right_comm _ b]; simp [add_right_comm _ a]; simp [add_assoc]

@[simp] lemma pair_ext_iff {a₁ a₂ b₁ b₂ : V} : ⟪a₁, b₁⟫ = ⟪a₂, b₂⟫ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  ⟨fun e ↦ ⟨by simpa using congr_arg (π₁ ·) e, by simpa using congr_arg (π₂ ·) e⟩, by rintro ⟨rfl, rfl⟩; simp⟩

section

def _root_.LO.FirstOrder.Arith.pair₃Def : 𝚺₀.Semisentence 4 :=
  .mkSigma “p a b c. ∃ bc <⁺ p, !pairDef p a bc ∧ !pairDef bc b c” (by simp)

def _root_.LO.FirstOrder.Arith.pair₄Def : 𝚺₀.Semisentence 5 :=
  .mkSigma “p a b c d. ∃ bcd <⁺ p, ∃ cd <⁺ bcd, !pairDef p a bcd ∧ !pairDef bcd b cd ∧ !pairDef cd c d” (by simp)

def _root_.LO.FirstOrder.Arith.pair₅Def : 𝚺₀.Semisentence 6 :=
  .mkSigma “p a b c d e. ∃ bcde <⁺ p, ∃ cde <⁺ bcde, ∃ de <⁺ cde, !pairDef p a bcde ∧ !pairDef bcde b cde ∧ !pairDef cde c de ∧ !pairDef de d e” (by simp)

def _root_.LO.FirstOrder.Arith.pair₆Def : 𝚺₀.Semisentence 7 :=
  .mkSigma “p a b c d e f. ∃ bcdef <⁺ p, !pair₅Def bcdef b c d e f ∧ !pairDef p a bcdef” (by simp)

theorem fegergreg (v : Fin 4 → ℕ) : v (0 : Fin (Nat.succ 1)).succ.succ = v 2 := by { simp only [Nat.succ_eq_add_one,
  Nat.reduceAdd, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] }

axiom P : Fin 3 → Prop

theorem fin4 {n} : (2 : Fin (n + 3)).succ = 3 := rfl

@[simp] theorem Fin.succ_zero_eq_one'' {n} : (0 : Fin (n + 1)).succ = 1 := rfl

@[simp] theorem Fin.succ_two_eq_three {n} : (2 : Fin (n + 3)).succ = 3 := rfl

example (v : Fin 4 → ℕ) : v (2 : Fin 3).succ = v 3 := by { simp [fin4] }

theorem ss (v : Fin 4 → ℕ) : v (Fin.succ (0 : Fin (Nat.succ 1))).succ = v 2 := by { simp [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] }

lemma pair₃_defined : 𝚺₀-Function₃ ((⟪·, ·, ·⟫) : V → V → V → V) via pair₃Def := by
  intro v; simp [pair₃Def]
  rintro h; simp [h]

@[simp] lemma eval_pair₃Def (v) :
    Semiformula.Evalbm V v pair₃Def.val ↔ v 0 = ⟪v 1, v 2, v 3⟫ := pair₃_defined.df.iff v

lemma pair₄_defined : 𝚺₀-Function₄ ((⟪·, ·, ·, ·⟫) : V → V → V → V → V) via pair₄Def := by
  intro v; simp [pair₄Def]
  constructor
  · intro h; simp only [Fin.isValue, h, pair_ext_iff, true_and]
    exact ⟨_, by simp, _, by simp, rfl, rfl, rfl⟩
  · rintro ⟨_, _, _, _, h, rfl, rfl⟩; exact h

@[simp] lemma eval_pair₄Def (v) :
    Semiformula.Evalbm V v pair₄Def.val ↔ v 0 = ⟪v 1, v 2, v 3, v 4⟫ := pair₄_defined.df.iff v

lemma pair₅_defined : 𝚺₀.DefinedFunction (fun v : Fin 5 → V ↦ (⟪v 0, v 1, v 2, v 3, v 4⟫)) pair₅Def := by
  intro v; simp [pair₅Def]
  constructor
  · intro h; simp only [Fin.isValue, h, pair_ext_iff, true_and]
    exact ⟨_, le_pair_right _ _, _, le_pair_right _ _, _, le_pair_right _ _, rfl, rfl, rfl, rfl⟩
  · rintro ⟨_, _, _, _, _, _, h, rfl, rfl, rfl⟩; exact h

@[simp] lemma eval_pair₅Def (v) :
    Semiformula.Evalbm V v pair₅Def.val ↔ v 0 = ⟪v 1, v 2, v 3, v 4, v 5⟫ := pair₅_defined.df.iff v

lemma pair₆_defined : 𝚺₀.DefinedFunction (fun v : Fin 6 → V ↦ (⟪v 0, v 1, v 2, v 3, v 4, v 5⟫)) pair₆Def := by
  intro v; simp [pair₆Def]
  constructor
  · intro h; simp only [Fin.isValue, h, pair_ext_iff, true_and]
    exact ⟨_, le_pair_right _ _, rfl, rfl⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_pair₆Def (v) :
    Semiformula.Evalbm V v pair₆Def.val ↔ v 0 = ⟪v 1, v 2, v 3, v 4, v 5, v 6⟫ := pair₆_defined.df.iff v

end

def npair : {n : ℕ} → (v : Fin n → V) → V
  | 0,     _ => 0
  | _ + 1, v => ⟪v 0, npair (v ·.succ)⟫

@[simp] lemma npair_zero (v : Fin 0 → V) : npair v = 0 := by simp [npair]

lemma npair_succ (x) (v : Fin n → V) : npair (x :> v) = ⟪x, npair v⟫ := by simp [npair]

def unNpair : {n : ℕ} → Fin n → V → V
  | 0,     i, _ => i.elim0
  | _ + 1, i, x => Fin.cases (π₁ x) (fun i ↦ unNpair i (π₂ x)) i

@[simp] lemma unNpair_npair {n} (i : Fin n) (v : Fin n → V) : unNpair i (npair v) = v i := by
  induction' n with n ih <;> simp [npair, unNpair, *]
  · exact i.elim0
  · cases i using Fin.cases <;> simp

section

def _root_.LO.FirstOrder.Arith.unNpairDef : {n : ℕ} → (i : Fin n) → 𝚺₀.Semisentence 2
  | 0,     i => i.elim0
  | n + 1, i =>
    Fin.cases pi₁Def (fun i ↦ .mkSigma “z v. ∃ r <⁺ v, !pi₂Def r v ∧ !(unNpairDef i) z r” (by simp)) i

lemma unNpair_defined {n} (i : Fin n) : 𝚺₀-Function₁ (unNpair i : V → V) via unNpairDef i := by
  induction' n with n ih
  · exact i.elim0
  · intro v
    cases' i using Fin.cases with i
    · simp [unNpairDef, unNpair]
    · simp [unNpairDef, unNpair, (ih i).df.iff]
      constructor
      · intro h; exact ⟨π₂ (v 1), by simp, rfl, h⟩
      · rintro ⟨x, _, rfl, h⟩; exact h

@[simp] lemma eval_unNpairDef {n} (i : Fin n) (v) :
    Semiformula.Evalbm V v (unNpairDef i).val ↔ v 0 = unNpair i (v 1) := (unNpair_defined i).df.iff v

@[definability, simp] instance unNpair_definable {n} (i : Fin n) (Γ) : Γ-Function₁ (unNpair i : V → V) :=
  (unNpair_defined i).to_definable₀

end

end pair

end IOpen

section polynomial_induction

variable [V ⊧ₘ* 𝐈open]

@[elab_as_elim]
lemma hierarchy_polynomial_induction (Γ m) [V ⊧ₘ* Theory.indScheme ℒₒᵣ (Arith.Hierarchy Γ m)]
    {P : V → Prop} (hP : Γ-[m]-Predicate P)
    (zero : P 0) (even : ∀ x > 0, P x → P (2 * x)) (odd : ∀ x, P x → P (2 * x + 1)) : ∀ x, P x := by
  intro x; induction x using order_induction_h
  · exact Γ
  · exact m
  · exact hP
  case inst => exact inferInstance
  case ind x IH =>
    rcases zero_le x with (rfl | pos)
    · exact zero
    · have : x / 2 < x := div_lt_of_pos_of_one_lt pos one_lt_two
      rcases even_or_odd' x with (hx | hx)
      · simpa [←hx] using even (x / 2) (by by_contra A; simp at A; simp [show x = 0 from by simpa [A] using hx] at pos) (IH (x / 2) this)
      · simpa [←hx] using odd (x / 2) (IH (x / 2) this)

end polynomial_induction

@[elab_as_elim] lemma hierarchy_polynomial_induction_oRing_sigma₀ [V ⊧ₘ* 𝐈𝚺₀] {P : V → Prop} (hP : 𝚺₀-Predicate P)
    (zero : P 0) (even : ∀ x > 0, P x → P (2 * x)) (odd : ∀ x, P x → P (2 * x + 1)) : ∀ x, P x :=
  hierarchy_polynomial_induction 𝚺 0 (P := P) hP zero even odd

@[elab_as_elim] lemma hierarchy_polynomial_induction_oRing_sigma₁ [V ⊧ₘ* 𝐈𝚺₁] {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (zero : P 0) (even : ∀ x > 0, P x → P (2 * x)) (odd : ∀ x, P x → P (2 * x + 1)) : ∀ x, P x :=
  hierarchy_polynomial_induction 𝚺 1 (P := P) hP zero even odd

@[elab_as_elim] lemma hierarchy_polynomial_induction_oRing_pi₁ [V ⊧ₘ* 𝐈𝚷₁] {P : V → Prop} (hP : 𝚷₁-Predicate P)
    (zero : P 0) (even : ∀ x > 0, P x → P (2 * x)) (odd : ∀ x, P x → P (2 * x + 1)) : ∀ x, P x :=
  hierarchy_polynomial_induction 𝚷 1 (P := P) hP zero even odd

variable [V ⊧ₘ* 𝐈open]

lemma nat_cast_pair (n m : ℕ) : (⟪n, m⟫ : ℕ) = ⟪(↑n : V), (↑m : V)⟫ := by simp [pair]

lemma nat_pair_eq (m n : ℕ) : ⟪n, m⟫ = Nat.pair n m := by simp [Arith.pair, Nat.pair]

lemma pair_coe_eq_coe_pair (m n : ℕ) :  ⟪n, m⟫ = (Nat.pair n m : V) := by simp [nat_cast_pair, nat_pair_eq]

end

end LO.Arith
