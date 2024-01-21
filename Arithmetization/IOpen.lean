import Arithmetization.Ind

namespace LO.FirstOrder

namespace Arith

noncomputable section

variable {M : Type} [Inhabited M] [DecidableEq M] [ORingSymbol M]
  [Structure ℒₒᵣ M] [Structure.ORing ℒₒᵣ M]
  [𝐏𝐀⁻.Mod M]

namespace Model

section IOpen

variable [𝐈open.Mod M]

@[elab_as_elim]
lemma open_induction {P : M → Prop}
    (hP : ∃ p : Semiformula ℒₒᵣ M 1, p.Open ∧ ∀ x, P x ↔ Semiformula.Eval! M ![x] id p)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  induction (C := Semiformula.Open)
    (by rcases hP with ⟨p, hp, hhp⟩
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

lemma remainder (a : M) {b} (pos : 0 < b) : ∃! u, ∃ v < b, a = b * u + v := by
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

section ediv

lemma ediv_exists_unique (a b : M) : ∃! u, (0 < b → ∃ v < b, a = b * u + v) ∧ (b = 0 → u = 0) := by
  have : 0 ≤ b := by exact zero_le b
  rcases this with (rfl | pos) <;> simp [*]
  · simpa [pos_iff_ne_zero.mp pos] using remainder a pos

/-- Euclidean division -/
def ediv (a b : M) : M := Classical.choose! (ediv_exists_unique a b)

infix:70 " /ₑ " => ediv

lemma ediv_spec_of_pos (a : M) (h : 0 < b) : ∃ v < b, a = b * (a /ₑ b) + v :=
  (Classical.choose!_spec (ediv_exists_unique a b)).1 h

@[simp] lemma ediv_spec_zero (a : M) : a /ₑ 0 = 0 :=
  (Classical.choose!_spec (ediv_exists_unique a 0)).2 (by simp)

lemma ediv_graph {a b c : M} : c = a /ₑ b ↔ ((0 < b → ∃ v < b, a = b * c + v) ∧ (b = 0 → c = 0)) :=
  Classical.choose!_eq_iff _

def edivdef : Σᴬ[0] 3 :=
  ⟨“(0 < #2 → ∃[#0 < #3] (#2 = #3 * #1 + #0)) ∧ (#2 = 0 → #0 = 0)”, by simp[Hierarchy.pi_zero_iff_sigma_zero]⟩

lemma ediv_defined : Σᴬ[0]-Function₂ ((· /ₑ ·) : M → M → M) edivdef := by
  intro v; simp[ediv_graph, edivdef, Matrix.vecHead, Matrix.vecTail]

lemma ediv_spec_of_pos' (a : M) (h : 0 < b) : ∃ v < b, a = (a /ₑ b) * b + v := by
  simpa [mul_comm] using ediv_spec_of_pos a h

@[simp] lemma mul_ediv_le (a b : M) : b * (a /ₑ b) ≤ a := by
  have : 0 ≤ b := by exact zero_le b
  rcases this with (rfl | pos) <;> simp [*]
  rcases ediv_spec_of_pos a pos with ⟨v, _, e⟩
  simpa [← e] using show b * (a /ₑ b) ≤ b * (a /ₑ b) + v from le_self_add

@[simp] lemma ediv_le (a b : M) : a /ₑ b ≤ a := by
  have : 0 ≤ b := zero_le b
  rcases this with (rfl | pos) <;> simp [*]
  have : 1 * (a /ₑ b) ≤ b * (a /ₑ b) := mul_le_mul_of_nonneg_right (le_iff_lt_succ.mpr (by simp[pos])) (by simp)
  simpa using le_trans this (mul_ediv_le a b)

instance ediv_polybounded : PolyBounded₂ ((· /ₑ ·) : M → M → M) := ⟨#0, λ _ ↦ by simp⟩

instance : DefinableFunction₂ b s ((· /ₑ ·) : M → M → M) := defined_to_with_param₀ _ ediv_defined

@[simp] lemma ediv_mul_le (a b : M) : a /ₑ b * b ≤ a := by rw [mul_comm]; exact mul_ediv_le _ _

lemma lt_mul_ediv (a : M) {b} (pos : 0 < b) : a < b * (a /ₑ b + 1) := by
  rcases ediv_spec_of_pos a pos with ⟨v, hv, e⟩
  calc a = b * (a /ₑ b) + v := e
       _ < b * (a /ₑ b + 1) := by simp [mul_add, hv]

@[simp] lemma ediv_one (a : M) : a /ₑ 1 = a :=
  le_antisymm (by simp) (le_iff_lt_succ.mpr $ by simpa using lt_mul_ediv a one_pos)

lemma ediv_mul_add (a : M) {b r} (pos : 0 < b) (hr : r < b) : (a * b + r) /ₑ b = a := by
  rcases ediv_spec_of_pos (a * b + r) pos with ⟨v, hv, e⟩
  symm; apply eq_of_le_of_not_lt
  · have : a * b < ((a * b + r) /ₑ b + 1) * b := calc
      a * b ≤ a * b + r                  := le_self_add
      _     = ((a * b + r) /ₑ b) * b + v := by simpa [@mul_comm _ _ b] using e
      _     < ((a * b + r) /ₑ b + 1) * b := by simp [add_mul, hv]
    exact le_iff_lt_succ.mpr <| lt_of_mul_lt_mul_of_nonneg_right this (by simp)
  · intro H
    have : ((a * b + r) /ₑ b) * b < (a + 1) * b := calc
      ((a * b + r) /ₑ b) * b ≤ a * b + r   := by simp
      _                      < (a + 1) * b := by simp [add_mul, hr]
    have : (a * b + r) /ₑ b ≤ a := le_iff_lt_succ.mpr ((mul_lt_mul_right pos).mp this)
    have : a < a := lt_of_lt_of_le H this
    exact LT.lt.false this

lemma ediv_add_mul_self (a c : M) {b} (pos : 0 < b) : (a + c * b) /ₑ b = a /ₑ b + c := by
  rcases ediv_spec_of_pos' a pos with ⟨r, hr, ex⟩
  simpa [add_mul, add_right_comm, ← ex] using ediv_mul_add (a /ₑ b + c) pos hr

lemma ediv_mul_add_self (a c : M) {b} (pos : 0 < b) : (a * b + c) /ₑ b = a + c /ₑ b := by
  simp [ediv_add_mul_self, pos, add_comm]

@[simp] lemma ediv_mul_left (a : M) {b} (pos : 0 < b) : (a * b) /ₑ b = a := by
  simpa using ediv_mul_add a pos pos

@[simp] lemma ediv_mul_right (a : M) {b} (pos : 0 < b) : (b * a) /ₑ b = a := by
  simpa [mul_comm] using ediv_mul_add a pos pos

@[simp] lemma ediv_eq_zero_of_lt (b : M) {a} (h : a < b) : a /ₑ b = 0 := by
  simpa using ediv_mul_add 0 (pos_of_gt h) h

@[simp] lemma ediv_self {a : M} (hx : 0 < a) : a /ₑ a = 1 := by
  simpa using ediv_mul_left 1 hx

@[simp] lemma zero_ediv (a : M) : 0 /ₑ a = 0 := by
  rcases zero_le a with (rfl | pos) <;> simp [*]

@[simp] lemma ediv_mul' (a : M) {b} (pos : 0 < b) : (b * a) /ₑ b = a := by simp [mul_comm, pos]

@[simp] lemma ediv_add_self_left {a} (pos : 0 < a) (b : M) : (a + b) /ₑ a = 1 + b /ₑ a := by
  simpa using ediv_mul_add_self 1 b pos

@[simp] lemma ediv_add_self_right (a : M) {b} (pos : 0 < b) : (a + b) /ₑ b = a /ₑ b + 1 := by
  simpa using ediv_add_mul_self a 1 pos

lemma mul_ediv_self_of_dvd {a b : M} : a * (b /ₑ a) = b ↔ a ∣ b := by
  rcases zero_le a with (rfl | pos)
  · simp[eq_comm]
  · constructor
    · intro e; rw [←e]; simp
    · rintro ⟨r, rfl⟩; simp [pos]

end ediv

section remainder

def rem (a b : M) : M := a - b * (a /ₑ b)

infix:60 " mod " => rem

def remdef : Σᴬ[0] 3 :=
  ⟨“∃[#0 < #2 + 1] (!edivdef [#0, #2, #3] ∧ !subdef [#1, #2, #3 * #0])”, by simp⟩

lemma rem_graph (a b c : M) : a = b mod c ↔ ∃ x ≤ b, (x = b /ₑ c ∧ a = b - c * x) := by
  simp [rem]; constructor
  · rintro rfl; exact ⟨b /ₑ c, by simp, rfl, by rfl⟩
  · rintro ⟨_, _, rfl, rfl⟩; simp

lemma rem_defined : Σᴬ[0]-Function₂ ((· mod ·) : M → M → M) remdef := by
  intro v; simp [Matrix.vecHead, Matrix.vecTail, remdef,
    rem_graph, Semiformula.eval_substs, ediv_defined.pval, sub_defined.pval, le_iff_lt_succ]

instance : DefinableFunction₂ b s ((· mod ·) : M → M → M) := defined_to_with_param₀ _ rem_defined

lemma ediv_add_remainder (a b : M) : b * (a /ₑ b) + (a mod b) = a :=
  add_tsub_self_of_le (mul_ediv_le a b)

@[simp] lemma remainder_zero (a : M) : a mod 0 = a := by simp [rem]

@[simp] lemma remainder_self (a : M) : a mod a = 0 := by
  rcases zero_le a with (rfl | h)
  · simp
  · simp [rem, h]

lemma remainder_mul_add_of_lt (a : M) {b} (pos : 0 < b) {r} (hr : r < b) : (a * b + r) mod b = r := by
  simp [rem, ediv_mul_add a pos hr, mul_comm]

@[simp] lemma remainder_mul_add (a c : M) (pos : 0 < b) : (a * b + c) mod b = c mod b := by
  simp [rem, ediv_mul_add_self, pos, mul_add, ←sub_sub, show b * a = a * b from mul_comm _ _]

@[simp] lemma remainder_add_mul (a b : M) (pos : 0 < c) : (a + b * c) mod c = a mod c := by
  simp [add_comm a (b * c), pos]

@[simp] lemma remainder_add_mul' (a b : M) (pos : 0 < c) : (a + c * b) mod c = a mod c := by
  simp [mul_comm c b, pos]

@[simp] lemma remainder_mul_add' (a c : M) (pos : 0 < b) : (b * a + c) mod b = c mod b := by
  simp [mul_comm b a, pos]

@[simp] lemma remainder_mul_self_left (a b : M) : (a * b) mod b = 0 := by
  rcases zero_le b with (rfl | h)
  · simp
  · simpa using remainder_mul_add_of_lt a h h

@[simp] lemma remainder_mul_self_right (a b : M) : (b * a) mod b = 0 := by
  simp [mul_comm]

@[simp] lemma remainder_eq_self_of_lt {a b : M} (h : a < b) : a mod b = a := by
  simpa using remainder_mul_add_of_lt 0 (pos_of_gt h) h

@[simp] lemma remainder_lt (a : M) {b} (pos : 0 < b) : a mod b < b := by
  rcases ediv_spec_of_pos' a pos with ⟨r, hr, ha⟩
  have : ((a /ₑ b) * b + r) mod b = r := remainder_mul_add_of_lt _ pos hr
  have : a mod b = r := by simpa [←ha] using this
  simp [this, hr]

@[simp] lemma remainder_le (a b : M) : a mod b ≤ a := by
  simp [rem]

instance remainder_polybounded : PolyBounded₂ ((· mod ·) : M → M → M) := ⟨#0, by intro v; simp⟩

lemma remainder_eq_zero_iff_dvd {a b : M} : b mod a = 0 ↔ a ∣ b := by
  simp [rem]
  constructor
  · intro H; exact mul_ediv_self_of_dvd.mp (le_antisymm (mul_ediv_le b a) H)
  · intro H; simp [mul_ediv_self_of_dvd.mpr H]

@[simp] lemma remainder_add_remove_right {a b : M} (pos : 0 < b) : (a + b) mod b = a mod b := by
  simpa using remainder_add_mul a 1 pos

lemma remainder_add_remove_right_of_dvd {a b m : M} (h : m ∣ b) (pos : 0 < m) : (a + b) mod m = a mod m := by
  rcases h with ⟨b, rfl⟩; simp [pos]

@[simp] lemma remainder_add_remove_left {a b : M} (pos : 0 < a) : (a + b) mod a = b mod a := by
  simpa using remainder_mul_add 1 b pos

lemma remainder_add_remove_left_of_dvd {a b m : M} (h : m ∣ a) (pos : 0 < m) : (a + b) mod m = b mod m := by
  rcases h with ⟨b, rfl⟩; simp [pos]

lemma remainder_add {a b m : M} (pos : 0 < m) : (a + b) mod m = ((a mod m) + (b mod m)) mod m := calc
  (a + b) mod m = ((m * (a /ₑ m) + (a mod m)) + (m * (b /ₑ m) + (b mod m))) mod m := by simp [ediv_add_remainder]
  _             = ((a mod m) + (b mod m)) mod m                                   := by simp [add_mul, mul_add, pos, mul_left_comm _ m,
                                                                                          add_assoc, mul_assoc, add_left_comm]

lemma remainder_mul {a b m : M} (pos : 0 < m) : (a * b) mod m = ((a mod m) * (b mod m)) mod m := calc
  (a * b) mod m = ((m * (a /ₑ m) + (a mod m)) * (m * (b /ₑ m) + (b mod m))) mod m := by simp [ediv_add_remainder]
  _             = ((a mod m) * (b mod m)) mod m                                   := by simp [add_mul, mul_add, pos, mul_left_comm _ m, add_assoc, mul_assoc]

lemma remainder_two (a : M) : a mod 2 = 0 ∨ a mod 2 = 1 :=
  le_one_iff_eq_zero_or_one.mp <| lt_two_iff_le_one.mp <| remainder_lt a (b := 2) (by simp)

@[simp] lemma remainder_two_not_zero_iff {a : M} : ¬a mod 2 = 0 ↔ a mod 2 = 1 := by
  rcases remainder_two a with (h | h) <;> simp [*]

@[simp] lemma remainder_two_not_one_iff {a : M} : ¬a mod 2 = 1 ↔ a mod 2 = 0 := by
  rcases remainder_two a with (h | h) <;> simp [*]

end remainder

lemma two_dvd_mul {a b : M} : 2 ∣ a * b → 2 ∣ a ∨ 2 ∣ b := by
  intro H; by_contra A
  simp [not_or] at A
  have ha : a mod 2 = 1 := by
    have : a mod 2 = 0 ∨ a mod 2 = 1 := remainder_two a
    simpa [show a mod 2 ≠ 0 from by simpa [←remainder_eq_zero_iff_dvd] using A.1] using this
  have hb : b mod 2 = 1 := by
    have : b mod 2 = 0 ∨ b mod 2 = 1 :=
      le_one_iff_eq_zero_or_one.mp <| lt_two_iff_le_one.mp <| remainder_lt b (b := 2) (by simp)
    simpa [show b mod 2 ≠ 0 from by simpa [←remainder_eq_zero_iff_dvd] using A.2] using this
  have : a * b mod 2 = 1 := by simp [remainder_mul, ha, hb]; exact remainder_eq_self_of_lt one_lt_two
  have : ¬2 ∣ a * b := by simp [←remainder_eq_zero_iff_dvd, this]
  contradiction

lemma even_or_odd (a : M) : ∃ x, a = 2 * x ∨ a = 2 * x + 1 :=
  ⟨a /ₑ 2, by
    have : 2 * (a /ₑ 2) + (a mod 2) = a := ediv_add_remainder a 2
    rcases remainder_two a with (e | e) <;> { simp[e] at this; simp [this] }⟩

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


@[simp] lemma sq_sqrt_le (a : M) : (√a)^2 ≤ a := by simp [sq]

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
    _ < (√a)^2 := sq_lt_sq_iff.mp (by simpa using A)
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

notation "⟨" a " ; " b "⟩" => pair a b

lemma pair_graph {a b c : M} :
    c = ⟨a ; b⟩ ↔ (a < b ∧ c = b * b + a) ∨ (b ≤ a ∧ c = a * a + a + b) := by
  simp [pair]
  by_cases h : a < b
  · simp [h, show ¬b ≤ a from by simpa using h]
  · simp [h, show b ≤ a from by simpa using h]

def pairdef : Σᴬ[0] 3 := ⟨“(#1 < #2 ∧ #0 = #2 * #2 + #1) ∨ (#2 ≤ #1 ∧ #0 = #1 * #1 + #1 + #2)”, by simp⟩

lemma pair_defined : Σᴬ[0]-Function₂ (λ a b : M ↦ ⟨a ; b⟩) pairdef := by
  intro v; simp [pair_graph, pairdef]

def unpair (a : M) : M × M := if a - √a * √a < √a then (a - √a * √a, √a) else (√a, a - √a * √a - √a)

abbrev pi₁ (a : M) : M := (unpair a).1

abbrev pi₂ (a : M) : M := (unpair a).2

@[simp] lemma pair_unpair (a : M) : ⟨pi₁ a ; pi₂ a⟩ = a := by
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

@[simp] lemma unpair_pair (a b : M) : unpair ⟨a ; b⟩ = (a, b) := by
  simp [pair]; split_ifs with h
  · have : √(b * b + a) = b := sqrt_eq_of_le_of_le (by simp) (by simp; exact le_trans (le_of_lt h) (by simp))
    simp [unpair, this, show ¬b ≤ a from by simpa using h]
  · have : √(a * a + (a + b)) = a :=
      sqrt_eq_of_le_of_le (by simp [add_assoc]) (by simp [add_assoc, two_mul, show b ≤ a from by simpa using h])
    simp [unpair, this, add_assoc]

def pairEquiv : M × M ≃ M :=
  ⟨Function.uncurry pair, unpair, fun ⟨a, b⟩ => unpair_pair a b, pair_unpair⟩

end pair

end IOpen

end Model

end

end Arith

end LO.FirstOrder
