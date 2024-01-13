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

lemma open_induction₁ {P : M → M → Prop}
    (hP : ∃ p : Semiformula ℒₒᵣ (Fin 1) 1, p.Open ∧ ∀ x a, P a x ↔ Semiformula.Eval! M ![x] ![a] p) (a) :
    P a 0 → (∀ x, P a x → P a (x + 1)) → ∀ x, P a x :=
  induction₁ (C := Semiformula.Open) (by simpa) a

lemma open_induction₂ {P : M → M → M → Prop}
    (hP : ∃ p : Semiformula ℒₒᵣ (Fin 2) 1, p.Open ∧ (∀ x a b, P a b x ↔ Semiformula.Eval! M ![x] ![a, b] p)) (a b) :
    P a b 0 → (∀ x, P a b x → P a b (x + 1)) → ∀ x, P a b x :=
  induction₂ (C := Semiformula.Open) (by simpa) a b

lemma open_leastNumber₁ {P : M → M → Prop}
    (hP : ∃ p : Semiformula ℒₒᵣ (Fin 1) 1, p.Open ∧ (∀ x a, P a x ↔ Semiformula.Eval! M ![x] ![a] p)) (a x) :
    P a 0 → ¬P a x → ∃ x, P a x ∧ ¬P a (x + 1) := fun h0 hx ↦ by
  simpa using (not_imp_not.mpr <| open_induction₁ hP a h0) (by simp; exact ⟨x, hx⟩)

lemma open_leastNumber₂ {P : M → M → M → Prop}
    (hP : ∃ p : Semiformula ℒₒᵣ (Fin 2) 1, p.Open ∧ (∀ x a b, P a b x ↔ Semiformula.Eval! M ![x] ![a, b] p)) (a b x) :
    P a b 0 → ¬P a b x → ∃ x, P a b x ∧ ¬P a b (x + 1) := fun h0 hx ↦ by
  simpa using (not_imp_not.mpr <| open_induction₂ hP a b h0) (by simp; exact ⟨x, hx⟩)

lemma remainder (a : M) {b} (pos : 0 < b) : ∃! u, ∃ v < b, a = b * u + v := by
  have : ∃! u, b * u ≤ a ∧ a < b * (u + 1) := by
    have : ∃ u, b * u ≤ a ∧ a < b * (u + 1) := by
      have : a < b * (a + 1) → ∃ u, b * u ≤ a ∧ a < b * (u + 1) := by
        simpa using open_leastNumber₂ (P := λ a b u ↦ b * u ≤ a) ⟨“&1 * #0 ≤ &0”, by simp, by simp⟩ a b (a + 1)
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
      let v := a ∸ b * u
      have e : a = b*u + v := by simp [add_tmsub_self_of_le h.1]
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

lemma ediv_defined : Σᴬ[0]-Function₂ (λ a b : M ↦ a /ₑ b) edivdef := by
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

lemma ediv_polybounded : PolyBounded₂ (λ a b : M ↦ a /ₑ b) #0 := λ _ ↦ by simp

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

lemma mul_ediv_self_of_dvd {a b : M} : a * (b /ₑ a) = b ↔ a ∣ b := by
  rcases zero_le a with (rfl | pos)
  · simp[eq_comm]
  · constructor
    · intro e; rw [←e]; simp
    · rintro ⟨r, rfl⟩; simp [pos]

end ediv

section remainder

def rem (a b : M) : M := a ∸ b * (a /ₑ b)

infix:60 " mod " => rem

def remdef : Σᴬ[0] 3 :=
  ⟨“∃[#0 < #2 + 1] (!edivdef [#0, #2, #3] ∧ !msubdef [#1, #2, #3 * #0])”, by simp⟩

lemma rem_graph (a b c : M) : a = b mod c ↔ ∃ x ≤ b, (x = b /ₑ c ∧ a = b ∸ c * x) := by
  simp [rem]; constructor
  · rintro rfl; exact ⟨b /ₑ c, by simp, rfl, by rfl⟩
  · rintro ⟨_, _, rfl, rfl⟩; simp

lemma rem_defined : Σᴬ[0]-Function₂ (λ a b : M ↦ a mod b) remdef := by
  intro v; simp [Matrix.vecHead, Matrix.vecTail, remdef,
    rem_graph, Semiformula.eval_substs, ediv_defined.pval, msub_defined.pval, le_iff_lt_succ]

lemma ediv_add_remainder (a b : M) : b * (a /ₑ b) + (a mod b) = a :=
  add_tmsub_self_of_le (mul_ediv_le a b)

lemma remainder_mul_add_of_lt (a : M) {b} (pos : 0 < b) {r} (hr : r < b) : (a * b + r) mod b = r := by
  simp [rem, ediv_mul_add a pos hr, mul_comm]

@[simp] lemma remainder_mul_add (a c : M) (pos : 0 < b) : (a * b + c) mod b = c mod b := by
  simp [rem, ediv_mul_add_self, pos, mul_add, ←msub_msub, show b * a = a * b from mul_comm _ _]

@[simp] lemma remainder_add_mul (a b : M) (pos : 0 < c) : (a + b * c) mod c = a mod c := by
  simp [add_comm a (b * c), pos]

@[simp] lemma remainder_mul_add' (a c : M) (pos : 0 < b) : (b * a + c) mod b = c mod b := by
  simp [mul_comm b a, pos]

@[simp] lemma remainder_eq_self_of_lt {a b : M} (h : a < b) : a mod b = a := by
  simpa using remainder_mul_add_of_lt 0 (pos_of_gt h) h

@[simp] lemma remainder_zero (a : M) : a mod 0 = a := by simp [rem]

@[simp] lemma remainder_self {a : M} (pos : 0 < a) : a mod a = 0 := by simp [rem, pos]

@[simp] lemma remainder_lt (a : M) {b} (pos : 0 < b) : a mod b < b := by
  rcases ediv_spec_of_pos' a pos with ⟨r, hr, ha⟩
  have : ((a /ₑ b) * b + r) mod b = r := remainder_mul_add_of_lt _ pos hr
  have : a mod b = r := by simpa [←ha] using this
  simp [this, hr]

@[simp] lemma remainder_le_add (a b : M) : a mod b ≤ a + b := by
  have : 0 ≤ b := zero_le b
  rcases this with (rfl | pos) <;> simp [*]
  exact le_trans (le_of_lt (remainder_lt a pos)) (by simp)

lemma remainder_eq_zero_iff_dvd {a b : M} : b mod a = 0 ↔ a ∣ b := by
  simp [rem]
  constructor
  · intro H; exact mul_ediv_self_of_dvd.mp (le_antisymm (mul_ediv_le b a) H)
  · intro H; simp [mul_ediv_self_of_dvd.mpr H]

lemma remainder_mul {a b m : M} (pos : 0 < m) : (a * b) mod m = ((a mod m) * (b mod m)) mod m := calc
  (a * b) mod m = ((m * (a /ₑ m) + (a mod m)) * (m * (b /ₑ m) + (b mod m))) mod m := by simp [ediv_add_remainder]
  _             = ((a mod m) * (b mod m)) mod m                                   := by simp [add_mul, mul_add, pos, mul_left_comm _ m, add_assoc, mul_assoc]

lemma remainder_two (a : M) : a mod 2 = 0 ∨ a mod 2 = 1 :=
  le_one_iff_eq_zero_or_one.mp <| lt_two_iff_le_one.mp <| remainder_lt a (b := 2) (by simp)

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

lemma two_prime : Prime (2 : M) := ⟨by simp, by simp, by intro a b h; exact two_dvd_mul h⟩

lemma pow2_mul_two {a : M} : IsPow2 (2 * a) ↔ IsPow2 a :=
  ⟨by intro H
      have : ∀ r ≤ a, 1 < r → r ∣ a → 2 ∣ r := by
        intro r hr ltr dvd
        exact H.dvd (show r ≤ 2 * a from le_trans hr (le_mul_of_one_le_left (by simp) one_le_two)) ltr (Dvd.dvd.mul_left dvd 2)
      exact ⟨by simpa using H.pos, this⟩,
   by intro H
      exact ⟨by simpa using H.pos, by
        intro r _ hr hd
        rcases two_prime.left_dvd_or_dvd_right_of_dvd_mul hd with (hd | hd)
        · exact hd
        · exact H.dvd (show r ≤ a from le_of_dvd H.pos hd) hr hd⟩⟩

lemma pow2_mul_four {a : M} : IsPow2 (4 * a) ↔ IsPow2 a := by
  simp [←two_mul_two_eq_four, mul_assoc, pow2_mul_two]

lemma IsPow2.elim {p : M} : IsPow2 p ↔ p = 1 ∨ ∃ q, p = 2 * q ∧ IsPow2 q :=
  ⟨by intro H
      by_cases hp : 1 < p
      · have : 2 ∣ p := H.two_dvd hp
        rcases this with ⟨q, rfl⟩
        right; exact ⟨q, rfl, pow2_mul_two.mp H⟩
      · have : p = 1 := le_antisymm (by simpa using hp) (pos_iff_one_le.mp H.pos)
        left; exact this,
   by rintro (rfl | ⟨q, rfl, hq⟩) <;> simp [pow2_one, pow2_mul_two, *]⟩

@[simp] lemma pow2_two : IsPow2 (2 : M) := IsPow2.elim.mpr (Or.inr ⟨1, by simp⟩)

lemma IsPow2.div_two {p : M} (h : IsPow2 p) (ne : p ≠ 1) : IsPow2 (p /ₑ 2) := by
  rcases IsPow2.elim.mp h with (rfl | ⟨q, rfl, pq⟩)
  · simp at ne
  simpa

lemma IsPow2.two_mul_div_two {p : M} (h : IsPow2 p) (ne : p ≠ 1) : 2 * (p /ₑ 2) = p := by
  rcases IsPow2.elim.mp h with (rfl | ⟨q, rfl, _⟩)
  · simp at ne
  simp

lemma IsPow2.div_two_mul_two {p : M} (h : IsPow2 p) (ne : p ≠ 1) : (p /ₑ 2) * 2 = p := by
  simp [mul_comm, h.two_mul_div_two ne]

lemma IsPow2.elim' {p : M} : IsPow2 p ↔ p = 1 ∨ 1 < p ∧ ∃ q, p = 2 * q ∧ IsPow2 q := by
  by_cases hp : 1 < p <;> simp [hp]
  · exact IsPow2.elim
  · have : p = 0 ∨ p = 1 := le_one_iff_eq_zero_or_one.mp (show p ≤ 1 from by simpa using hp)
    rcases this with (rfl | rfl) <;> simp

-- lemma pow_dvd {p q : M} (hp : IsPow2 p) (hq : IsPow2 q) : p ≤ q → p ∣ q := by {  }

section sqrt

lemma sqrt_exists_unique (a : M) : ∃! x, x * x ≤ a ∧ a < (x + 1) * (x + 1) := by
  have : ∃ x, x * x ≤ a ∧ a < (x + 1) * (x + 1) := by
    have : a < (a + 1) * (a + 1) → ∃ x, x * x ≤ a ∧ a < (x + 1) * (x + 1) := by
      simpa using open_leastNumber₁ (P := λ a x ↦ x * x ≤ a) ⟨“#0 * #0 ≤ &0”, by simp, by simp⟩ a (a + 1)
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

lemma eq_sqrt (x a : M) : x * x ≤ a ∧ a < (x + 1) * (x + 1) → x = √a := Classical.choose_uniq (sqrt_exists_unique a)

@[simp] lemma sq_sqrt_le (a : M) : (√a)^2 ≤ a := by simp [sq]

@[simp] lemma sqrt_mul_self (a : M) : √(a * a) = a :=
  Eq.symm <| eq_sqrt a (a * a) (by simp; exact mul_self_lt_mul_self (by simp) (by simp))

@[simp] lemma sqrt_sq (a : M) : √(a^2) = a := by simp [sq]

@[simp] lemma sqrt_zero : √(0 : M) = 0 := by simpa using sqrt_mul_self (0 : M)

@[simp] lemma sqrt_one : √(1 : M) = 1 := by simpa using sqrt_mul_self (1 : M)

@[simp] lemma sqrt_two : √(2 : M) = 1 :=
  Eq.symm <| eq_sqrt 1 2 (by simp [one_le_two, one_add_one_eq_two, one_lt_two])

@[simp] lemma sqrt_three : √(3 : M) = 1 :=
  Eq.symm <| eq_sqrt 1 3 (by
    simp [one_add_one_eq_two, two_mul_two_eq_four]
    constructor
    · simp [←two_add_one_eq_three]
    · simp [←three_add_one_eq_four])

@[simp] lemma sqrt_le_self (a : M) : √a ≤ a := by
  by_contra A
  have : a < a := calc
    a ≤ a^2    := le_sq a
    _ < (√a)^2 := by simpa [sq] using mul_self_lt_mul_self (by simp) (by simpa using A)
    _ ≤ a      := sq_sqrt_le a
  simp_all

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

section cpair

def cpair (a b : M) : M := ((a + b) * (a + b + 1)) /ₑ 2 + b

notation "⟨" a " ; " b "⟩" => cpair a b

lemma cpair_graph {a b c : M} :
    c = ⟨a ; b⟩ ↔ ∃ r < 2, (a + b) * (a + b + 1) + 2 * b = 2 * c + r := by
  simp [cpair, ediv_graph, ←ediv_add_mul_self, mul_comm]

def cpairdef : Σᴬ[0] 3 :=
  ⟨“∃[#0 < 2] (#2 + #3) * (#2 + #3 + 1) + 2 * #3 = 2 * #1 + #0”, by simp[Hierarchy.pi_zero_iff_sigma_zero]⟩

def cpairPolyBound : Polynomial 2 := ᵀ“(#0 + #1) * (#0 + #1 + 1) + #1 * 2”

lemma cpair_defined : Σᴬ[0]-Function₂ (λ a b : M ↦ ⟨a ; b⟩) cpairdef := by
  intro v; simp [Matrix.vecHead, Matrix.vecTail, Matrix.constant_eq_singleton, cpair_graph, cpairdef]

lemma cpair_polybounded : PolyBounded₂ (λ a b : M ↦ ⟨a ; b⟩) cpairPolyBound :=
  λ _ ↦ by simp[cpair, ←ediv_add_mul_self, cpairPolyBound]

end cpair

namespace LenBit

/-- $\mathrm{LenBit} (2^i, a) \iff \text{$i$th-bit of $a$ is $1$}$. -/
def LenBit (w a : M) : Prop := (a /ₑ w) mod 2 = 1

def lenBitdef : Σᴬ[0] 2 :=
  ⟨“∃[#0 < #2 + 1] !remdef [1, #0, 2]”, by simp⟩

end LenBit

end IOpen

end Model

end

end Arith

end LO.FirstOrder
