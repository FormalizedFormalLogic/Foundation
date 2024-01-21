import Arithmetization.IOpen

namespace LO.FirstOrder

namespace Arith

noncomputable section

variable {M : Type} [Inhabited M] [DecidableEq M] [ORingSymbol M]
  [Structure ℒₒᵣ M] [Structure.ORing ℒₒᵣ M]
  [𝐏𝐀⁻.Mod M]

namespace Model

section IOpen

variable [𝐈open.Mod M]

def Pow2 (a : M) : Prop := 0 < a ∧ ∀ r ≤ a, 1 < r → r ∣ a → 2 ∣ r

def pow2def : Σᴬ[0] 1 :=
  ⟨“0 < #0 ∧ ∀[#0 < #1 + 1] (1 < #0 →  !dvddef [#0, #1] → !dvddef [2, #0])”, by simp [Hierarchy.pi_zero_iff_sigma_zero]⟩

lemma pow2_defined : Σᴬ[0]-Predicate (Pow2 : M → Prop) pow2def := by
  intro v
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.vecHead, Matrix.constant_eq_singleton,
    Pow2, pow2def, le_iff_lt_succ, dvd_defined.pval]

instance {b s} : DefinablePred b s (Pow2 : M → Prop) := defined_to_with_param₀ _ pow2_defined

lemma Pow2.pos {a : M} (h : Pow2 a) : 0 < a := h.1

lemma Pow2.dvd {a : M} (h : Pow2 a) {r} (hr : r ≤ a) : 1 < r → r ∣ a → 2 ∣ r := h.2 r hr

@[simp] lemma pow2_one : Pow2 (1 : M) := ⟨by simp, by
  intro r hr hhr hd
  rcases show r = 0 ∨ r = 1 from le_one_iff_eq_zero_or_one.mp hr with (rfl | rfl)
  · simp
  · simp at hhr⟩

@[simp] lemma not_pow2_zero : ¬Pow2 (0 : M) := by
  intro h; have := h.pos; simp at this

lemma Pow2.two_dvd {a : M} (h : Pow2 a) (lt : 1 < a) : 2 ∣ a := h.dvd (le_refl _) lt (by simp)

lemma Pow2.two_dvd' {a : M} (h : Pow2 a) (lt : a ≠ 1) : 2 ∣ a :=
  h.dvd (le_refl _) (by
    by_contra A; simp [le_one_iff_eq_zero_or_one] at A
    rcases A with (rfl | rfl) <;> simp at h lt)
    (by simp)

lemma Pow2.of_dvd {a b : M} (h : b ∣ a) : Pow2 a → Pow2 b := by
  intro ha
  have : 0 < b := by
    by_contra e
    have : a = 0 := by simpa [show b = 0 from by simpa using e] using h
    rcases this with rfl
    simpa using ha.pos
  exact ⟨this, fun r hr ltr hb ↦
    ha.dvd (show r ≤ a from le_trans hr (le_of_dvd ha.pos h)) ltr (dvd_trans hb h)⟩

lemma pow2_mul_two {a : M} : Pow2 (2 * a) ↔ Pow2 a :=
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

lemma pow2_mul_four {a : M} : Pow2 (4 * a) ↔ Pow2 a := by
  simp [←two_mul_two_eq_four, mul_assoc, pow2_mul_two]

lemma Pow2.elim {p : M} : Pow2 p ↔ p = 1 ∨ ∃ q, p = 2 * q ∧ Pow2 q :=
  ⟨by intro H
      by_cases hp : 1 < p
      · have : 2 ∣ p := H.two_dvd hp
        rcases this with ⟨q, rfl⟩
        right; exact ⟨q, rfl, pow2_mul_two.mp H⟩
      · have : p = 1 := le_antisymm (by simpa using hp) (pos_iff_one_le.mp H.pos)
        left; exact this,
   by rintro (rfl | ⟨q, rfl, hq⟩) <;> simp [pow2_one, pow2_mul_two, *]⟩

@[simp] lemma pow2_two : Pow2 (2 : M) := Pow2.elim.mpr (Or.inr ⟨1, by simp⟩)

lemma Pow2.div_two {p : M} (h : Pow2 p) (ne : p ≠ 1) : Pow2 (p /ₑ 2) := by
  rcases Pow2.elim.mp h with (rfl | ⟨q, rfl, pq⟩)
  · simp at ne
  simpa

lemma Pow2.two_mul_div_two {p : M} (h : Pow2 p) (ne : p ≠ 1) : 2 * (p /ₑ 2) = p := by
  rcases Pow2.elim.mp h with (rfl | ⟨q, rfl, _⟩)
  · simp at ne
  simp

lemma Pow2.div_two_mul_two {p : M} (h : Pow2 p) (ne : p ≠ 1) : (p /ₑ 2) * 2 = p := by
  simp [mul_comm, h.two_mul_div_two ne]

lemma Pow2.elim' {p : M} : Pow2 p ↔ p = 1 ∨ 1 < p ∧ ∃ q, p = 2 * q ∧ Pow2 q := by
  by_cases hp : 1 < p <;> simp [hp]
  · exact Pow2.elim
  · have : p = 0 ∨ p = 1 := le_one_iff_eq_zero_or_one.mp (show p ≤ 1 from by simpa using hp)
    rcases this with (rfl | rfl) <;> simp


section LenBit

/-- $\mathrm{LenBit} (2^i, a) \iff \text{$i$th-bit of $a$ is $1$}$. -/
def LenBit (i a : M) : Prop := ¬2 ∣ (a /ₑ i)

def lenbitdef : Σᴬ[0] 2 :=
  ⟨“∃[#0 < #2 + 1] (!edivdef [#0, #2, #1] ∧ ¬!dvddef [2, #0])”, by simp⟩

lemma lenbit_defined : Σᴬ[0]-Relation (LenBit : M → M → Prop) lenbitdef := by
  intro v; simp[sqrt_graph, lenbitdef, Matrix.vecHead, Matrix.vecTail, ediv_defined.pval, dvd_defined.pval, LenBit, ←le_iff_lt_succ]
  constructor
  · intro h; exact ⟨v 1 /ₑ v 0, by simp, rfl, h⟩
  · rintro ⟨z, hz, rfl, h⟩; exact h

instance {b s} : DefinableRel b s (LenBit : M → M → Prop) := defined_to_with_param₀ _ lenbit_defined

lemma LenBit.le {i a : M} (h : LenBit i a) : i ≤ a := by
  by_contra A; simp [LenBit, show a < i from by simpa using A] at h

lemma not_lenbit_of_lt {i a : M} (h : a < i) : ¬LenBit i a := by
  intro A; exact not_le.mpr h A.le

@[simp] lemma LenBit.zero (a : M) : ¬LenBit 0 a := by simp [LenBit]

@[simp] lemma LenBit.on_zero (a : M) : ¬LenBit a 0 := by simp [LenBit]

lemma LenBit.one (a : M) : LenBit 1 a ↔ ¬2 ∣ a := by simp [LenBit]

lemma LenBit.iff_rem {i a : M} : LenBit i a ↔ (a /ₑ i) mod 2 = 1 := by
  simp [LenBit]; rcases remainder_two (a /ₑ i) with (h | h) <;> simp [h, ←remainder_eq_zero_iff_dvd]

lemma not_lenbit_iff_rem {i a : M} : ¬LenBit i a ↔ (a /ₑ i) mod 2 = 0 := by
  simp [LenBit, ←remainder_eq_zero_iff_dvd]

@[simp] lemma LenBit.self {a : M} (pos : 0 < a) : LenBit a a := by simp [LenBit.iff_rem, pos, one_lt_two]

lemma LenBit.remainder {i a k : M} (h : 2 * i ∣ k) : LenBit i (a mod k) ↔ LenBit i a := by
  have : 0 ≤ i := zero_le i
  rcases (eq_or_lt_of_le this) with (rfl | pos)
  · simp
  rcases h with ⟨k', hk'⟩
  calc
    LenBit i (a mod k) ↔ ((a mod k) /ₑ i) mod 2 = 1                             := LenBit.iff_rem
    _                  ↔ (2 * k') * (a /ₑ k) + ((a mod k) /ₑ i) mod 2 = 1       := by simp [mul_assoc]
    _                  ↔ (((2 * k') * (a /ₑ k) * i + (a mod k)) /ₑ i) mod 2 = 1 := by simp [ediv_mul_add_self, pos]
    _                  ↔ ((k * (a /ₑ k) + (a mod k)) /ₑ i) mod 2 = 1            := iff_of_eq (by
                                                                                      congr 3
                                                                                      simp [mul_right_comm _ (a /ₑ k), mul_right_comm 2 k' i, ←hk'])
    _                  ↔ LenBit i a                                             := by simp [ediv_add_remainder a k, LenBit.iff_rem]

@[simp] lemma LenBit.remainder_two_mul_self {a i : M} : LenBit i (a mod 2 * i) ↔ LenBit i a := LenBit.remainder (by simp)

lemma LenBit.add {i a b : M} (h : 2 * i ∣ b) : LenBit i (a + b) ↔ LenBit i a := by
  have : 0 ≤ i := zero_le i
  rcases (eq_or_lt_of_le this) with (rfl | pos)
  · simp
  rcases h with ⟨b', hb'⟩
  have hb' : b = 2 * b' * i := by simp [hb', mul_right_comm]
  calc
    LenBit i (a + b) ↔ ((a + b) /ₑ i) mod 2 = 1    := LenBit.iff_rem
    _                ↔ (a /ₑ i) + 2 * b' mod 2 = 1 := by rw [hb', ediv_add_mul_self _ _ pos]
    _                ↔ LenBit i a                  := by simp [LenBit.iff_rem]

lemma LenBit.add_self {i a : M} (h : a < i) : LenBit i (a + i) := by
  have pos : 0 < i := by exact pos_of_gt h
  simp [LenBit.iff_rem, ediv_add_self_right _ pos, h, one_lt_two]

lemma LenBit.add_self_of_not_lenbit {a i : M} (pos : 0 < i) (h : ¬LenBit i a) : LenBit i (a + i) := by
  have : a /ₑ i mod 2 = 0 := by simpa [LenBit.iff_rem] using h
  simp [LenBit.iff_rem, ediv_add_self_right, pos]
  rw [remainder_add] <;> simp [this, one_lt_two]

end LenBit

end IOpen

section ISigma₀

variable [𝐈𝚺₀.Mod M]

namespace Pow2

lemma mul {a b : M} (ha : Pow2 a) (hb : Pow2 b) : Pow2 (a * b) := by
  wlog hab : a ≤ b
  · simpa [mul_comm] using this hb ha (by simp at hab; exact LT.lt.le hab)
  suffices : ∀ b : M, ∀ a ≤ b, Pow2 a → Pow2 b → Pow2 (a * b)
  · exact this b a hab ha hb
  intro b
  induction b using hierarchy_order_induction_sigma₀
  · definability
  case ind IH a b IH =>
    intro a hab ha hb
    have : a = 1 ∨ 1 < a ∧ ∃ a', a = 2 * a' ∧ Pow2 a' := Pow2.elim'.mp ha
    rcases this with (rfl | ⟨lta, a, rfl, ha⟩)
    · simpa using hb
    · have : b = 1 ∨ 1 < b ∧ ∃ b', b = 2 * b' ∧ Pow2 b' := Pow2.elim'.mp hb
      rcases this with (rfl | ⟨ltb, b, rfl, hb⟩)
      · simpa using ha
      · have ltb : b < 2 * b := lt_two_mul_self (pos_iff_ne_zero.mpr $ by rintro rfl; simp at ltb)
        have hab : a ≤ b := le_of_mul_le_mul_left hab (by simp)
        have : Pow2 (a * b) := IH b ltb a hab (by assumption) (by assumption)
        suffices : Pow2 (4 * a * b)
        · have : (2 * a) * (2 * b) = 4 * a * b := by simp [mul_assoc, mul_left_comm a 2 b, ←two_mul_two_eq_four]
          simpa [this]
        simpa [mul_assoc, pow2_mul_four] using this

@[simp] lemma mul_iff {a b : M} : Pow2 (a * b) ↔ Pow2 a ∧ Pow2 b :=
  ⟨fun h ↦ ⟨h.of_dvd (by simp), h.of_dvd (by simp)⟩, by rintro ⟨ha, hb⟩; exact ha.mul hb⟩

@[simp] lemma sq_iff {a : M} : Pow2 (a^2) ↔ Pow2 a := by
  simp [_root_.sq]

lemma sq {a : M} : Pow2 a → Pow2 (a^2) := by
  simp [_root_.sq]

lemma dvd_of_le {a b : M} (ha : Pow2 a) (hb : Pow2 b) : a ≤ b → a ∣ b := by
  suffices : ∀ b : M, ∀ a ≤ b, Pow2 a → Pow2 b → a ∣ b
  · intro hab; exact this b a hab ha hb
  intro b; induction b using hierarchy_order_induction_sigma₀
  · definability
  case ind b IH =>
    intro a hab ha hb
    have : b = 1 ∨ 1 < b ∧ ∃ b', b = 2 * b' ∧ Pow2 b' := Pow2.elim'.mp hb
    rcases this with (rfl | ⟨ltb, b, rfl, hb⟩)
    · rcases le_one_iff_eq_zero_or_one.mp hab with (rfl | rfl) <;> simp
      · simp at ha
    · have : a = 1 ∨ 1 < a ∧ ∃ a', a = 2 * a' ∧ Pow2 a' := Pow2.elim'.mp ha
      rcases this with (rfl | ⟨lta, a, rfl, ha⟩)
      · simp
      · have ltb : b < 2 * b := lt_two_mul_self (pos_iff_ne_zero.mpr $ by rintro rfl; simp at ltb)
        have hab : a ≤ b := le_of_mul_le_mul_left hab (by simp)
        exact mul_dvd_mul_left 2 <| IH b ltb a hab (by assumption) (by assumption)

lemma le_iff_dvd {a b : M} (ha : Pow2 a) (hb : Pow2 b) : a ≤ b ↔ a ∣ b :=
  ⟨Pow2.dvd_of_le ha hb, le_of_dvd hb.pos⟩

lemma two_le {a : M} (pa : Pow2 a) (ne1 : a ≠ 1) : 2 ≤ a :=
  le_of_dvd pa.pos (pa.two_dvd' ne1)

lemma le_iff_lt_two {a b : M} (ha : Pow2 a) (hb : Pow2 b) : a ≤ b ↔ a < 2 * b := by
  constructor
  · intro h; exact lt_of_le_of_lt h (lt_two_mul_self hb.pos)
  · intro h
    by_cases ea : a = 1
    · rcases ea with rfl
      simpa [←pos_iff_one_le] using hb.pos
    · suffices : a ∣ b
      · exact le_of_dvd hb.pos this
      have : a /ₑ 2 ∣ b := by
        have : 2 * (a /ₑ 2) ∣ 2 * b := by
          simpa [ha.two_mul_div_two ea] using dvd_of_le ha (by simpa using hb) (LT.lt.le h)
        exact (mul_dvd_mul_iff_left (by simp)).mp this
      rcases this with ⟨b', rfl⟩
      have hb' : Pow2 b' := by simp at hb; exact hb.2
      have : 2 ∣ b' := hb'.two_dvd' (by rintro rfl; simp [ha.two_mul_div_two ea] at h)
      rcases this with ⟨b'', rfl⟩
      simp [←mul_assoc, ha.div_two_mul_two ea]

lemma lt_iff_two_mul_le {a b : M} (ha : Pow2 a) (hb : Pow2 b) : a < b ↔ 2 * a ≤ b := by
  by_cases eb : b = 1
  · simp [eb, ←lt_two_iff_le_one]
  · rw [←hb.two_mul_div_two eb]; simp [le_iff_lt_two ha (hb.div_two eb)]


lemma sq_or_dsq {a : M} (pa : Pow2 a) : ∃ b, a = b^2 ∨ a = 2 * b^2 := by
  suffices : ∃ b ≤ a, a = b^2 ∨ a = 2 * b^2
  · rcases this with ⟨b, _, h⟩
    exact ⟨b, h⟩
  revert pa
  induction a using hierarchy_order_induction_sigma₀
  · definability
  case ind a IH =>
    intro pa
    rcases Pow2.elim'.mp pa with (rfl | ⟨ha, a, rfl, pa'⟩)
    · exact ⟨1, by simp⟩
    · have : 0 < a := by simpa [←pos_iff_one_le] using one_lt_iff_two_le.mp ha
      rcases IH a (lt_mul_of_one_lt_left this one_lt_two) pa' with ⟨b, _, (rfl | rfl)⟩
      · exact ⟨b, le_trans (by simp) le_two_mul_left, by right; rfl⟩
      · exact ⟨2 * b, by simp; exact le_trans (by simp) le_two_mul_left,
        by left; simp [_root_.sq, mul_assoc, mul_left_comm]⟩

lemma sqrt {a : M} (h : Pow2 a) (hsq : (√a)^2 = a) : Pow2 (√a) := by
  rw [←hsq] at h; simpa using h

@[simp] lemma Pow2.not_three : ¬Pow2 (3 : M) := by
  intro h
  have : 2 ∣ 3 := h.two_dvd (by simp [←two_add_one_eq_three])
  simp [←two_add_one_eq_three, ←remainder_eq_zero_iff_dvd, one_lt_two] at this

lemma four_le {i : M} (hi : Pow2 i) (lt : 2 < i) : 4 ≤ i := by
  by_contra A
  have : i ≤ 3 := by simpa [←three_add_one_eq_four, ←le_iff_lt_succ] using A
  rcases le_three_iff_eq_zero_or_one_or_two_or_three.mp this with (rfl | rfl | rfl | rfl) <;> simp at lt hi

lemma mul_add_lt_of_mul_lt_of_pos {a b p q : M} (hp : Pow2 p) (hq : Pow2 q)
    (h : a * p < q) (hb : b < p) (hbq : b < q) : a * p + b < q := by
  rcases zero_le a with (rfl | pos)
  · simp [hbq]
  have : p ∣ q :=
    dvd_of_le hp hq (le_of_lt $
      lt_of_mul_lt_of_one_le_of_nonneg_left (by simpa [mul_comm a p] using h) (pos_iff_one_le.mp pos) (by simp))
  rcases this with ⟨q, rfl⟩
  have : a < q := lt_of_mul_lt_mul_right (a := p) (by simpa [mul_comm] using h)
  calc
    a * p + b < (a + 1) * p := by simp [add_mul, hb]
    _         ≤ p * q       := by simp [mul_comm p q]; exact mul_le_mul_right (lt_iff_succ_le.mp this)

end Pow2

lemma LenBit.remainder_pow2 {a i j : M} (pi : Pow2 i) (pj : Pow2 j) (h : i < j) : LenBit i (a mod j) ↔ LenBit i a :=
  LenBit.remainder (by rw [←Pow2.le_iff_dvd] <;> simp [pi, pj, ←Pow2.lt_iff_two_mul_le, h])

lemma LenBit.add_pow2 {a i j : M} (pi : Pow2 i) (pj : Pow2 j) (h : i < j) : LenBit i (a + j) ↔ LenBit i a :=
  LenBit.add (by rw [←Pow2.le_iff_dvd] <;> simp [pi, pj, ←Pow2.lt_iff_two_mul_le, h])

lemma LenBit.add_pow2_iff_of_lt {a i j : M} (pi : Pow2 i) (pj : Pow2 j) (h : a < j) : LenBit i (a + j) ↔ i = j ∨ LenBit i a := by
  rcases show i < j ∨ i = j ∨ i > j from lt_trichotomy i j with (hij | rfl | hij)
  · simp [LenBit.add_pow2 pi pj hij, hij.ne]
  · simp [LenBit.add_self h]
  · have : a + j < i := calc
      a + j < 2 * j  := by simp[two_mul, h]
      _     ≤ i      := (pj.lt_iff_two_mul_le pi).mp hij
    simp [not_lenbit_of_lt this, not_lenbit_of_lt (show a < i from lt_trans _ _ _ h hij), hij.ne.symm]

lemma lenbit_iff_add_mul {i a : M} (hi : Pow2 i) :
    LenBit i a ↔ ∃ k, ∃ r < i, a = k * (2 * i) + i + r := by
  constructor
  · intro h
    have : 2 * ((a /ₑ i) /ₑ 2) + 1 = a /ₑ i := by simpa [LenBit.iff_rem.mp h] using ediv_add_remainder (a /ₑ i) 2
    have : a = ((a /ₑ i) /ₑ 2) * (2 * i) + i + (a mod i) := calc
      a = i * (a /ₑ i) + (a mod i)                  := Eq.symm <| ediv_add_remainder a i
      _ = i * (2 * ((a /ₑ i) /ₑ 2) + 1) + (a mod i) := by simp [this]
      _ = ((a /ₑ i) /ₑ 2) * (2 * i) + i + (a mod i) := by simp [mul_add, ←mul_assoc, mul_comm i 2, mul_comm (2 * i)]
    exact ⟨(a /ₑ i) /ₑ 2, a mod i, by simp [hi.pos], this⟩
  · rintro ⟨k, r, h, rfl⟩
    simp [LenBit.iff_rem, ←mul_assoc, add_assoc, ediv_mul_add_self, hi.pos, h, one_lt_two]

lemma not_lenbit_iff_add_mul {i a : M} (hi : Pow2 i) :
    ¬LenBit i a ↔ ∃ k, ∃ r < i, a = k * (2 * i) + r := by
  constructor
  · intro h
    have : 2 * ((a /ₑ i) /ₑ 2) = a /ₑ i := by simpa [not_lenbit_iff_rem.mp h] using ediv_add_remainder (a /ₑ i) 2
    have : a = ((a /ₑ i) /ₑ 2) * (2 * i) + (a mod i) := calc
      a = i * (a /ₑ i) + (a mod i)              := Eq.symm <| ediv_add_remainder a i
      _ = i * (2 * ((a /ₑ i) /ₑ 2)) + (a mod i) := by simp [this]
      _ = ((a /ₑ i) /ₑ 2) * (2 * i) + (a mod i) := by simp [mul_add, ←mul_assoc, mul_comm i 2, mul_comm (2 * i)]
    exact ⟨(a /ₑ i) /ₑ 2, a mod i, by simp [hi.pos], this⟩
  · rintro ⟨k, r, h, rfl⟩
    simp [not_lenbit_iff_rem, ←mul_assoc, add_assoc, ediv_mul_add_self, hi.pos, h]

lemma lenbit_mul_add {i j a r : M} (pi : Pow2 i) (pj : Pow2 j) (hr : r < j) :
    LenBit (i * j) (a * j + r) ↔ LenBit i a := by
  by_cases h : LenBit i a <;> simp [h]
  · rcases (lenbit_iff_add_mul pi).mp h with ⟨a, b, hb, rfl⟩
    have : b * j + r < i * j :=
      pj.mul_add_lt_of_mul_lt_of_pos (by simp[pi, pj]) ((mul_lt_mul_right pj.pos).mpr hb)  hr (lt_of_lt_of_le hr $ le_mul_of_pos_left $ pi.pos)
    exact (lenbit_iff_add_mul (by simp [pi, pj])).mpr ⟨a, b * j + r, this, by simp [add_mul, add_assoc, mul_assoc]⟩
  · rcases (not_lenbit_iff_add_mul pi).mp h with ⟨a, b, hb, rfl⟩
    have : b * j + r < i * j :=
      pj.mul_add_lt_of_mul_lt_of_pos (by simp[pi, pj]) ((mul_lt_mul_right pj.pos).mpr hb) hr (lt_of_lt_of_le hr $ le_mul_of_pos_left $ pi.pos)
    exact (not_lenbit_iff_add_mul (by simp [pi, pj])).mpr ⟨a, b * j + r, this, by simp [add_mul, add_assoc, mul_assoc]⟩

lemma lenbit_add_pow2_iff_of_not_lenbit {a i j : M} (pi : Pow2 i) (pj : Pow2 j) (h : ¬LenBit j a) :
    LenBit i (a + j) ↔ i = j ∨ LenBit i a := by
  rcases show i < j ∨ i = j ∨ i > j from lt_trichotomy i j with (hij | rfl | hij)
  · simp [LenBit.add_pow2 pi pj hij, hij.ne]
  · simp [LenBit.add_self_of_not_lenbit pi.pos, h]
  · simp [ne_of_gt hij]
    have : 2 * j ∣ i := Pow2.dvd_of_le (by simp [pj]) pi <| (pj.lt_iff_two_mul_le pi).mp hij
    rcases this with ⟨i, rfl⟩
    rcases (not_lenbit_iff_add_mul pj).mp h with ⟨a, r, hr, rfl⟩
    simp at pi
    have pi' : Pow2 i := pi.2
    have pj' : Pow2 j := pi.1
    calc
      LenBit (2 * j * i) (a * (2 * j) + r + j) ↔ LenBit (i * (2 * j)) (a * (2 * j) + (r + j)) := by
        simp [mul_comm (2 * j), add_assoc]
      _                                        ↔ LenBit i a                                   :=
        lenbit_mul_add pi' (by simpa using pj') (by simp [two_mul, hr])
      _                                        ↔ LenBit (i * (2 * j)) (a * (2 * j) + r)       :=
        Iff.symm <| lenbit_mul_add pi' (by simpa using pj') (lt_of_lt_of_le hr $ by simp)
      _                                        ↔ LenBit (2 * j * i) (a * (2 * j) + r)         := by
        simp [mul_comm]

end ISigma₀

end Model

end

end Arith

end LO.FirstOrder
