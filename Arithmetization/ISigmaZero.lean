import Arithmetization.IOpen
import Mathlib.Tactic.Linarith

namespace LO.FirstOrder

attribute [simp] Semiformula.eval_substs Matrix.vecHead Matrix.vecTail Matrix.comp_vecCons' Matrix.constant_eq_singleton

namespace Arith

noncomputable section

variable {M : Type} [Inhabited M] [DecidableEq M] [ORingSymbol M]
  [Structure ℒₒᵣ M] [Structure.ORing ℒₒᵣ M]
  [𝐏𝐀⁻.Mod M]

namespace Model

section ISigma₀

variable [𝐈𝚺₀.Mod M]

--lemma lt_of_pos {a : M} (pos : 0 < a) : a < 2*a := by exact lt_two_mul_self pos

lemma lt_square_of_lt {a : M} (pos : 1 < a) : a < a^2 := lt_self_pow pos Nat.one_lt_two

lemma two_mul_le_sq {i : M} (h : 2 ≤ i) : 2 * i ≤ i ^ 2 := by simp [sq]; exact mul_le_mul_right h

lemma two_mul_lt_sq {i : M} (h : 2 < i) : 2 * i < i ^ 2 := by
  simp [sq]; exact (mul_lt_mul_right (show 0 < i from pos_of_gt h)).mpr h

lemma succ_le_double_of_pos {a : M} (h : 0 < a) : a + 1 ≤ 2 * a := by
  simpa [two_mul] using pos_iff_one_le.mp h

namespace IsPow2

lemma mul {a b : M} (ha : IsPow2 a) (hb : IsPow2 b) : IsPow2 (a * b) := by
  wlog hab : a ≤ b
  · simpa [mul_comm] using this hb ha (by simp at hab; exact LT.lt.le hab)
  refine hierarchy_order_induction₀ M Σ 0
    (fun b ↦ ∀ a ≤ b, IsPow2 a → IsPow2 b → IsPow2 (a * b))
    ⟨⟨“∀[#0 < #1 + 1] (!pow2def [#0] → !pow2def [#1] → !pow2def [#0 * #1])”, by simp⟩,
     by intro v; simp [le_iff_lt_succ, Semiformula.eval_substs, Matrix.vecHead, pow2_defined.pval]⟩ ?_ b a hab ha hb
  simp; intro b H a hab ha hb
  have : a = 1 ∨ 1 < a ∧ ∃ a', a = 2 * a' ∧ IsPow2 a' := IsPow2.elim'.mp ha
  rcases this with (rfl | ⟨lta, a, rfl, ha⟩)
  · simpa using hb
  · have : b = 1 ∨ 1 < b ∧ ∃ b', b = 2 * b' ∧ IsPow2 b' := IsPow2.elim'.mp hb
    rcases this with (rfl | ⟨ltb, b, rfl, hb⟩)
    · simpa using ha
    · have ltb : b < 2 * b := lt_two_mul_self (pos_iff_ne_zero.mpr $ by rintro rfl; simp at ltb)
      have hab : a ≤ b := le_of_mul_le_mul_left hab (by simp)
      have : IsPow2 (a * b) := H b ltb a hab (by assumption) (by assumption)
      suffices : IsPow2 (4 * a * b)
      · have : (2 * a) * (2 * b) = 4 * a * b := by simp [mul_assoc, mul_left_comm a 2 b, ←two_mul_two_eq_four]
        simpa [this]
      simpa [mul_assoc, pow2_mul_four] using this

@[simp] lemma mul_iff {a b : M} : IsPow2 (a * b) ↔ IsPow2 a ∧ IsPow2 b :=
  ⟨fun h ↦ ⟨h.of_dvd (by simp), h.of_dvd (by simp)⟩, by rintro ⟨ha, hb⟩; exact ha.mul hb⟩

@[simp] lemma sq_iff {a : M} : IsPow2 (a^2) ↔ IsPow2 a := by
  simp [_root_.sq]

lemma sq {a : M} : IsPow2 a → IsPow2 (a^2) := by
  simp [_root_.sq]

lemma dvd_of_le {a b : M} (ha : IsPow2 a) (hb : IsPow2 b) : a ≤ b → a ∣ b := by
  intro hab
  refine hierarchy_order_induction₀ M Σ 0 (fun b ↦ ∀ a ≤ b, IsPow2 a → IsPow2 b → a ∣ b)
    ⟨⟨“∀[#0 < #1 + 1] (!pow2def [#0] → !pow2def [#1] → !dvddef [#0, #1]) ”, by simp⟩,
      by intro v; simp [le_iff_lt_succ, Semiformula.eval_substs, Matrix.vecHead, pow2_defined.pval, dvd_defined.pval]⟩
    ?_ b a hab ha hb
  simp; intro b H a hab ha hb
  have : b = 1 ∨ 1 < b ∧ ∃ b', b = 2 * b' ∧ IsPow2 b' := IsPow2.elim'.mp hb
  rcases this with (rfl | ⟨ltb, b, rfl, hb⟩)
  · rcases le_one_iff_eq_zero_or_one.mp hab with (rfl | rfl) <;> simp
    · simp at ha
  · have : a = 1 ∨ 1 < a ∧ ∃ a', a = 2 * a' ∧ IsPow2 a' := IsPow2.elim'.mp ha
    rcases this with (rfl | ⟨lta, a, rfl, ha⟩)
    · simp
    · have ltb : b < 2 * b := lt_two_mul_self (pos_iff_ne_zero.mpr $ by rintro rfl; simp at ltb)
      have hab : a ≤ b := le_of_mul_le_mul_left hab (by simp)
      exact mul_dvd_mul_left 2 <| H b ltb a hab (by assumption) (by assumption)

lemma le_iff_dvd {a b : M} (ha : IsPow2 a) (hb : IsPow2 b) : a ≤ b ↔ a ∣ b :=
  ⟨IsPow2.dvd_of_le ha hb, le_of_dvd hb.pos⟩

lemma two_le {a : M} (pa : IsPow2 a) (ne1 : a ≠ 1) : 2 ≤ a :=
  le_of_dvd pa.pos (pa.two_dvd' ne1)

lemma le_iff_lt_two {a b : M} (ha : IsPow2 a) (hb : IsPow2 b) : a ≤ b ↔ a < 2 * b := by
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
      have hb' : IsPow2 b' := by simp at hb; exact hb.2
      have : 2 ∣ b' := hb'.two_dvd' (by rintro rfl; simp [ha.two_mul_div_two ea] at h)
      rcases this with ⟨b'', rfl⟩
      simp [←mul_assoc, ha.div_two_mul_two ea]

lemma lt_iff_two_mul_le {a b : M} (ha : IsPow2 a) (hb : IsPow2 b) : a < b ↔ 2 * a ≤ b := by
  by_cases eb : b = 1
  · simp [eb, ←lt_two_iff_le_one]
  · rw [←hb.two_mul_div_two eb]; simp [le_iff_lt_two ha (hb.div_two eb)]

lemma sq_or_dsq {a : M} (pa : IsPow2 a) : ∃ b, a = b^2 ∨ a = 2 * b^2 := by
  suffices : ∃ b ≤ a, a = b^2 ∨ a = 2 * b^2
  · rcases this with ⟨b, _, h⟩
    exact ⟨b, h⟩
  refine hierarchy_order_induction₀ M Σ 0 (fun a ↦ IsPow2 a → ∃ b ≤ a, a = b^2 ∨ a = 2 * b^2)
    ⟨⟨“!pow2def [#0] → ∃[#0 < #1 + 1] (#1 = #0 * #0 ∨ #1 = 2 * (#0 * #0)) ”, by simp⟩,
      by intro v; simp [←le_iff_lt_succ, Semiformula.eval_substs, pow2_defined.pval, Matrix.vecHead, _root_.sq]⟩
    ?_ a pa
  simp; intro a IH pa
  rcases IsPow2.elim'.mp pa with (rfl | ⟨ha, a, rfl, pa'⟩)
  · exact ⟨1, by simp⟩
  · have : 0 < a := by simpa [←pos_iff_one_le] using one_lt_iff_two_le.mp ha
    rcases IH a (lt_mul_of_one_lt_left this one_lt_two) pa' with ⟨b, _, (rfl | rfl)⟩
    · exact ⟨b, le_trans (by simp) le_two_mul_left, by right; rfl⟩
    · exact ⟨2 * b, by simp; exact le_trans (by simp) le_two_mul_left,
      by left; simp [_root_.sq, mul_assoc, mul_left_comm]⟩

lemma sqrt {a : M} (h : IsPow2 a) (hsq : (√a)^2 = a) : IsPow2 (√a) := by
  rw [←hsq] at h; simpa using h

@[simp] lemma IsPow2.not_three : ¬IsPow2 (3 : M) := by
  intro h
  have : 2 ∣ 3 := h.two_dvd (by simp [←two_add_one_eq_three])
  simp [←two_add_one_eq_three, ←remainder_eq_zero_iff_dvd, one_lt_two] at this

lemma four_le {i : M} (hi : IsPow2 i) (lt : 2 < i) : 4 ≤ i := by
  by_contra A
  have : i ≤ 3 := by simpa [←three_add_one_eq_four, ←le_iff_lt_succ] using A
  rcases le_three_iff_eq_zero_or_one_or_two_or_three.mp this with (rfl | rfl | rfl | rfl) <;> simp at lt hi

end IsPow2

lemma LenBit.remainder_pow2 {a i j : M} (pi : IsPow2 i) (pj : IsPow2 j) (h : i < j) : LenBit i (a mod j) ↔ LenBit i a :=
  LenBit.remainder (by rw [←IsPow2.le_iff_dvd] <;> simp [pi, pj, ←IsPow2.lt_iff_two_mul_le, h])

lemma LenBit.add_pow2 {a i j : M} (pi : IsPow2 i) (pj : IsPow2 j) (h : i < j) : LenBit i (a + j) ↔ LenBit i a :=
  LenBit.add (by rw [←IsPow2.le_iff_dvd] <;> simp [pi, pj, ←IsPow2.lt_iff_two_mul_le, h])

lemma LenBit.add_pow2_iff {a i j : M} (pi : IsPow2 i) (pj : IsPow2 j) (h : a < j) : LenBit i (a + j) ↔ i = j ∨ LenBit i a := by
  rcases show i < j ∨ i = j ∨ i > j from lt_trichotomy i j with (hij | rfl | hij)
  · simp [LenBit.add_pow2 pi pj hij, hij.ne]
  · simp [LenBit.add_self h]
  · have : a + j < i := calc
      a + j < 2 * j  := by simp[two_mul, h]
      _     ≤ i      := (pj.lt_iff_two_mul_le pi).mp hij
    simp [not_lenbit_of_lt this, not_lenbit_of_lt (show a < i from lt_trans _ _ _ h hij), hij.ne.symm]

def SPPow2 (m : M) : Prop := ¬LenBit 1 m ∧ LenBit 2 m ∧ ∀ i ≤ m, IsPow2 i → 2 < i → (LenBit i m ↔ (√i)^2 = i ∧ LenBit (√i) m)

def sppow2def : Σᴬ[0] 1 :=
  ⟨“¬!lenbitdef [1, #0] ∧ !lenbitdef [2, #0] ∧
      ∀[#0 < #1 + 1] (!pow2def [#0] → 2 < #0 →
        (!lenbitdef [#0, #1] ↔ ∃[#0 < #1 + 1] (!sqrtdef [#0, #1] ∧ #0 * #0 = #1 ∧ !lenbitdef [#0, #2])))”, by simp⟩

lemma sppow2_defined : Σᴬ[0]-Predicate (SPPow2 : M → Prop) sppow2def := by
  intro v; simp[SPPow2, sppow2def, Matrix.vecHead, Matrix.vecTail, lenbit_defined.pval, pow2_defined.pval, sqrt_defined.pval, ←le_iff_lt_succ, sq]
  intro _ _; apply ball_congr; intro x _; apply imp_congr_right; intro _; apply imp_congr_right; intro _; apply iff_congr
  · simp
  · constructor
    · intro h; exact ⟨√x, by simpa using h⟩
    · rintro ⟨_, _, rfl, h⟩; exact h

def IsPPow2 (i : M) : Prop := IsPow2 i ∧ ∃ m < 2 * i, SPPow2 m ∧ LenBit i m

def ppow2def : Σᴬ[0] 1 :=
  ⟨“!pow2def [#0] ∧ ∃[#0 < 2 * #1] (!sppow2def [#0] ∧ !lenbitdef [#1, #0])”, by simp⟩

lemma ppow2_defined : Σᴬ[0]-Predicate (IsPPow2 : M → Prop) ppow2def := by
  intro v; simp[IsPPow2, ppow2def, Matrix.vecHead, Matrix.vecTail, lenbit_defined.pval, pow2_defined.pval, sppow2_defined.pval]

namespace SPPow2

variable {m : M} (hm : SPPow2 m)

lemma not_lenbit_one : ¬LenBit 1 m := hm.1

lemma lenbit_two : LenBit 2 m := hm.2.1

lemma lenbit_iff {i : M} (hi : i ≤ m) (pi : IsPow2 i) (lt2 : 2 < i) :
    LenBit i m ↔ (√i)^2 = i ∧ LenBit (√i) m := hm.2.2 i hi pi lt2

lemma one_lt {i : M} (hi : LenBit i m) : 1 < i := by
  by_contra A
  rcases (le_one_iff_eq_zero_or_one.mp (show i ≤ 1 from by simpa using A)) with (rfl | rfl)
  · simp at hi
  · exact hm.1 hi

lemma two_lt {i : M} (hi : LenBit i m) (ne2 : i ≠ 2) : 2 < i :=
  lt_of_le_of_ne (one_lt_iff_two_le.mp $ hm.one_lt hi) (Ne.symm ne2)

lemma sqrt {i : M} (hi : LenBit i m) (pi : IsPow2 i) (ne2 : i ≠ 2) :
    LenBit (√i) m := ((hm.lenbit_iff hi.le pi (hm.two_lt hi ne2)).mp hi).2

lemma sq_sqrt_eq {i : M} (hi : LenBit i m) (pi : IsPow2 i) (ne2 : i ≠ 2) :
    (√i)^2 = i := ((hm.lenbit_iff hi.le pi (hm.two_lt hi ne2)).mp hi).1

lemma of_sqrt {i : M} (pi : IsPow2 i) (him : i ≤ m) (hsqi : (√i)^2 = i) (hi : LenBit (√i) m) :
    LenBit i m := by
  by_cases ne1 : i = 1
  · rcases ne1; simpa using hi
  · have ne2 : i ≠ 2 := by
      rintro rfl; simp [sqrt_two] at hsqi
    have : 2 < i := lt_of_le_of_ne
      (one_lt_iff_two_le.mp <| lt_of_le_of_ne (pos_iff_one_le.mp pi.pos) <| Ne.symm ne1) (Ne.symm ne2)
    exact (hm.lenbit_iff him pi this).mpr ⟨hsqi, hi⟩

@[simp] lemma two : SPPow2 (2 : M) :=
  ⟨by simp[LenBit.one], by simp, by
    intro i hi pi
    rcases le_two_iff_eq_zero_or_one_or_two.mp hi with (rfl | rfl | rfl) <;> simp⟩

@[simp] lemma not_zero : ¬SPPow2 (0 : M) := by
  rintro ⟨_, h, _⟩; simp at h

@[simp] lemma not_one : ¬SPPow2 (1 : M) := by
  rintro ⟨_, h, _⟩; simp [LenBit.iff_rem, one_lt_two] at h

lemma sq_le_of_lt {i j : M} (pi : IsPow2 i) (pj : IsPow2 j) (hi : LenBit i m) (hj : LenBit j m) : i < j → i^2 ≤ j := by
  intro hij
  refine hierarchy_order_induction₁ M Σ 0
    (fun m j ↦ ∀ i < j, IsPow2 i → IsPow2 j → LenBit i m → LenBit j m → i^2 ≤ j)
    ⟨⟨“ ∀[#0 < #2](!pow2def [#0] → !pow2def [#2] → !lenbitdef [#0, #1] → !lenbitdef [#2, #1] → #0 * #0 ≤ #2)”, by simp⟩,
      by intro v; simp [Semiformula.eval_substs, Matrix.vecHead, pow2_defined.pval, lenbit_defined.pval, sq]⟩ m ?_ j i hij pi pj hi hj
  simp; intro j ih i hij pi pj  hi hj
  by_cases jne2 : j = 2
  · rcases jne2 with rfl
    have : 2 ≤ i := one_lt_iff_two_le.mp (hm.one_lt hi)
    exact False.elim ((not_lt.mpr this) hij)
  · by_cases ine2 : i = 2
    · rcases ine2 with rfl
      simpa [sq, two_mul_two_eq_four] using pj.four_le hij
    · have : √i < √j := by
        by_contra A
        have : j ≤ i := by
          simpa [hm.sq_sqrt_eq hi pi ine2, hm.sq_sqrt_eq hj pj jne2] using
            sq_le_sq_iff.mp (show √j ≤ √i from by simpa using A)
        exact False.elim ((not_lt.mpr this) (by simpa using hij))
      have : i ≤ √j := by
        simpa [hm.sq_sqrt_eq hi pi ine2] using
          ih (√j) (sqrt_lt_self_of_one_lt (hm.one_lt hj)) (√i) this
            (pi.sqrt (hm.sq_sqrt_eq hi pi ine2)) (pj.sqrt (hm.sq_sqrt_eq hj pj jne2)) (hm.sqrt hi pi ine2) (hm.sqrt hj pj jne2)
      simpa [hm.sq_sqrt_eq hj pj jne2] using sq_le_sq_iff.mp this

lemma last_uniq {i j : M} (pi : IsPow2 i) (pj : IsPow2 j) (hi : LenBit i m) (hj : LenBit j m)
    (hsqi : m < i^2) (hsqj : m < j^2) : i = j := by
  by_contra ne
  wlog hij : i < j
  · exact this hm pj pi hj hi hsqj hsqi (Ne.symm ne) (lt_of_le_of_ne (by simpa using hij) (Ne.symm ne))
  have : i^2 ≤ m := le_trans  (hm.sq_le_of_lt pi pj hi hj hij) hj.le
  have ltsqi : 2 < i^2 := lt_of_le_of_ne (one_lt_iff_two_le.mp $ by simpa using hm.one_lt hi) (by simp)
  have : LenBit (i^2) m ↔ LenBit i m := by simpa using hm.lenbit_iff this pi.sq ltsqi
  have : LenBit (i^2) m := this.mpr hi
  have : ¬m < i^2 := by simp; exact this.le
  contradiction

end SPPow2

namespace IsPPow2

lemma pow2 {i : M} (h : IsPPow2 i) : IsPow2 i := h.1

lemma pos {i : M} (ppi : IsPPow2 i) : 0 < i := ppi.pow2.pos

lemma one_lt {i : M} (ppi : IsPPow2 i) : 1 < i := by
  rcases ppi with ⟨_, m, _, sppm, lb⟩; exact sppm.one_lt lb

lemma sq_sqrt_eq {i : M} (ppi : IsPPow2 i) (ne2 : i ≠ 2) : (√i)^2 = i := by
  rcases ppi with ⟨pi, m, _, sppm, lb⟩
  exact ((sppm.lenbit_iff lb.le pi (lt_of_le_of_ne (one_lt_iff_two_le.mp $ sppm.one_lt lb) (Ne.symm ne2))).mp lb).1

lemma sqrt {i : M} (ppi : IsPPow2 i) (ne2 : i ≠ 2) : IsPPow2 (√i) := by
  rcases ppi with ⟨pi, m, _, sppm, him⟩
  have : LenBit i m ↔ (√i)^2 = i ∧ LenBit (√i) m :=
    sppm.lenbit_iff him.le pi (lt_of_le_of_ne (one_lt_iff_two_le.mp $ sppm.one_lt him) (Ne.symm ne2))
  rcases this.mp him with ⟨e, H⟩
  have psqi : IsPow2 (√i) := IsPow2.sq_iff.mp (by simp [e, pi])
  have one_lt_sqi : 1 < √i := one_lt_sq_iff.mp (by simpa [e] using sppm.one_lt him)
  have : SPPow2 (m mod (2 * √i)) :=
    ⟨ by simpa [LenBit.remainder] using sppm.not_lenbit_one,
      (LenBit.remainder_pow2 (by simp) (by simp [psqi]) (by simp [one_lt_sqi])).mpr sppm.lenbit_two,
      by  intro j hj pj lt2
          have hjsi : j < 2 * √i := lt_of_le_of_lt hj (remainder_lt _ (by simp [psqi.pos]))
          have : LenBit j m ↔ (√j) ^ 2 = j ∧ LenBit (√j) m := sppm.lenbit_iff (le_trans hj (by simp)) pj lt2
          rw [LenBit.remainder_pow2, this] <;> try simp [pj, psqi, hjsi]
          intro hsqj
          have : IsPow2 (√j) := pj.sqrt hsqj
          rw [LenBit.remainder_pow2] <;> try simp [psqi, this]
          · exact lt_of_le_of_lt (by simp) hjsi⟩
  exact ⟨psqi, m mod (2 * √i), remainder_lt _ (by simp [psqi.pos]), this, by simp [H]⟩

lemma exists_spp {i : M} (h : IsPPow2 i) : ∃ m < 2 * i, SPPow2 m ∧ LenBit i m := h.2

protected lemma sq {i : M} (ppi : IsPPow2 i) : IsPPow2 (i^2) := by
  rcases ppi.exists_spp with ⟨m, hm, sppm, hi⟩
  have sppm' : SPPow2 (m + i^2) :=
    ⟨by rw [LenBit.add_pow2] <;> try simp [ppi.pow2, sppm.not_lenbit_one, sppm.one_lt hi],
     by rw [LenBit.add_pow2] <;> try simp [ppi.pow2, sppm.lenbit_two]
        exact lt_of_le_of_ne (ppi.pow2.sq.two_le $ by simp; rintro rfl; exact sppm.not_lenbit_one hi) (by simp),
     by intro j hj pj lt2
        have hsqi : i < i^2 := lt_square_of_lt ppi.one_lt
        have hmi : m < i^2 := lt_of_lt_of_le hm (two_mul_le_sq $ one_lt_iff_two_le.mp $ sppm.one_lt hi)
        rw [LenBit.add_pow2_iff] <;> try simp [pj, ppi.pow2, hmi]
        constructor
        · rintro (rfl | hj)
          · simp; rw [LenBit.add_pow2] <;> simp [hi, ppi.pow2, hsqi]
          · have : (√j)^2 = j := sppm.sq_sqrt_eq hj pj (ne_of_gt lt2)
            rw [LenBit.add_pow2_iff] <;> try simp [ppi.pow2, pj.sqrt this, hmi]
            simp [sppm.sqrt hj pj (ne_of_gt lt2), this]
        · rintro ⟨ej, lb⟩
          have hsqj : √j < i^2 := lt_of_mul_lt_mul_left (a := 2) (by calc
            2 * √j ≤ (√j)^2  := two_mul_le_sq
                                    (one_lt_iff_two_le.mp <| one_lt_sq_iff.mp <| by
                                      rw [ej]; exact lt_trans _ _ _ one_lt_two lt2)
            _      ≤ j       := by simp
            _      ≤ m + i^2 := hj
            _      < 2 * i^2 := by simp [two_mul, hmi])
          have hsqj : LenBit (√j) m := (LenBit.add_pow2 (pj.sqrt ej) ppi.pow2.sq hsqj).mp lb
          by_cases hjm : j ≤ m
          · exact Or.inr <| sppm.of_sqrt pj hjm ej hsqj
          · have : i = √j := sppm.last_uniq ppi.pow2 (pj.sqrt ej) hi hsqj hmi (by simpa [ej] using hjm)
            left; simp [this, ej]⟩
  by_cases ne1 : i = 1
  · rcases ne1; simpa using ppi
  have : m < i^2 :=
    lt_of_lt_of_le hm
      (two_mul_le_sq $ one_lt_iff_two_le.mp $ lt_of_le_of_ne (pos_iff_one_le.mp $ ppi.pos) (Ne.symm ne1))
  exact ⟨ppi.pow2.sq, m + i^2,
    by simp [two_mul, hm, this],
    sppm', LenBit.add_self this⟩

@[simp] lemma two : IsPPow2 (2 : M) := ⟨by simp, 2, by simp [one_lt_two]⟩

@[simp] lemma not_zero : ¬IsPPow2 (0 : M) := by intro h; simpa using h.pow2

@[simp] lemma not_one : ¬IsPPow2 (1 : M) := by
  rintro ⟨_, m, hm, H, _⟩
  have : m ≤ 1 := lt_two_iff_le_one.mp (by simpa using hm)
  rcases le_one_iff_eq_zero_or_one.mp this with (rfl | rfl) <;> simp at H

lemma elim {i : M} : IsPPow2 i ↔ i = 2 ∨ ∃ b, i = b^2 ∧ IsPPow2 b := by
  by_cases ei : i = 2
  · rcases ei with rfl; simp
  · simp [ei]; constructor
    · rintro ppi
      exact ⟨√i, Eq.symm <| ppi.sq_sqrt_eq ei, ppi.sqrt ei⟩
    · rintro ⟨j, rfl, ppj⟩
      exact ppj.sq

lemma elim' {i : M} : IsPPow2 i ↔ i = 2 ∨ 2 < i ∧ ∃ j, i = j^2 ∧ IsPPow2 j := by
  by_cases ha : 2 < i <;> simp [ha, ←elim]
  have : i = 0 ∨ i = 1 ∨ i = 2 := by simpa [le_two_iff_eq_zero_or_one_or_two] using ha
  rcases this with (rfl | rfl | rfl) <;> simp

@[simp] lemma four : IsPPow2 (4 : M) := elim.mpr (Or.inr <| ⟨2, by simp [two_pow_two_eq_four]⟩)

lemma two_le {i : M} (hi : IsPPow2 i) : 2 ≤ i := by
  simp [←one_add_one_eq_two, ←lt_iff_succ_le, hi.one_lt]

lemma not_three : ¬IsPPow2 (3 : M) := by
  intro h; simpa [sqrt_three] using h.sqrt (by simp)

lemma two_lt {i : M} (hi : IsPPow2 i) (ne : i ≠ 2) : 2 < i := by
  by_contra A; simp [ne, le_iff_lt_or_eq, lt_two_iff_le_one] at A
  rcases A with (rfl | rfl) <;> simp at hi

lemma four_le {i : M} (hi : IsPPow2 i) (ne : i ≠ 2) : 4 ≤ i := by
  by_contra A
  have : i ≤ 3 := by simpa [←three_add_one_eq_four, ←le_iff_lt_succ] using A
  rcases le_three_iff_eq_zero_or_one_or_two_or_three.mp this with (rfl | rfl | rfl | rfl) <;> simp at ne hi
  · have : IsPPow2 (1 : M) := by simpa [sqrt_three] using hi.sqrt (by simp)
    simp at this

lemma four_lt {i : M} (hi : IsPPow2 i) (ne2 : i ≠ 2) (ne4 : i ≠ 4) : 4 < i :=
  Ne.lt_of_le (Ne.symm ne4) (hi.four_le ne2)

lemma sq_ne_two {i : M} (hi : IsPPow2 i) : i^2 ≠ 2 := by
  intro e; have : i < 2 := by simpa [←e] using lt_square_of_lt hi.one_lt
  exact not_le.mpr this hi.two_le

lemma sqrt_ne_two {i : M} (hi : IsPPow2 i) (ne2 : i ≠ 2) (ne4 : i ≠ 4) : √i ≠ 2 := by
  intro e
  have : i = 4 := by simpa [e, two_pow_two_eq_four] using Eq.symm <| hi.sq_sqrt_eq ne2
  contradiction

lemma sq_ne_four {i : M} (hi : IsPPow2 i) (ne2 : i ≠ 2) : i^2 ≠ 4 := by
  simpa [two_pow_two_eq_four] using ne_of_gt (sq_lt_sq_iff.mp (hi.two_lt ne2))

lemma sq_le_of_lt {i j : M} (hi : IsPPow2 i) (hj : IsPPow2 j) : i < j → i^2 ≤ j := by
  intro hij
  refine hierarchy_order_induction₀ M Σ 0 (fun j ↦ ∀ i < j, IsPPow2 i → IsPPow2 j → i^2 ≤ j)
    ⟨⟨“ ∀[#0 < #1](!ppow2def [#0] → !ppow2def [#1] → #0 * #0 ≤ #1)”, by simp⟩,
      by intro v; simp [Semiformula.eval_substs, Matrix.vecHead, ppow2_defined.pval, sq]⟩ ?_ j i hij hi hj
  simp; intro j ih i hij hi hj
  by_cases ej : j = 2
  · have : 2 ≤ i := by simpa [one_add_one_eq_two] using lt_iff_succ_le.mp hi.one_lt
    exact False.elim ((not_lt.mpr this) (by simpa [ej] using hij))
  · by_cases ei : i = 2
    · rcases ei with rfl
      simpa [sq, two_mul_two_eq_four] using hj.four_le ej
    · have : √i < √j := by
        by_contra A
        have : j ≤ i := by simpa [hi.sq_sqrt_eq ei, hj.sq_sqrt_eq ej] using sq_le_sq_iff.mp (show √j ≤ √i from by simpa using A)
        exact False.elim ((not_lt.mpr this) (by simpa using hij))
      have : i ≤ √j := by
        simpa [hi.sq_sqrt_eq ei] using
          ih (√j) (sqrt_lt_self_of_one_lt hj.one_lt) (√i) this (hi.sqrt ei) (hj.sqrt ej)
      simpa [hj.sq_sqrt_eq ej] using sq_le_sq_iff.mp this

lemma sq_uniq {y i j : M} (py : IsPow2 y) (ppi : IsPPow2 i) (ppj : IsPPow2 j)
    (hi : y < i ∧ i ≤ y^2) (hj : y < j ∧ j ≤ y^2) : i = j := by
  by_contra ne
  wlog hij : i < j
  · exact this py ppj ppi hj hi (Ne.symm ne) (Ne.lt_of_le' ne (by simpa using hij))
  have : y^2 < y^2 := calc
    y^2 < i^2 := sq_lt_sq_iff.mp hi.1
    _   ≤ j   := sq_le_of_lt ppi ppj hij
    _   ≤ y^2 := hj.2
  simp_all

lemma two_mul_sq_uniq {y i j : M} (py : IsPow2 y) (ppi : IsPPow2 i) (ppj : IsPPow2 j)
    (hi : y < i ∧ i ≤ 2 * y^2) (hj : y < j ∧ j ≤ 2 * y^2) : i = j := by
  by_contra ne
  wlog hij : i < j
  · exact this py ppj ppi hj hi (Ne.symm ne) (Ne.lt_of_le' ne (by simpa using hij))
  have : i^2 < (2 * y)^2 := calc
    i^2 ≤ j         := sq_le_of_lt ppi ppj hij
    _   ≤ 2 * y^2   := hj.2
    _   < (2 * y)^2 := by
      simp [sq, mul_assoc]; rw [mul_left_comm]
      exact lt_mul_of_pos_of_one_lt_left (by simpa using pos_iff_ne_zero.mp py.pos) (by simp [one_lt_two])
  have : i < 2 * y := sq_lt_sq_iff.mpr this
  have : y < y := lt_of_lt_of_le hi.1 ((ppi.pow2.le_iff_lt_two py).mpr this)
  simp_all

end IsPPow2

def ext (u z : M) : M := z /ₑ u mod u

lemma ext_graph (a b c : M) : a = ext b c ↔ ∃ x ≤ c, x = c /ₑ b ∧ a = x mod b := by
  simp [ext]; constructor
  · rintro rfl; exact ⟨c /ₑ b, by simp, rfl, by rfl⟩
  · rintro ⟨_, _, rfl, rfl⟩; simp

def extdef : Σᴬ[0] 3 :=
  ⟨“∃[#0 < #3 + 1] (!edivdef [#0, #3, #2] ∧ !remdef [#1, #0, #2])”, by simp⟩

lemma ext_defined : Σᴬ[0]-Function₂ (λ a b : M ↦ ext a b) extdef := by
  intro v; simp [Matrix.vecHead, Matrix.vecTail, extdef,
    ext_graph, Semiformula.eval_substs, ediv_defined.pval, rem_defined.pval, le_iff_lt_succ]

@[simp] lemma ext_le_add (u z : M) : ext u z ≤ z :=
  le_trans (remainder_le (z /ₑ u) u) (by simp [add_comm])

@[simp] lemma ext_lt {u} (z : M) (pos : 0 < u) : ext u z < u := by simp [ext, pos]

lemma ext_add_of_dvd_sq_right {u z₁ z₂ : M} (pos : 0 < u) (h : u^2 ∣ z₂) : ext u (z₁ + z₂) = ext u z₁ := by
  simp [ext]
  have : ∃ z', z₂ = z' * u * u := by rcases h with ⟨u', rfl⟩; exact ⟨u', by simp [mul_comm _ u', mul_assoc]; simp [sq]⟩
  rcases this with ⟨z₂, rfl⟩
  simp [ediv_add_mul_self, pos]

lemma ext_add_of_dvd_sq_left {u z₁ z₂ : M} (pos : 0 < u) (h : u^2 ∣ z₁) : ext u (z₁ + z₂) = ext u z₂ := by
  rw [add_comm]; exact ext_add_of_dvd_sq_right pos h

lemma ext_rem {i j z : M} (ppi : IsPPow2 i) (ppj : IsPPow2 j) (hij : i < j) : ext i (z mod j) = ext i z := by
  have := ediv_add_remainder z j
  have : i^2 ∣ j := ppi.pow2.sq.dvd_of_le ppj.pow2 (IsPPow2.sq_le_of_lt ppi ppj hij)
  calc
    ext i (z mod j) = ext i (j * (z /ₑ j) + (z mod j)) := by symm; exact ext_add_of_dvd_sq_left ppi.pos (Dvd.dvd.mul_right this (z /ₑ j))
    _               = ext i z                          := by simp [ediv_add_remainder]

def Exp.Seq₀ (X Y : M) : Prop := ext 4 X = 1 ∧ ext 4 Y = 2

def Exp.Seqₛ.Even (X Y u : M) : Prop := ext (u^2) X = 2 * ext u X ∧ ext (u^2) Y = (ext u Y)^2

def Exp.Seqₛ.Odd (X Y u : M) : Prop := ext (u^2) X = 2 * ext u X + 1 ∧ ext (u^2) Y = 2 * (ext u Y)^2

def Exp.Seqₛ (y X Y : M) : Prop := ∀ u ≤ y, u ≠ 2 → IsPPow2 u → Seqₛ.Even X Y u ∨ Seqₛ.Odd X Y u

def Exp.Seqₘ (x y X Y : M) : Prop := ∃ u ≤ y^2, u ≠ 2 ∧ IsPPow2 u ∧ ext u X = x ∧ ext u Y = y

def Exp (x y : M) : Prop := (x = 0 ∧ y = 1) ∨ ∃ X ≤ y^4, ∃ Y ≤ y^4, Exp.Seq₀ X Y ∧ Exp.Seqₛ y X Y ∧ Exp.Seqₘ x y X Y

lemma Exp.Seqₛ.iff (y X Y : M) :
  Exp.Seqₛ y X Y ↔
  ∀ u ≤ y, u ≠ 2 → IsPPow2 u →
    ((∃ ext_u_X ≤ X, ext_u_X = ext u X ∧ 2 * ext_u_X = ext (u^2) X)     ∧ (∃ ext_u_Y ≤ Y, ext_u_Y = ext u Y ∧ ext_u_Y^2 = ext (u^2) Y)) ∨
    ((∃ ext_u_X ≤ X, ext_u_X = ext u X ∧ 2 * ext_u_X + 1 = ext (u^2) X) ∧ (∃ ext_u_Y ≤ Y, ext_u_Y = ext u Y ∧ 2 * ext_u_Y^2 = ext (u^2) Y)) :=
  ⟨by intro H u hu ne2 ppu
      rcases H u hu ne2 ppu with (H | H)
      · exact Or.inl ⟨⟨ext u X, by simp [H.1]⟩, ⟨ext u Y, by simp [H.2]⟩⟩
      · exact Or.inr ⟨⟨ext u X, by simp [H.1]⟩, ⟨ext u Y, by simp [H.2]⟩⟩,
   by intro H u hu ne2 ppu
      rcases H u hu ne2 ppu with (⟨⟨_, _, rfl, hx⟩, ⟨_, _, rfl, hy⟩⟩ | ⟨⟨_, _, rfl, hx⟩, ⟨_, _, rfl, hy⟩⟩)
      · exact Or.inl ⟨by simp [hx, hy], by simp [hx, hy]⟩
      · exact Or.inr ⟨by simp [hx, hy], by simp [hx, hy]⟩⟩

def Exp.Seqₛ.def : Σᴬ[0] 3 := ⟨
  “∀[#0 < #1 + 1](#0 ≠ 2 → !ppow2def [#0] →
    ( ∃[#0 < #3 + 1] (!extdef [#0, #1, #3] ∧ !extdef [2 * #0, #1 * #1, #3]) ∧
      ∃[#0 < #4 + 1] (!extdef [#0, #1, #4] ∧ !extdef [#0 * #0, #1 * #1, #4]) ) ∨
    ( ∃[#0 < #3 + 1] (!extdef [#0, #1, #3] ∧ !extdef [2 * #0 + 1, #1 * #1, #3]) ∧
      ∃[#0 < #4 + 1] (!extdef [#0, #1, #4] ∧ !extdef [2 * (#0 * #0), #1 * #1, #4])))”, by simp⟩

lemma Exp.Seqₛ.defined : Σᴬ[0]-Relation₃ (Exp.Seqₛ : M → M → M → Prop) Exp.Seqₛ.def := by
  intro v; simp [Exp.Seqₛ.iff, Exp.Seqₛ.def, ppow2_defined.pval, ext_defined.pval, ←le_iff_lt_succ, sq]

lemma Exp.graph_iff (x y : M) :
    Exp x y ↔
    (x = 0 ∧ y = 1) ∨ ∃ X ≤ y^4, ∃ Y ≤ y^4,
      (1 = ext 4 X ∧ 2 = ext 4 Y) ∧
      Exp.Seqₛ y X Y ∧
      (∃ u ≤ y^2, u ≠ 2 ∧ IsPPow2 u ∧ x = ext u X ∧ y = ext u Y) :=
  ⟨by rintro (H | ⟨X, bX, Y, bY, H₀, Hₛ, ⟨u, hu, ne2, ppu, hX, hY⟩⟩)
      · exact Or.inl H
      · exact Or.inr ⟨X, bX, Y, bY, ⟨H₀.1.symm, H₀.2.symm⟩, Hₛ, ⟨u, hu, ne2, ppu, hX.symm, hY.symm⟩⟩,
   by rintro (H | ⟨X, bX, Y, bY, H₀, Hₛ, ⟨u, hu, ne2, ppu, hX, hY⟩⟩)
      · exact Or.inl H
      · exact Or.inr ⟨X, bX, Y, bY, ⟨H₀.1.symm, H₀.2.symm⟩, Hₛ, ⟨u, hu, ne2, ppu, hX.symm, hY.symm⟩⟩⟩

def Exp.def : Σᴬ[0] 2 := ⟨
  “(#0 = 0 ∧ #1 = 1) ∨ (
    ∃[#0 < #2 * #2 * #2 * #2 + 1] ∃[#0 < #3 * #3 * #3 * #3 + 1] (
      (!extdef [1, 4, #1] ∧ !extdef [2, 4, #0]) ∧
      !Exp.Seqₛ.def [#3, #1, #0] ∧
      ∃[#0 < #4 * #4 + 1] (#0 ≠ 2 ∧ !ppow2def [#0] ∧ !extdef [#3, #0, #2] ∧!extdef [#4, #0, #1])))”, by { simp }⟩

lemma Exp.defined : Σᴬ[0]-Relation (Exp : M → M → Prop) Exp.def := by
  intro v; simp [Exp.graph_iff, Exp.def, ppow2_defined.pval, ext_defined.pval, Exp.Seqₛ.defined.pval, ←le_iff_lt_succ, pow_four, sq]

namespace Exp

def seqX₀ : M := 4

def seqY₀ : M := 2 * 4

lemma one_lt_four : (1 : M) < 4 := by
  rw [←three_add_one_eq_four]
  exact lt_add_of_pos_left 1 three_pos

lemma two_lt_three : (2 : M) < 3 := by rw [←two_add_one_eq_three]; exact lt_add_one 2

lemma three_lt_four : (3 : M) < 4 := by rw [←three_add_one_eq_four]; exact lt_add_one 3

lemma two_lt_four : (2 : M) < 4 := lt_trans _ _ _ two_lt_three three_lt_four

lemma seq₀_zero_two : Seq₀ (seqX₀ : M) (seqY₀ : M) := by simp [seqX₀, seqY₀, Seq₀, ext, one_lt_four, two_lt_four]

lemma Seq₀.rem {X Y i : M} (h : Seq₀ X Y) (ppi : IsPPow2 i) (hi : 4 < i) :
    Seq₀ (X mod i) (Y mod i) := by
  rw [Seq₀, ext_rem, ext_rem] <;> try simp [ppi, hi]
  exact h

lemma Seqₛ.rem {y y' X Y i : M} (h : Seqₛ y X Y) (ppi : IsPPow2 i) (hi : y'^2 < i) (hy : y' ≤ y) :
    Seqₛ y' (X mod i) (Y mod i) := by
  intro j hj ne2 ppj
  have : j^2 < i := lt_of_le_of_lt (sq_le_sq_iff.mp hj) hi
  have : j < i := lt_of_le_of_lt (le_trans hj $ by simp) hi
  rcases h j (le_trans hj hy) ne2 ppj with (H | H)
  · left; simpa [Seqₛ.Even, ext_rem, ppj, ppj.sq, ppi, *] using H
  · right; simpa [Seqₛ.Odd, ext_rem, ppj, ppj.sq, ppi, *] using H

lemma seqₛ_one_zero_two : Seqₛ (1 : M) (seqX₀ : M) (seqY₀ : M) := by
  intro u leu; rcases le_one_iff_eq_zero_or_one.mp leu with (rfl | rfl) <;> simp

def append (i X z : M) : M := (X mod i) + z * i

lemma append_lt (i X : M) {z} (hz : z < i) : append i X z < i^2 := calc
  append i X z = (X mod i) + z * i := rfl
  _            < (1 + z) * i       := by simp [add_mul]; exact remainder_lt _ (pos_of_gt hz)
  _            ≤ i^2               := by simp [sq, add_comm]; exact mul_le_mul_of_nonneg_right (lt_iff_succ_le.mp hz) (by simp)

lemma ext_append_last (i X : M) {z} (hz : z < i) :
    ext i (append i X z) = z := by
  simp [ext, append, ediv_add_mul_self, show 0 < i from pos_of_gt hz, hz]

lemma ext_append_of_lt {i j : M} (hi : IsPPow2 i) (hj : IsPPow2 j) (hij : i < j) (X z : M) :
    ext i (append j X z) = ext i X := by
  have : i^2 ∣ j := IsPow2.dvd_of_le hi.pow2.sq hj.pow2 (IsPPow2.sq_le_of_lt hi hj hij)
  calc
    ext i (append j X z) = ext i ((X mod j) + z * j)        := rfl
    _                    = ext i (X mod j)                  := ext_add_of_dvd_sq_right hi.pos (Dvd.dvd.mul_left this z)
    _                    = ext i (j * (X /ₑ j) + (X mod j)) := by rw [add_comm]
                                                                  refine Eq.symm <| ext_add_of_dvd_sq_right hi.pos (Dvd.dvd.mul_right this _)
    _                    = ext i X                          := by simp [ediv_add_remainder]

lemma Seq₀.append {X Y i x y : M} (H : Seq₀ X Y) (ppi : IsPPow2 i) (hi : 4 < i) :
    Seq₀ (append i X x) (append i Y y) := by
  rw [Seq₀, ext_append_of_lt, ext_append_of_lt] <;> try simp [ppi, hi]
  exact H

lemma Seqₛ.append {z x y X Y i : M} (h : Seqₛ z X Y) (ppi : IsPPow2 i) (hz : z < i) :
    Seqₛ z (append (i^2) X x) (append (i^2) Y y) := by
  intro j hj ne2 ppj
  have : j < i^2 := lt_of_lt_of_le (lt_of_le_of_lt hj hz) (by simp)
  have : j^2 < i^2 := sq_lt_sq_iff.mp (lt_of_le_of_lt hj hz)
  rcases h j hj ne2 ppj with (H | H) <;> simp [Even, Odd]
  · left; rw [ext_append_of_lt, ext_append_of_lt, ext_append_of_lt, ext_append_of_lt] <;> try simp [ppi.sq, ppj.sq, *]
    exact H
  · right; rw [ext_append_of_lt, ext_append_of_lt, ext_append_of_lt, ext_append_of_lt] <;> try simp [ppi.sq, ppj.sq, *]
    exact H

@[simp] lemma exp_zero_one : Exp (0 : M) 1 := Or.inl (by simp)

lemma pow_three (x : M) : x^3 = x * x * x := by simp [← two_add_one_eq_three, pow_add, sq]

lemma pow_four (x : M) : x^4 = x * x * x * x := by simp [← three_add_one_eq_four, pow_add, pow_three]

lemma pow_four_eq_sq_sq (x : M) : x^4 = (x^2)^2 := by simp [pow_four, sq, mul_assoc]

@[simp] lemma exp_one_two : Exp (1 : M) 2 :=
  Or.inr ⟨
    4, by simp [pow_four_eq_sq_sq, two_pow_two_eq_four],
    2 * 4, by simp [pow_four_eq_sq_sq, two_pow_two_eq_four, sq (4 : M)]; exact le_of_lt two_lt_four,
    by simp [Seq₀, ext, one_lt_four, two_lt_four],
    by simp [Seqₛ]; intro i hi ne2 ppi; exact False.elim <| not_le.mpr (ppi.two_lt ne2) hi,
    ⟨4, by simp [two_pow_two_eq_four], by simp, by simp [ext, one_lt_four, two_lt_four]⟩⟩

lemma pow2_ext_of_seq₀_of_seqₛ {y X Y : M} (h₀ : Exp.Seq₀ X Y) (hₛ : Exp.Seqₛ y X Y)
    {i} (ne2 : i ≠ 2) (hi : i ≤ y^2) (ppi : IsPPow2 i) : IsPow2 (ext i Y) := by
  refine hierarchy_order_induction₂ M Σ 0 (fun y Y i ↦ i ≠ 2 → i ≤ y^2 → IsPPow2 i → IsPow2 (ext i Y))
    ⟨⟨“#2 ≠ 2 → #2 ≤ #0 * #0 → !ppow2def [#2] → ∃[#0 < #2 + 1] (!extdef [#0, #3, #2] ∧ !pow2def [#0])”, by simp⟩,
     by intro v
        simp [sq, Semiformula.eval_substs, pow2_defined.pval, ppow2_defined.pval, ext_defined.pval]
        apply imp_congr_right; intro _; apply imp_congr_right; intro _; apply imp_congr_right; intro _
        exact ⟨fun h ↦ ⟨ext (v 2) (v 1), by simp [← le_iff_lt_succ, h]⟩,
          by rintro ⟨x, _, rfl, h⟩; exact h⟩⟩ y Y ?_ i ne2 hi ppi
  simp; intro i IH ne2 hi ppi
  by_cases ei : i = 4
  · rcases ei with rfl; simp [h₀.2]
  · have ppsq : IsPow2 (ext (√i) Y) :=
      IH (√i) (sqrt_lt_self_of_one_lt ppi.one_lt) (ppi.sqrt_ne_two ne2 ei) (le_trans (by simp) hi) (ppi.sqrt ne2)
    rcases show Seqₛ.Even X Y (√i) ∨ Seqₛ.Odd X Y (√i) from
      hₛ (√i) (sqrt_le_of_le_sq $ hi) (ppi.sqrt_ne_two ne2 ei) (ppi.sqrt ne2) with (heven | hodd)
    · have : ext i Y = (ext (√i) Y)^2 := by simpa [ppi.sq_sqrt_eq ne2] using heven.2
      simp [this, ppsq]
    · have : ext i Y = 2*(ext (√i) Y)^2 := by simpa [ppi.sq_sqrt_eq ne2] using hodd.2
      simp [this, ppsq]

lemma range_pow2 {x y : M} (h : Exp x y) : IsPow2 y := by
  rcases h with (⟨rfl, rfl⟩ | ⟨X, bX, Y, bY, H₀, Hₛ, ⟨u, hu, ne2, ppu, rfl, rfl⟩⟩)
  · simp
  · exact pow2_ext_of_seq₀_of_seqₛ H₀ Hₛ ne2 hu ppu

lemma le_sq_ext_of_seq₀_of_seqₛ {y X Y : M} (h₀ : Exp.Seq₀ X Y) (hₛ : Exp.Seqₛ y X Y)
    {i} (ne2 : i ≠ 2) (hi : i ≤ y^2) (ppi : IsPPow2 i) : i ≤ (ext i Y)^2 := by
  refine hierarchy_order_induction₂ M Σ 0 (fun y Y i ↦ i ≠ 2 → i ≤ y^2 → IsPPow2 i → i ≤ (ext i Y)^2)
    ⟨⟨“#2 ≠ 2 → #2 ≤ #0 * #0 → !ppow2def [#2] → ∃[#0 < #2 + 1] (!extdef [#0, #3, #2] ∧ #3 ≤ #0 * #0)”, by simp⟩,
     by intro v
        simp [sq, Semiformula.eval_substs, pow2_defined.pval, ppow2_defined.pval, ext_defined.pval]
        apply imp_congr_right; intro _; apply imp_congr_right; intro _; apply imp_congr_right; intro _
        exact ⟨fun h ↦ ⟨ext (v 2) (v 1), by simp [← le_iff_lt_succ, h]⟩,
          by rintro ⟨x, _, rfl, h⟩; exact h⟩⟩ y Y ?_ i ne2 hi ppi
  simp; intro i IH ne2 hi ppi
  by_cases ei : i = 4
  · rcases ei with rfl; simp [h₀.2, two_pow_two_eq_four]
  · have IH : √i ≤ (ext (√i) Y)^2 :=
      IH (√i) (sqrt_lt_self_of_one_lt ppi.one_lt) (ppi.sqrt_ne_two ne2 ei) (le_trans (by simp) hi) (ppi.sqrt ne2)
    rcases show Seqₛ.Even X Y (√i) ∨ Seqₛ.Odd X Y (√i) from
      hₛ (√i) (sqrt_le_of_le_sq $ hi) (ppi.sqrt_ne_two ne2 ei) (ppi.sqrt ne2) with (heven | hodd)
    · have : ext i Y = (ext (√i) Y)^2 := by simpa [ppi.sq_sqrt_eq ne2] using heven.2
      have : √i ≤ ext i Y := by simpa [this] using IH
      simpa [ppi.sq_sqrt_eq ne2] using sq_le_sq_iff.mp this
    · have : ext i Y = 2*(ext (√i) Y)^2 := by simpa [ppi.sq_sqrt_eq ne2] using hodd.2
      have : 2 * √i ≤ ext i Y := by simpa [this] using mul_le_mul_left (a := 2) IH
      have : √i ≤ ext i Y := le_trans (le_mul_of_pos_left $ by simp) this
      simpa [ppi.sq_sqrt_eq ne2] using sq_le_sq_iff.mp this

example {a b c : ℕ} : a * (b * c) = b * (a * c) := by exact Nat.mul_left_comm a b c

lemma two_mul_ext_le_of_seq₀_of_seqₛ {y X Y : M} (h₀ : Exp.Seq₀ X Y) (hₛ : Exp.Seqₛ y X Y)
    {i} (ne2 : i ≠ 2) (hi : i ≤ y^2) (ppi : IsPPow2 i) : 2 * ext i Y ≤ i := by
  refine hierarchy_order_induction₂ M Σ 0 (fun y Y i ↦ i ≠ 2 → i ≤ y^2 → IsPPow2 i → 2 * (ext i Y) ≤ i)
    ⟨⟨“#2 ≠ 2 → #2 ≤ #0 * #0 → !ppow2def [#2] → ∃[#0 < #2 + 1] (!extdef [#0, #3, #2] ∧ 2 * #0 ≤ #3)”, by simp⟩,
     by intro v
        simp [sq, Semiformula.eval_substs, pow2_defined.pval, ppow2_defined.pval, ext_defined.pval]
        apply imp_congr_right; intro _; apply imp_congr_right; intro _; apply imp_congr_right; intro _
        exact ⟨fun h ↦ ⟨ext (v 2) (v 1), by simp [← le_iff_lt_succ, h]⟩,
          by rintro ⟨x, _, rfl, h⟩; exact h⟩⟩ y Y ?_ i ne2 hi ppi
  simp; intro i IH ne2 hi ppi
  by_cases ei : i = 4
  · rcases ei with rfl; simp [h₀.2, two_mul_two_eq_four]
  · have IH : 2 * ext (√i) Y ≤ √i :=
      IH (√i) (sqrt_lt_self_of_one_lt ppi.one_lt) (ppi.sqrt_ne_two ne2 ei) (le_trans (by simp) hi) (ppi.sqrt ne2)
    rcases show Seqₛ.Even X Y (√i) ∨ Seqₛ.Odd X Y (√i) from
      hₛ (√i) (sqrt_le_of_le_sq $ hi) (ppi.sqrt_ne_two ne2 ei) (ppi.sqrt ne2) with (heven | hodd)
    · have : ext i Y = (ext (√i) Y)^2 := by simpa [ppi.sq_sqrt_eq ne2] using heven.2
      calc
        2 * ext i Y ≤ 2 * (2 * ext i Y)  := le_mul_of_pos_left (by simp)
        _           = (2 * ext (√i) Y)^2 := by simp [this, sq, mul_left_comm, mul_assoc]
        _           ≤ (√i)^2             := sq_le_sq_iff.mp IH
        _           = i                  := ppi.sq_sqrt_eq ne2
    · have : ext i Y = 2*(ext (√i) Y)^2 := by simpa [ppi.sq_sqrt_eq ne2] using hodd.2
      calc
        2 * ext i Y = (2 * ext (√i) Y)^2 := by simp [this, sq, mul_left_comm, mul_assoc]
        _           ≤ (√i)^2             := sq_le_sq_iff.mp IH
        _           = i                  := ppi.sq_sqrt_eq ne2

lemma exp_exists_sq_of_exp_even {x y : M} : Exp (2 * x) y → ∃ y', y = y'^2 ∧ Exp x y' := by
  rintro (⟨hx, rfl⟩ | ⟨X, _, Y, _, hseq₀, hseqₛ, i, hi, ne2, ppi, hXx, hYy⟩)
  · exact ⟨1, by simp [show x = 0 from by simpa using hx]⟩
  by_cases ne4 : i = 4
  · rcases ne4 with rfl
    have ex : 1 = 2 * x := by simpa [hseq₀.1] using hXx
    have : (2 : M) ∣ 1 := by rw [ex]; simp
    have : ¬(2 : M) ∣ 1 := not_dvd_of_lt (by simp) one_lt_two
    contradiction
  have : Seqₛ.Even X Y (√i) ∨ Seqₛ.Odd X Y (√i) :=
    hseqₛ (√i) (sqrt_le_of_le_sq hi) (ppi.sqrt_ne_two ne2 ne4) (ppi.sqrt ne2)
  rcases this with (⟨hXi, hYi⟩ | ⟨hXi, _⟩)
  · have hXx : x = ext (√i) X := by simpa [ppi.sq_sqrt_eq ne2, hXx] using hXi
    have hYy : y = (ext (√i) Y)^2 := by simpa [ppi.sq_sqrt_eq ne2, hYy] using hYi
    let X' := X mod i
    let Y' := Y mod i
    have bX' : X' ≤ (ext (√i) Y)^4 := by simp [pow_four_eq_sq_sq, ←hYy]; exact le_trans (le_of_lt $ by simp [ppi.pos]) hi
    have bY' : Y' ≤ (ext (√i) Y)^4 := by simp [pow_four_eq_sq_sq, ←hYy]; exact le_trans (le_of_lt $ by simp [ppi.pos]) hi
    have hseqₛ' : Seqₛ (ext (√i) Y) X' Y' :=
      hseqₛ.rem ppi (sq_lt_of_lt_sqrt $ ext_lt Y (ppi.sqrt ne2).pos) (by simp [hYy])
    have hseqₘ' : Seqₘ x (ext (√i) Y) X' Y' :=
      ⟨√i, sqrt_le_of_le_sq $ by simp [←hYy, hi], ppi.sqrt_ne_two ne2 ne4, ppi.sqrt ne2,
       by have : √i < i := sqrt_lt_self_of_one_lt ppi.one_lt
          simp [this, ext_rem, ppi, ppi.sqrt ne2, hXx]⟩
    have : Exp x (ext (√i) Y) :=
      Or.inr ⟨X', bX', Y', bY', hseq₀.rem ppi (ppi.four_lt ne2 ne4), hseqₛ', hseqₘ'⟩
    exact ⟨ext (√i) Y, hYy, this⟩
  · have : 2 ∣ ext i X := by simp [hXx]
    have : ¬2 ∣ ext i X := by
      simp [show ext i X = 2 * ext (√i) X + 1 from by simpa [ppi.sq_sqrt_eq ne2] using hXi,
        ←remainder_eq_zero_iff_dvd, one_lt_two]
    contradiction

lemma bit_zero {x y : M} : Exp x y → Exp (2 * x) (y ^ 2) := by
  rintro (⟨hx, rfl⟩ | ⟨X, _, Y, _, hseq₀, hseqₛ, i, hi, ne2, ppi, hXx, hYy⟩)
  · rcases hx with rfl; simp
  have hxsqi : 2 * x < i ^ 2 := lt_of_lt_of_le (by simp [←hXx, ppi.pos]) (two_mul_le_sq ppi.two_le)
  have hysqi : y ^ 2 < i ^ 2 := sq_lt_sq_iff.mp $ by simp [←hYy, ppi.pos]
  have hiisq : i < i^2 := lt_square_of_lt ppi.one_lt
  let X' := append (i^2) X (2 * x)
  let Y' := append (i^2) Y (y ^ 2)
  have bX' : X' ≤ (y^2)^4 := by
    have : X' < i^4 := by simpa [pow_four_eq_sq_sq] using append_lt (i^2) X hxsqi
    exact le_trans (le_of_lt this) (pow_le_pow_left (by simp) hi 4)
  have bY' : Y' ≤ (y^2)^4 := by
    have : Y' < i^4 := by simpa [pow_four_eq_sq_sq] using append_lt (i^2) Y hysqi
    exact le_trans (le_of_lt this) (pow_le_pow_left (by simp) hi 4)
  have hseq₀' : Seq₀ X' Y' := hseq₀.append ppi.sq (ppi.sq.four_lt ppi.sq_ne_two (ppi.sq_ne_four ne2))
  have hseqₛ' : Seqₛ (y ^ 2) X' Y' := by
    intro j hj jne2 ppj
    by_cases hjy : j ≤ y
    · have : Seqₛ y X' Y' := hseqₛ.append ppi (by simp [←hYy, ppi.pos])
      exact this j hjy jne2 ppj
    · have : i = j := by
        have : IsPow2 y := by simpa [hYy] using pow2_ext_of_seq₀_of_seqₛ hseq₀ hseqₛ ne2 hi ppi
        exact IsPPow2.sq_uniq this ppi ppj
          ⟨by simp [←hYy, ppi.pos], hi⟩ ⟨by simpa using hjy, hj⟩
      rcases this with rfl
      left; simp [Seqₛ.Even]
      rw [ext_append_last, ext_append_last, ext_append_of_lt , ext_append_of_lt] <;>
        simp [ppi, ppi.sq, hxsqi, hysqi, hiisq, hXx, hYy]
  have hseqₘ' : Seqₘ (2 * x) (y ^ 2) X' Y' :=
    ⟨i ^ 2, sq_le_sq_iff.mp hi, ppi.sq_ne_two, ppi.sq,
     by simp; rw [ext_append_last, ext_append_last] <;> try simp [hxsqi, hysqi]⟩
  exact Or.inr <| ⟨X', bX', Y', bY', hseq₀', hseqₛ', hseqₘ'⟩

lemma exp_even {x y : M} : Exp (2 * x) y ↔ ∃ y', y = y'^2 ∧ Exp x y' :=
  ⟨exp_exists_sq_of_exp_even, by rintro ⟨y, rfl, h⟩; exact bit_zero h⟩

lemma exp_even_sq {x y : M} : Exp (2 * x) (y ^ 2) ↔ Exp x y :=
  ⟨by intro h
      rcases exp_exists_sq_of_exp_even h with ⟨y', e, h⟩
      simpa [show y = y' from by simpa using e] using h,
   bit_zero⟩

lemma exp_exists_sq_of_exp_odd {x y : M} : Exp (2 * x + 1) y → ∃ y', y = 2 * y'^2 ∧ Exp x y' := by
  rintro (⟨hx, rfl⟩ | ⟨X, _, Y, _, hseq₀, hseqₛ, i, hi, ne2, ppi, hXx, hYy⟩)
  · simp at hx
  by_cases ne4 : i = 4
  · rcases ne4 with rfl
    have ex : x = 0 := by simpa [hseq₀.1] using hXx
    have ey : y = 2 := by simpa [hseq₀.2] using Eq.symm hYy
    exact ⟨1, by simp [ex, ey]⟩
  have : Seqₛ.Even X Y (√i) ∨ Seqₛ.Odd X Y (√i) :=
    hseqₛ (√i) (sqrt_le_of_le_sq hi) (ppi.sqrt_ne_two ne2 ne4) (ppi.sqrt ne2)
  rcases this with (⟨hXi, _⟩ | ⟨hXi, hYi⟩)
  · have hXx : 2 * x + 1 = 2 * ext (√i) X := by simpa [ppi.sq_sqrt_eq ne2, hXx] using hXi
    have : 2 ∣ 2 * x + 1 := by rw [hXx]; simp
    have : ¬2 ∣ 2 * x + 1 := by simp [←remainder_eq_zero_iff_dvd, one_lt_two]
    contradiction
  · have hXx : x = ext (√i) X := by simpa [ppi.sq_sqrt_eq ne2, hXx] using hXi
    have hYy : y = 2 * (ext (√i) Y)^2 := by simpa [ppi.sq_sqrt_eq ne2, hYy] using hYi
    let X' := X mod i
    let Y' := Y mod i
    have bsqi : √i ≤ (ext (√i) Y)^2 := le_sq_ext_of_seq₀_of_seqₛ hseq₀ hseqₛ (ppi.sqrt_ne_two ne2 ne4) (le_trans (by simp) hi) (ppi.sqrt ne2)
    have bi : i ≤ ext (√i) Y^4 := by simpa [pow_four_eq_sq_sq, ppi.sq_sqrt_eq ne2] using sq_le_sq_iff.mp bsqi
    have bX' : X' ≤ (ext (√i) Y)^4 := le_trans (le_of_lt $ by simp [ppi.pos]) bi
    have bY' : Y' ≤ (ext (√i) Y)^4 := le_trans (le_of_lt $ by simp [ppi.pos]) bi
    have hseqₛ' : Seqₛ (ext (√i) Y) X' Y' :=
      hseqₛ.rem ppi (sq_lt_of_lt_sqrt $ ext_lt Y (ppi.sqrt ne2).pos) (le_trans (le_sq _)
        (by simp [hYy]))
    have hseqₘ' : Seqₘ x (ext (√i) Y) X' Y' :=
      ⟨√i, bsqi, ppi.sqrt_ne_two ne2 ne4, ppi.sqrt ne2,
       by have : √i < i := sqrt_lt_self_of_one_lt ppi.one_lt
          simp [this, ext_rem, ppi, ppi.sqrt ne2, hXx]⟩
    have : Exp x (ext (√i) Y) :=
      Or.inr ⟨X', bX', Y', bY', hseq₀.rem ppi (ppi.four_lt ne2 ne4), hseqₛ', hseqₘ'⟩
    exact ⟨ext (√i) Y, hYy, this⟩

lemma bit_one {x y : M} : Exp x y → Exp (2 * x + 1) (2 * y ^ 2) := by
  rintro (⟨hx, rfl⟩ | ⟨X, _, Y, _, hseq₀, hseqₛ, i, hi, ne2, ppi, hXx, hYy⟩)
  · rcases hx with rfl; simp
  have hxsqi : 2 * x + 1 < i ^ 2 := calc
    2 * x + 1 < 2 * i + 1 := by simp [←hXx, ppi.pos]
    _         ≤ i ^ 2     := lt_iff_succ_le.mp (two_mul_lt_sq $ ppi.two_lt ne2)
  have hysqi : 2 * y ^ 2 < i ^ 2 := by
    have : 2 * ext i Y ≤ i := two_mul_ext_le_of_seq₀_of_seqₛ hseq₀ hseqₛ ne2 hi ppi
    suffices : 2 * (2 * y ^ 2) < 2 * i ^ 2
    · exact lt_of_mul_lt_mul_left this
    calc
      2 * (2 * y ^ 2) = (2 * y)^2 := by simp [sq, mul_assoc, mul_left_comm y 2]
      _               ≤ i^2       := sq_le_sq_iff.mp (by simpa [hYy] using this)
      _               < 2 * i^2   := lt_mul_of_one_lt_left ppi.sq.pos one_lt_two
  have hiisq : i < i^2 := lt_square_of_lt ppi.one_lt
  let X' := append (i^2) X (2 * x + 1)
  let Y' := append (i^2) Y (2 * (y^2))
  have bX' : X' ≤ (2 * y ^ 2)^4 := by
    have : X' < i^4 := by simpa [pow_four_eq_sq_sq] using append_lt (i^2) X hxsqi
    exact le_trans (le_of_lt this) (pow_le_pow_left (by simp) (le_trans hi $ by simp) 4)
  have bY' : Y' ≤ (2 * y ^ 2)^4 := by
    have : Y' < i^4 := by simpa [pow_four_eq_sq_sq] using append_lt (i^2) Y hysqi
    exact le_trans (le_of_lt this) (pow_le_pow_left (by simp) (le_trans hi $ by simp) 4)
  have hseq₀' : Seq₀ X' Y' := hseq₀.append ppi.sq (ppi.sq.four_lt ppi.sq_ne_two (ppi.sq_ne_four ne2))
  have hseqₛ' : Seqₛ (2 * y ^ 2) X' Y' := by
    intro j hj jne2 ppj
    by_cases hjy : j ≤ y
    · have : Seqₛ y X' Y' := hseqₛ.append ppi (by simp [←hYy, ppi.pos])
      exact this j hjy jne2 ppj
    · have : i = j := by
        have : IsPow2 y := by simpa [hYy] using pow2_ext_of_seq₀_of_seqₛ hseq₀ hseqₛ ne2 hi ppi
        exact IsPPow2.two_mul_sq_uniq this ppi ppj
          ⟨by simp [←hYy, ppi.pos], le_trans hi (by simp)⟩ ⟨by simpa using hjy, hj⟩
      rcases this with rfl
      right; simp [Seqₛ.Odd]
      rw [ext_append_last, ext_append_last, ext_append_of_lt , ext_append_of_lt] <;>
        simp [ppi, ppi.sq, hxsqi, hysqi, hiisq, hXx, hYy]
  have hseqₘ' : Seqₘ (2 * x + 1) (2 * y ^ 2) X' Y' :=
    ⟨i ^ 2, sq_le_sq_iff.mp (le_trans hi $ by simp), ppi.sq_ne_two, ppi.sq,
     by simp; rw [ext_append_last, ext_append_last] <;> try simp [hxsqi, hysqi]⟩
  exact Or.inr <| ⟨X', bX', Y', bY', hseq₀', hseqₛ', hseqₘ'⟩

lemma exp_odd {x y : M} : Exp (2 * x + 1) y ↔ ∃ y', y = 2 * y' ^ 2 ∧ Exp x y' :=
  ⟨exp_exists_sq_of_exp_odd, by rintro ⟨y, rfl, h⟩; exact bit_one h⟩

lemma exp_odd_two_mul_sq {x y : M} : Exp (2 * x + 1) (2 * y ^ 2) ↔ Exp x y :=
  ⟨by intro h
      rcases exp_exists_sq_of_exp_odd h with ⟨y', e, h⟩
      simpa [show y = y' from by simpa using e] using h,
   bit_one⟩

lemma two_le_ext_of_seq₀_of_seqₛ {y X Y : M} (h₀ : Exp.Seq₀ X Y) (hₛ : Exp.Seqₛ y X Y)
    {i} (ne2 : i ≠ 2) (hi : i ≤ y^2) (ppi : IsPPow2 i) : 2 ≤ ext i Y := by
  refine hierarchy_order_induction₂ M Σ 0 (fun y Y i ↦ i ≠ 2 → i ≤ y^2 → IsPPow2 i → 2 ≤ ext i Y)
    ⟨⟨“#2 ≠ 2 → #2 ≤ #0 * #0 → !ppow2def [#2] → ∃[#0 < #2 + 1] (!extdef [#0, #3, #2] ∧ 2 ≤ #0)”, by simp⟩,
     by intro v
        simp [sq, ppow2_defined.pval, ext_defined.pval]
        apply imp_congr_right; intro _; apply imp_congr_right; intro _; apply imp_congr_right; intro _
        exact ⟨fun h ↦ ⟨ext (v 2) (v 1), by simp [← le_iff_lt_succ, h]⟩,
          by rintro ⟨x, _, rfl, h⟩; exact h⟩⟩ y Y ?_ i ne2 hi ppi
  simp; intro i IH ne2 hi ppi
  by_cases ei : i = 4
  · rcases ei with rfl; simp [h₀.2]
  · have IH : 2 ≤ ext (√i) Y :=
      IH (√i) (sqrt_lt_self_of_one_lt ppi.one_lt) (ppi.sqrt_ne_two ne2 ei) (le_trans (by simp) hi) (ppi.sqrt ne2)
    rcases show Seqₛ.Even X Y (√i) ∨ Seqₛ.Odd X Y (√i) from
      hₛ (√i) (sqrt_le_of_le_sq $ hi) (ppi.sqrt_ne_two ne2 ei) (ppi.sqrt ne2) with (heven | hodd)
    · calc
        2 ≤ ext (√i) Y     := IH
        _ ≤ (ext (√i) Y)^2 := by simp
        _ = ext i Y        := by simpa [ppi.sq_sqrt_eq ne2] using Eq.symm heven.2
    · calc
        2 ≤ ext (√i) Y         := IH
        _ ≤ (ext (√i) Y)^2     := by simp
        _ ≤ 2 * (ext (√i) Y)^2 := by simp
        _ = ext i Y            := by simpa [ppi.sq_sqrt_eq ne2] using Eq.symm hodd.2

lemma ext_le_ext_of_seq₀_of_seqₛ {y X Y : M} (h₀ : Exp.Seq₀ X Y) (hₛ : Exp.Seqₛ y X Y)
    {i} (ne2 : i ≠ 2) (hi : i ≤ y^2) (ppi : IsPPow2 i) : ext i X < ext i Y := by
  refine hierarchy_order_induction₃ M Σ 0 (fun y X Y i ↦ i ≠ 2 → i ≤ y^2 → IsPPow2 i → ext i X < ext i Y)
    ⟨⟨“#3 ≠ 2 → #3 ≤ #0 * #0 → !ppow2def [#3] →
        ∃[#0 < #2 + 1] (!extdef [#0, #4, #2] ∧ ∃[#0 < #4 + 1] (!extdef [#0, #5, #4] ∧ #1 < #0))”, by simp⟩,
     by intro v
        simp [sq, Semiformula.eval_substs, ppow2_defined.pval, ext_defined.pval, ←le_iff_lt_succ]
        apply imp_congr_right; intro _; apply imp_congr_right; intro _; apply imp_congr_right; intro _
        exact ⟨fun h ↦ ⟨ext (v 3) (v 1), by simp, rfl, ext (v 3) (v 2), by simp, rfl, h⟩,
          by rintro ⟨x, _, rfl, _, _, rfl, h⟩; exact h⟩⟩ y X Y ?_ i ne2 hi ppi
  simp; intro i IH ne2 hi ppi
  by_cases ne4 : i = 4
  · rcases ne4 with rfl; simp [h₀.1, h₀.2, one_lt_two]
  · have IH : ext (√i) X < ext (√i) Y :=
    IH (√i) (sqrt_lt_self_of_one_lt ppi.one_lt) (ppi.sqrt_ne_two ne2 ne4) (le_trans (by simp) hi) (ppi.sqrt ne2)
    rcases show Seqₛ.Even X Y (√i) ∨ Seqₛ.Odd X Y (√i) from
      hₛ (√i) (sqrt_le_of_le_sq $ hi) (ppi.sqrt_ne_two ne2 ne4) (ppi.sqrt ne2) with (heven | hodd)
    · calc
        ext i X = 2 * ext (√i) X := by simpa [ppi.sq_sqrt_eq ne2] using heven.1
        _       < 2 * ext (√i) Y := by simpa using IH
        _       ≤ ext (√i) Y^2   := two_mul_le_sq (two_le_ext_of_seq₀_of_seqₛ h₀ hₛ (ppi.sqrt_ne_two ne2 ne4) (le_trans (by simp) hi) (ppi.sqrt ne2))
        _       = ext i Y        := by simpa [ppi.sq_sqrt_eq ne2] using Eq.symm heven.2
    · calc
        ext i X = 2 * ext (√i) X + 1 := by simpa [ppi.sq_sqrt_eq ne2] using hodd.1
        _       < 2 * ext (√i) Y + 1 := by simpa using IH
        _       ≤ 2 * ext (√i) Y^2   := lt_iff_succ_le.mp
          (by simp [sq]; exact lt_mul_self (lt_iff_succ_le.mpr $ by
                simp [one_add_one_eq_two]; exact (two_le_ext_of_seq₀_of_seqₛ h₀ hₛ (ppi.sqrt_ne_two ne2 ne4) (le_trans (by simp) hi) (ppi.sqrt ne2))))
        _       = ext i Y            := by simpa [ppi.sq_sqrt_eq ne2] using Eq.symm hodd.2

lemma range_pos {x y : M} (h : Exp x y) : 0 < y := by
  rcases h with (⟨rfl, rfl⟩ | ⟨X, bX, Y, bY, H₀, Hₛ, ⟨u, hu, ne2, ppu, rfl, rfl⟩⟩)
  · simp
  · have : 2 ≤ ext u Y := two_le_ext_of_seq₀_of_seqₛ H₀ Hₛ ne2 hu ppu
    exact lt_of_lt_of_le (by simp) this

lemma dom_lt_range {x y : M} (h : Exp x y) : x < y := by
  rcases h with (⟨rfl, rfl⟩ | ⟨X, bX, Y, bY, H₀, Hₛ, ⟨u, hu, ne2, ppu, rfl, rfl⟩⟩)
  · simp
  · exact ext_le_ext_of_seq₀_of_seqₛ H₀ Hₛ ne2 hu ppu

lemma not_exp_of_le {x y : M} (h : x ≤ y) : ¬Exp y x := by
  intro hxy; exact not_le.mpr (dom_lt_range hxy) h

protected lemma uniq {x y₁ y₂ : M} : Exp x y₁ → Exp x y₂ → y₁ = y₂ := by
  sorry

protected lemma inj {x₁ x₂ y : M} : Exp x₁ y → Exp x₂ y → x₁ = x₂ := by
  sorry

@[simp] lemma one_not_even (a : M) : 1 ≠ 2 * a := by
  intro h
  have : (2 : M) ∣ 1 := by rw [h]; simp
  have : ¬(2 : M) ∣ 1 := not_dvd_of_lt (by simp) one_lt_two
  contradiction

@[simp] lemma exp_two_four : Exp (2 : M) 4 := by
  simpa [two_pow_two_eq_four] using (show Exp (1 : M) 2 from by simp).bit_zero

lemma exp_succ {x y : M} : Exp (x + 1) y ↔ ∃ z, y = 2 * z ∧ Exp x z := by
  suffices : x < y → (Exp (x + 1) y ↔ ∃ z ≤ y, y = 2 * z ∧ Exp x z)
  · by_cases hxy : x < y
    · simp [this hxy]
      exact ⟨by rintro ⟨z, _, rfl, hz⟩; exact ⟨z, rfl, hz⟩,
             by rintro ⟨z, rfl, hz⟩; exact ⟨z, by simpa using hz⟩⟩
    · simp [not_exp_of_le (show y ≤ x + 1 from le_add_right (by simpa using hxy))]
      rintro z rfl
      exact not_exp_of_le (le_trans le_two_mul_left $  by simpa using hxy)
  · refine hierarchy_order_induction₀ M Σ 0 (fun y ↦ ∀ x < y, (Exp (x + 1) y ↔ ∃ z ≤ y, y = 2 * z ∧ Exp x z))
      ⟨⟨“∀[#0 < #1] (!Exp.def [#0 + 1, #1] ↔ ∃[#0 < #2 + 1] (#2 = 2 * #0 ∧ !Exp.def [#1, #0]))”,
         by simp [Hierarchy.pi_zero_iff_sigma_zero]⟩,
       by intro v
          simp [sq, Semiformula.eval_substs, Exp.defined.pval, ←le_iff_lt_succ]⟩ ?_ y x
    simp; intro y IH x hxy
    rcases even_or_odd x with ⟨x, (rfl | rfl)⟩
    · constructor
      · intro H
        rcases exp_odd.mp H with ⟨y, rfl, H'⟩
        exact ⟨y^2, by simp, rfl, H'.bit_zero⟩
      · rintro ⟨y, hy, rfl, H⟩
        rcases exp_even.mp H with ⟨y, rfl, H'⟩
        exact H'.bit_one
    · constructor
      · intro H
        have : Exp (2 * (x + 1)) y := by simpa [mul_add, add_assoc, one_add_one_eq_two] using H
        rcases exp_even.mp this with ⟨y, rfl, H'⟩
        have : 1 < y := by
          simpa using (show 1 < y^2 from lt_of_le_of_lt (by simp) hxy)
        have : Exp (x + 1) y ↔ ∃ z ≤ y, y = 2 * z ∧ Exp x z :=
          IH y (lt_square_of_lt $ this) x (lt_trans _ _ _ (by simp) H'.dom_lt_range)
        rcases this.mp H' with ⟨y, _, rfl, H''⟩
        exact ⟨2 * y ^ 2, by simp [sq, mul_assoc, mul_left_comm y 2],
          by simp [sq, mul_assoc, mul_left_comm y 2], H''.bit_one⟩
      · rintro ⟨y, _, rfl, H⟩
        rcases exp_odd.mp H with ⟨y, rfl, H'⟩
        by_cases ne1 : y = 1
        · rcases ne1 with rfl
          rcases (show x = 0 from by simpa using H'.dom_lt_range)
          simp [one_add_one_eq_two, two_mul_two_eq_four]
        have : y < y^2 := lt_square_of_lt $ one_lt_iff_two_le.mpr $ H'.range_pow2.two_le ne1
        have : Exp (x + 1) (2 * y) ↔ ∃ z ≤ 2 * y, 2 * y = 2 * z ∧ Exp x z :=
          IH (2 * y) (by simp; exact lt_of_lt_of_le this le_two_mul_left) x
            (lt_of_lt_of_le H'.dom_lt_range $ by simp)
        have : Exp (x + 1) (2 * y) := this.mpr ⟨y, by simp, rfl, H'⟩
        simpa [sq, mul_add, add_assoc, mul_assoc, one_add_one_eq_two, mul_left_comm y 2] using this.bit_zero

lemma exp_succ_mul_two {x y : M} : Exp (x + 1) (2 * y) ↔ Exp x y :=
  ⟨by intro h; rcases exp_succ.mp h with ⟨y', e, h⟩; simpa [show y = y' from by simpa using e] using h,
   by intro h; exact exp_succ.mpr ⟨y, rfl, h⟩⟩

end Exp

end ISigma₀

end Model

end

end Arith

end LO.FirstOrder
