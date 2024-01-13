import Arithmetization.IOpen

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

end IsPow2

def IsPPow2 (x : M) : Prop := sorry

def ppow2def : Σᴬ[0] 1 := sorry

lemma ppow2_defined : Σᴬ[0]-Predicate (IsPPow2 : M → Prop) ppow2def := sorry

namespace IsPPow2

lemma elim {a : M} : IsPPow2 a ↔ a = 2 ∨ ∃ b, a = b^2 ∧ IsPPow2 b := sorry

@[simp] lemma two : IsPPow2 (2 : M) := elim.mpr (Or.inl rfl)

@[simp] lemma not_zero : ¬IsPPow2 (0 : M) := sorry

@[simp] lemma not_one : ¬IsPPow2 (1 : M) := sorry

lemma elim' {i : M} : IsPPow2 i ↔ i = 2 ∨ 2 < i ∧ ∃ j, i = j^2 ∧ IsPPow2 j := by
  by_cases ha : 2 < i <;> simp [ha, ←elim]
  have : i = 0 ∨ i = 1 ∨ i = 2 := by simpa [le_two_iff_eq_zero_or_one_or_two] using ha
  rcases this with (rfl | rfl | rfl) <;> simp

protected lemma sq {i : M} (h : IsPPow2 i) : IsPPow2 (i^2) := elim.mpr (Or.inr <| ⟨i, rfl, h⟩)

lemma pow2 {i : M} (h : IsPPow2 i) : IsPow2 i := by
  refine hierarchy_order_induction₀ M Σ 0 (fun i ↦ IsPPow2 i → IsPow2 i)
    ⟨⟨“!ppow2def → !pow2def”, by simp⟩, by intro v; simp [pow2_defined.pval, ppow2_defined.pval]⟩ ?_ i h
  simp; intro x ih hx
  have : x = 2 ∨ 2 < x ∧ ∃ y, x = y^2 ∧ IsPPow2 y := IsPPow2.elim'.mp hx
  rcases this with (rfl | ⟨hx, y, rfl, hy⟩)
  · exact pow2_two
  · have : y < y^2 := lt_square_of_lt
      (by by_contra A
          have : y = 0 ∨ y = 1 := le_one_iff_eq_zero_or_one.mp (by simpa using A)
          rcases this with (rfl | rfl) <;> simp at hx)
    simpa using ih y this hy

lemma one_lt {i : M} (hi : IsPPow2 i) : 1 < i := by
  rcases elim'.mp hi with (rfl | ⟨ltj, j, rfl, _⟩)
  · exact one_lt_two
  · exact _root_.lt_trans one_lt_two ltj

lemma two_le {i : M} (hi : IsPPow2 i) : 2 ≤ i := by
  simp [←one_add_one_eq_two, ←lt_iff_succ_le, hi.one_lt]

lemma pos {i : M} (hi : IsPPow2 i) : 0 < i := by
  by_contra A; rcases (show i = 0 from by simpa using A) with rfl; simp at hi

lemma sqrt {i : M} (hi : IsPPow2 i) (ne : i ≠ 2) : IsPPow2 (√i) := by
  rcases elim'.mp hi with (_ | ⟨ltj, j, rfl, _⟩)
  · contradiction
  · simpa

lemma sq_sqrt_eq {i : M} (hi : IsPPow2 i) (ne : i ≠ 2) : (√i)^2 = i := by
  rcases elim'.mp hi with (_ | ⟨ltj, j, rfl, _⟩)
  · contradiction
  · simp

lemma two_lt {i : M} (hi : IsPPow2 i) (ne : i ≠ 2) : 2 < i := by
  by_contra A; simp [ne, le_iff_lt_or_eq, lt_two_iff_le_one] at A
  rcases A with (rfl | rfl) <;> simp at hi

lemma four_le {i : M} (hi : IsPPow2 i) (ne : i ≠ 2) : 4 ≤ i := by
  by_contra A
  have : i ≤ 3 := by simpa [←three_add_one_eq_four, ←le_iff_lt_succ] using A
  rcases le_three_iff_eq_zero_or_one_or_two_or_three.mp this with (rfl | rfl | rfl | rfl) <;> simp at ne hi
  · have : IsPPow2 1 := hi.sqrt (by simp)
    simp at this

lemma sq_ne_two {i : M} (hi : IsPPow2 i) : i^2 ≠ 2 := by
  intro e; have : i < 2 := by simpa [←e] using lt_square_of_lt hi.one_lt
  exact not_le.mpr this hi.two_le

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

@[simp] lemma ext_le_add (u z : M) : ext u z ≤ u + z :=
  le_trans (remainder_le_add (z /ₑ u) u) (by simp [add_comm])

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

def Exp.Seq₀ (X Y : M) : Prop := ext 2 X = 0 ∧ ext 2 Y = 1

def Exp.Seqₛ.Even (X Y u : M) : Prop := ext (u^2) X = 2 * ext u X ∧ ext (u^2) Y = (ext u Y)^2

def Exp.Seqₛ.Odd (X Y u : M) : Prop := ext (u^2) X = 2 * ext u X + 1 ∧ ext (u^2) Y = 2 * (ext u Y)^2

def Exp.Seqₛ (y X Y : M) : Prop := ∀ u ≤ y, IsPPow2 u → Seqₛ.Even X Y u ∨ Seqₛ.Odd X Y u

def Exp.Seqₘ (x y X Y : M) : Prop := ∃ u ≤ y^2, u ≠ 2 ∧ IsPPow2 u ∧ ext u X = x ∧ ext u Y = y

def Exp (x y : M) : Prop := (x = 0 ∧ y = 1) ∨ ∃ X ≤ y^4, ∃ Y ≤ y^4, Exp.Seq₀ X Y ∧ Exp.Seqₛ y X Y ∧ Exp.Seqₘ x y X Y

namespace Exp

def seqX₀ : M := 1

def seqY₀ : M := 2

lemma seq₀_zero_two : Seq₀ (seqX₀ : M) (seqY₀ : M) := by simp [seqX₀, seqY₀, Seq₀, ext, one_lt_two]

lemma Seq₀.rem {X Y i : M} (h : Seq₀ X Y) (ppi : IsPPow2 i) (hi : i ≠ 2) :
    Seq₀ (X mod i) (Y mod i) := by
  simpa [Seq₀, ext_rem, ppi, ppi.two_lt hi] using h

lemma Seqₛ.rem {y y' X Y i : M} (h : Seqₛ y X Y) (ppi : IsPPow2 i) (hi : y'^2 < i) (hy : y' ≤ y) :
    Seqₛ y' (X mod i) (Y mod i) := by
  intro j hj ppj
  have : j^2 < i := lt_of_le_of_lt (sq_le_sq_iff.mp hj) hi
  have : j < i := lt_of_le_of_lt (le_trans hj $ by simp) hi
  rcases h j (le_trans hj hy) ppj with (H | H)
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

lemma Seq₀.append {X Y i x y : M} (H : Seq₀ X Y) (ppi : IsPPow2 i) (hi : i ≠ 2) :
    Seq₀ (append i X x) (append i Y y) := by
  simpa [Seq₀, ext_append_of_lt, ppi, ppi.two_lt hi] using H

lemma Seqₛ.append {z x y X Y i : M} (h : Seqₛ z X Y) (ppi : IsPPow2 i) (hz : z < i) :
    Seqₛ z (append (i^2) X x) (append (i^2) Y y) := by
  intro j hj ppj
  have : j < i^2 := lt_of_lt_of_le (lt_of_le_of_lt hj hz) (by simp)
  have : j^2 < i^2 := sq_lt_sq_iff.mp (lt_of_le_of_lt hj hz)
  rcases h j hj ppj with (H | H) <;> simp [Even, Odd]
  · left; rw [ext_append_of_lt, ext_append_of_lt, ext_append_of_lt, ext_append_of_lt] <;> try simp [ppi.sq, ppj.sq, *]
    exact H
  · right; rw [ext_append_of_lt, ext_append_of_lt, ext_append_of_lt, ext_append_of_lt] <;> try simp [ppi.sq, ppj.sq, *]
    exact H

@[simp] lemma exp_zero_one : Exp (0 : M) 1 := Or.inl (by simp)

@[simp] lemma exp_one_two : Exp (0 : M) 1 := Or.inl (by simp)

lemma exp_pow2 {y X Y: M} (h₀ : Exp.Seq₀ X Y) (hₛ : Exp.Seqₛ y X Y)
    {i} (hi : i ≤ y^2) (ppi : IsPPow2 i) : IsPow2 (ext i Y) := by
  refine hierarchy_order_induction₂ M Σ 0 (fun y Y i ↦ i ≤ y^2 → IsPPow2 i → IsPow2 (ext i Y))
    ⟨⟨“#2 ≤ #0 * #0 → !ppow2def [#2] → ∃[#0 < #3 + #2 + 1] (!extdef [#0, #3, #2] ∧ !pow2def [#0])”, by simp⟩,
     by intro v
        simp [sq, Semiformula.eval_substs, pow2_defined.pval, ppow2_defined.pval, ext_defined.pval]
        apply imp_congr_right; intro _; apply imp_congr_right; intro _
        exact ⟨fun h ↦ ⟨ext (v 2) (v 1), by simp [← le_iff_lt_succ, h]⟩,
          by rintro ⟨x, _, rfl, h⟩; exact h⟩⟩ y Y ?_ i hi ppi
  simp; intro i IH hi ppi
  by_cases ei : i = 2
  · rcases ei with rfl; simp [h₀.2]
  · have ppsq : IsPow2 (ext (√i) Y) := IH (√i) (sqrt_lt_self_of_one_lt ppi.one_lt) (le_trans (by simp) hi) (ppi.sqrt ei)
    rcases show Seqₛ.Even X Y (√i) ∨ Seqₛ.Odd X Y (√i) from hₛ (√i) (sqrt_le_of_le_sq $ hi) (ppi.sqrt ei) with (heven | hodd)
    · have : ext i Y = (ext (√i) Y)^2 := by simpa [ppi.sq_sqrt_eq ei] using heven.2
      simp [this, ppsq]
    · have : ext i Y = 2*(ext (√i) Y)^2 := by simpa [ppi.sq_sqrt_eq ei] using hodd.2
      simp [this, ppsq]

lemma pow_three (x : M) : x^3 = x * x * x := by simp [← two_add_one_eq_three, pow_add, sq]

lemma pow_four (x : M) : x^4 = x * x * x * x := by simp [← three_add_one_eq_four, pow_add, pow_three]

lemma pow_four_eq_sq_sq (x : M) : x^4 = (x^2)^2 := by simp [pow_four, sq, mul_assoc]

lemma exp_exists_sq_of_exp_even {x y : M} : Exp (2 * x) y → ∃ y', y = y'^2 ∧ Exp x y' := by
  rintro (⟨hx, rfl⟩ | ⟨X, _, Y, _, hseq₀, hseqₛ, i, hi, ne, ppi, hXx, hYy⟩)
  · exact ⟨1, by simp [show x = 0 from by simpa using hx]⟩
  have : Seqₛ.Even X Y (√i) ∨ Seqₛ.Odd X Y (√i) := hseqₛ (√i) (sqrt_le_of_le_sq hi) (ppi.sqrt ne)
  rcases this with (⟨hsquX, hsquY⟩ | ⟨hsquX, _⟩)
  · have hXx : x = ext (√i) X := by simpa [ppi.sq_sqrt_eq ne, hXx] using hsquX
    have hYy : y = (ext (√i) Y)^2 := by simpa [ppi.sq_sqrt_eq ne, hYy] using hsquY
    by_cases hsqi : √i = 2
    · have ex : x = 0 := by simpa [hsqi, hseq₀.1] using hXx
      have ey : y = 1 := by simpa [hsqi, hseq₀.2] using hYy
      exact ⟨1, by simp [ex, ey]⟩
    let X' := X mod i
    let Y' := Y mod i
    have bX' : X' ≤ (ext (√i) Y)^4 := by simp [pow_four_eq_sq_sq, ←hYy]; exact le_trans (le_of_lt $ by simp [ppi.pos]) hi
    have bY' : Y' ≤ (ext (√i) Y)^4 := by simp [pow_four_eq_sq_sq, ←hYy]; exact le_trans (le_of_lt $ by simp [ppi.pos]) hi
    have hseqₛ' : Seqₛ (ext (√i) Y) X' Y' :=
      hseqₛ.rem ppi (sq_lt_of_lt_sqrt $ ext_lt Y (ppi.sqrt ne).pos) (by simp [hYy])
    have hseqₘ' : Seqₘ x (ext (√i) Y) X' Y' :=
      ⟨√i, sqrt_le_of_le_sq $ by simp [←hYy, hi], hsqi, ppi.sqrt ne,
       by have : √i < i := sqrt_lt_self_of_one_lt ppi.one_lt
          simp [this, ext_rem, ppi, ppi.sqrt ne, hXx]⟩
    have : Exp x (ext (√i) Y) :=
      Or.inr ⟨X', bX', Y', bY', hseq₀.rem ppi ne, hseqₛ', hseqₘ'⟩
    exact ⟨ext (√i) Y, hYy, this⟩
  · have : 2 ∣ ext i X := by simp [hXx]
    have : ¬2 ∣ ext i X := by
      simp [show ext i X = 2 * ext (√i) X + 1 from by simpa [ppi.sq_sqrt_eq ne] using hsquX,
        ←remainder_eq_zero_iff_dvd, one_lt_two]
    contradiction

lemma two_mul_le_sq {i : M} (h : 2 ≤ i) : 2 * i ≤ i ^ 2 := by simp [sq]; exact mul_le_mul_right h

lemma exp_even_sq_of_exp {x y : M} : Exp x y → Exp (2 * x) (y ^ 2) := by
  rintro (⟨hx, rfl⟩ | ⟨X, _, Y, _, hseq₀, hseqₛ, i, hi, ne, ppi, hXx, hYy⟩)
  · rcases hx with rfl; simp
  have hxisq : 2 * x < i ^ 2 := lt_of_lt_of_le (by simp [←hXx, ppi.pos]) (two_mul_le_sq ppi.two_le)
  have hyisq : y ^ 2 < i ^ 2 := sq_lt_sq_iff.mp $ by simp [←hYy, ppi.pos]
  have hiisq : i < i^2 := lt_square_of_lt ppi.one_lt
  let X' := append (i^2) X (2 * x)
  let Y' := append (i^2) Y (y ^ 2)
  have bX' : X' ≤ (y^2)^4 := by
    have : X' < i^4 := by simpa [pow_four_eq_sq_sq] using append_lt (i^2) X hxisq
    exact le_trans (le_of_lt this) (pow_le_pow_left (by simp) hi 4)
  have bY' : Y' ≤ (y^2)^4 := by
    have : Y' < i^4 := by simpa [pow_four_eq_sq_sq] using append_lt (i^2) Y hyisq
    exact le_trans (le_of_lt this) (pow_le_pow_left (by simp) hi 4)
  have hseq₀' : Seq₀ X' Y' := hseq₀.append ppi.sq (ne_of_gt $ lt_of_lt_of_le (ppi.two_lt ne) (by simp))
  have hseqₛ' : Seqₛ (y ^ 2) X' Y' := by
    intro j hj ppj
    by_cases hjy : j ≤ y
    · have : Seqₛ y X' Y' := hseqₛ.append ppi (by simp [←hYy, ppi.pos])
      exact this j hjy ppj
    · have : i = j := by
        have : IsPow2 y := by simpa [←hYy] using exp_pow2 hseq₀ hseqₛ hi ppi
        exact IsPPow2.sq_uniq this ppi ppj
          ⟨by simp [←hYy, ppi.pos], hi⟩ ⟨by simpa using hjy, hj⟩
      rcases this with rfl
      left; simp [Seqₛ.Even]
      rw [ext_append_last, ext_append_last, ext_append_of_lt , ext_append_of_lt] <;>
        simp [ppi, ppi.sq, hxisq, hyisq, hiisq, hXx, hYy]
  have hseqₘ' : Seqₘ (2 * x) (y ^ 2) X' Y' :=
    ⟨i ^ 2, sq_le_sq_iff.mp hi, ppi.sq_ne_two, ppi.sq,
     by simp; rw [ext_append_last, ext_append_last] <;> try simp [hxisq, hyisq]⟩
  exact Or.inr <| ⟨X', bX', Y', bY', hseq₀', hseqₛ', hseqₘ'⟩

lemma exp_even {x y : M} : Exp (2 * x) y ↔ ∃ y', y = y'^2 ∧ Exp x y' :=
  ⟨exp_exists_sq_of_exp_even, by rintro ⟨y, rfl, h⟩; exact exp_even_sq_of_exp h⟩

/-
lemma exp_exists_sq_of_exp_odd {x y : M} : Exp (2 * x + 1) y → ∃ y', y = 2 * y'^2 ∧ Exp x y' := by
  rintro (⟨hx, rfl⟩ | ⟨X, _, Y, _, hseq₀, hseqₛ, i, hi, ne, ppi, hXx, hYy⟩)
  · simp at hx
  have : Seqₛ.Even X Y (√i) ∨ Seqₛ.Odd X Y (√i) := hseqₛ (√i) (sqrt_le_of_le_sq hi) (ppi.sqrt ne)
  rcases this with (⟨hsquX, hsquY⟩ | ⟨hsquX, hsquY⟩)
  · sorry
  · have hXx : x = ext (√i) X := by simpa [ppi.sq_sqrt_eq ne, hXx] using hsquX
    have hYy : y = 2 * (ext (√i) Y)^2 := by simpa [ppi.sq_sqrt_eq ne, hYy] using hsquY
    by_cases hsqi : √i = 2
    let X' := X mod i
    let Y' := Y mod i
    have bX' : X' ≤ (ext (√i) Y)^4 := by
      simp [pow_four_eq_sq_sq, ←hYy]
      exact le_trans (le_of_lt $ remainder_lt _ ppi.pos) (by {  })
    have bY' : Y' ≤ (ext (√i) Y)^4 := by simp [pow_four_eq_sq_sq, ←hYy]; exact le_trans (le_of_lt $ by simp [ppi.pos]) hi
    have hseqₛ' : Seqₛ (ext (√i) Y) X' Y' :=
      hseqₛ.rem ppi (sq_lt_of_lt_sqrt $ ext_lt Y (ppi.sqrt ne).pos) (le_trans (le_sq _) (by simpa [hYy] using le_mul_of_pos_left (by simp)))
    have hseqₘ' : Seqₘ x (ext (√i) Y) X' Y' :=
      ⟨√i, sqrt_le_of_le_sq $ by simp [←hYy, hi], hsqi, ppi.sqrt ne,
       by have : √i < i := sqrt_lt_self_of_one_lt ppi.one_lt
          simp [this, ext_rem, ppi, ppi.sqrt ne, hXx]⟩
    have : Exp x (ext (√i) Y) :=
      Or.inr ⟨X', bX', Y', bY', hseq₀.rem ppi ne, hseqₛ', hseqₘ'⟩
    exact ⟨ext (√i) Y, hYy, this⟩
-/

end Exp

end ISigma₀

end Model

end

end Arith

end LO.FirstOrder
