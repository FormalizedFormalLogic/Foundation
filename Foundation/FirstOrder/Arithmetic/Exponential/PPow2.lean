module

public import Foundation.FirstOrder.Arithmetic.Exponential.Pow2

@[expose] public section
/-!
# On $\mathrm{PPow2}(x)$

$\mathrm{PPow2}(n)$ is a property that holds iff $n = 2^{2^i}$ for some $i$.
-/

namespace LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]

def SPPow2 (m : V) : Prop := ¬LenBit 1 m ∧ LenBit 2 m ∧ ∀ i ≤ m, Pow2 i → 2 < i → (LenBit i m ↔ (√i)^2 = i ∧ LenBit (√i) m)

def _root_.LO.FirstOrder.Arithmetic.sppow2Def : 𝚺₀.Semisentence 1 :=
  .mkSigma
  “ m. ¬!lenbitDef 1 m ∧ !lenbitDef 2 m ∧
    ∀ i <⁺ m, !pow2Def i → 2 < i → (!lenbitDef i m ↔ ∃ s <⁺ i, !sqrtDef s i ∧ s * s = i ∧ !lenbitDef s m)
  ”

instance sppow2_defined : 𝚺₀-Predicate[V] SPPow2 via sppow2Def := .mk fun v ↦ by
  simp [SPPow2, sppow2Def, sq]

def PPow2 (i : V) : Prop := Pow2 i ∧ ∃ m < 2 * i, SPPow2 m ∧ LenBit i m

def _root_.LO.FirstOrder.Arithmetic.ppow2Def : 𝚺₀.Semisentence 1 :=
  .mkSigma “i. !pow2Def i ∧ ∃ m < 2 * i, !sppow2Def m ∧ !lenbitDef i m”

instance ppow2_defined : 𝚺₀-Predicate (PPow2 : V → Prop) via ppow2Def := .mk fun v ↦ by
  simp [PPow2, ppow2Def]

instance ppow2_definable : 𝚺₀-Predicate (PPow2 : V → Prop) := ppow2_defined.to_definable

namespace SPPow2

variable {m : V}

lemma not_lenbit_one (hm : SPPow2 m) : ¬LenBit 1 m := hm.1

lemma lenbit_two (hm : SPPow2 m) : LenBit 2 m := hm.2.1

lemma lenbit_iff (hm : SPPow2 m) {i : V} (hi : i ≤ m) (pi : Pow2 i) (lt2 : 2 < i) :
    LenBit i m ↔ (√i)^2 = i ∧ LenBit (√i) m := hm.2.2 i hi pi lt2

lemma one_lt (hm : SPPow2 m) {i : V} (hi : LenBit i m) : 1 < i := by
  by_contra A
  rcases (le_one_iff_eq_zero_or_one.mp (show i ≤ 1 from by simpa using A)) with (rfl | rfl)
  · simp at hi
  · exact hm.1 hi

lemma two_lt (hm : SPPow2 m) {i : V} (hi : LenBit i m) (ne2 : i ≠ 2) : 2 < i :=
  lt_of_le_of_ne (one_lt_iff_two_le.mp $ hm.one_lt hi) (Ne.symm ne2)

lemma sqrt (hm : SPPow2 m) {i : V} (hi : LenBit i m) (pi : Pow2 i) (ne2 : i ≠ 2) :
    LenBit (√i) m := ((hm.lenbit_iff hi.le pi (hm.two_lt hi ne2)).mp hi).2

lemma sq_sqrt_eq (hm : SPPow2 m) {i : V} (hi : LenBit i m) (pi : Pow2 i) (ne2 : i ≠ 2) :
    (√i)^2 = i := ((hm.lenbit_iff hi.le pi (hm.two_lt hi ne2)).mp hi).1

lemma of_sqrt (hm : SPPow2 m) {i : V} (pi : Pow2 i) (him : i ≤ m) (hsqi : (√i)^2 = i) (hi : LenBit (√i) m) :
    LenBit i m := by
  by_cases ne1 : i = 1
  · rcases ne1; simpa using hi
  · have ne2 : i ≠ 2 := by
      rintro rfl; simp [sqrt_two] at hsqi
    have : 2 < i := lt_of_le_of_ne
      (one_lt_iff_two_le.mp <| lt_of_le_of_ne (pos_iff_one_le.mp pi.pos) <| Ne.symm ne1) (Ne.symm ne2)
    exact (hm.lenbit_iff him pi this).mpr ⟨hsqi, hi⟩

@[simp] lemma two : SPPow2 (2 : V) :=
  ⟨by simp [LenBit.one], by simp, by
    intro i hi pi
    rcases le_two_iff_eq_zero_or_one_or_two.mp hi with (rfl | rfl | rfl) <;> simp⟩

@[simp] lemma not_zero : ¬SPPow2 (0 : V) := by
  rintro ⟨_, h, _⟩; simp at h

@[simp] lemma not_one : ¬SPPow2 (1 : V) := by
  rintro ⟨_, h, _⟩; simp [LenBit.iff_rem] at h

lemma sq_le_of_lt (hm : SPPow2 m) {i j : V} (pi : Pow2 i) (pj : Pow2 j) (hi : LenBit i m) (hj : LenBit j m) : i < j → i^2 ≤ j := by
  intro hij
  suffices ∀ i < j, Pow2 i → Pow2 j → LenBit i m → LenBit j m → i^2 ≤ j from this i hij pi pj hi hj
  clear i pi hi hij pj hj
  induction j using ISigma0.order_induction
  · definability
  case ind j IH =>
    intro i hij pi pj  hi hj
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
              sq_le_sq.mpr (show √j ≤ √i from by simpa using A)
          exact False.elim ((not_lt.mpr this) (by simpa using hij))
        have : i ≤ √j := by
          simpa [hm.sq_sqrt_eq hi pi ine2] using
            IH (√j) (sqrt_lt_self_of_one_lt (hm.one_lt hj)) (√i) this
              (pi.sqrt (hm.sq_sqrt_eq hi pi ine2)) (pj.sqrt (hm.sq_sqrt_eq hj pj jne2)) (hm.sqrt hi pi ine2) (hm.sqrt hj pj jne2)
        simpa [hm.sq_sqrt_eq hj pj jne2] using sq_le_sq.mpr this

lemma last_uniq (hm : SPPow2 m) {i j : V} (pi : Pow2 i) (pj : Pow2 j) (hi : LenBit i m) (hj : LenBit j m)
    (hsqi : m < i^2) (hsqj : m < j^2) : i = j := by
  by_contra ne
  wlog hij : i < j
  · exact this hm pj pi hj hi hsqj hsqi (Ne.symm ne) (lt_of_le_of_ne (by simpa using hij) (Ne.symm ne))
  have : i^2 ≤ m := le_trans  (hm.sq_le_of_lt pi pj hi hj hij) hj.le
  have ltsqi : 2 < i^2 := lt_of_le_of_ne (one_lt_iff_two_le.mp $ by simpa using hm.one_lt hi) (by simp)
  have : LenBit (i^2) m ↔ LenBit i m := by simpa using hm.lenbit_iff this pi.sq ltsqi
  have : LenBit (i^2) m := this.mpr hi
  have : ¬m < i^2 := by simpa using this.le
  contradiction

end SPPow2

namespace PPow2

lemma pow2 {i : V} (h : PPow2 i) : Pow2 i := h.1

lemma pos {i : V} (ppi : PPow2 i) : 0 < i := ppi.pow2.pos

lemma one_lt {i : V} (ppi : PPow2 i) : 1 < i := by
  rcases ppi with ⟨_, m, _, sppm, lb⟩; exact sppm.one_lt lb

lemma sq_sqrt_eq {i : V} (ppi : PPow2 i) (ne2 : i ≠ 2) : (√i)^2 = i := by
  rcases ppi with ⟨pi, m, _, sppm, lb⟩
  exact ((sppm.lenbit_iff lb.le pi (lt_of_le_of_ne (one_lt_iff_two_le.mp $ sppm.one_lt lb) (Ne.symm ne2))).mp lb).1

lemma sqrt {i : V} (ppi : PPow2 i) (ne2 : i ≠ 2) : PPow2 (√i) := by
  rcases ppi with ⟨pi, m, _, sppm, him⟩
  have : LenBit i m ↔ (√i)^2 = i ∧ LenBit (√i) m :=
    sppm.lenbit_iff him.le pi (lt_of_le_of_ne (one_lt_iff_two_le.mp $ sppm.one_lt him) (Ne.symm ne2))
  rcases this.mp him with ⟨e, H⟩
  have psqi : Pow2 (√i) := Pow2.sq_iff.mp (by simp [e, pi])
  have one_lt_sqi : 1 < √i := one_lt_sq_iff.mp (by simpa [e] using sppm.one_lt him)
  have : SPPow2 (m % (2 * √i)) :=
    ⟨ by simpa [LenBit.mod] using sppm.not_lenbit_one,
      (LenBit.mod_pow2 (by simp) (by simp [psqi]) (by simp [one_lt_sqi])).mpr sppm.lenbit_two,
      by  intro j hj pj lt2
          have hjsi : j < 2 * √i := lt_of_le_of_lt hj <| mod_lt _ <| by simp [psqi.pos]
          have hjm : LenBit j m ↔ (√j) ^ 2 = j ∧ LenBit (√j) m := sppm.lenbit_iff (le_trans hj (by simp)) pj lt2
          have : LenBit j (m % (2 * √i)) ↔ LenBit j m := LenBit.mod_pow2 pj (by simp [psqi]) (by simp [hjsi])
          calc
            LenBit j (m % (2 * √i)) ↔ LenBit j m                                := LenBit.mod_pow2 pj
                                                                                     (by simp [psqi]) (by simp [hjsi])
            _                       ↔ (√j) ^ 2 = j ∧ LenBit (√j) m              := sppm.lenbit_iff (le_trans hj (by simp)) pj lt2
            _                       ↔ (√j) ^ 2 = j ∧ LenBit (√j) (m % (2 * √i)) := and_congr_right
                                                                                   <| fun hsqj ↦ Iff.symm
                                                                                     <| LenBit.mod_pow2 (pj.sqrt hsqj)
                                                                                       (by simp [psqi])
                                                                                       (lt_of_le_of_lt (by simp) hjsi) ⟩
  exact ⟨psqi, m % (2 * √i), mod_lt _ (by simp [psqi.pos]), this, by simp [H]⟩

lemma exists_spp {i : V} (h : PPow2 i) : ∃ m < 2 * i, SPPow2 m ∧ LenBit i m := h.2

protected lemma sq {i : V} (ppi : PPow2 i) : PPow2 (i^2) := by
  rcases ppi.exists_spp with ⟨m, hm, sppm, hi⟩
  have sppm' : SPPow2 (m + i^2) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [LenBit.add_pow2] <;> simp [ppi.pow2, sppm.not_lenbit_one, sppm.one_lt hi]
    · have : i ≠ 1 := by rintro rfl; exact sppm.not_lenbit_one hi
      have : 2 < i^2 := lt_of_le_of_ne (ppi.pow2.sq.two_le <| by simp [this]) (by simp)
      rw [LenBit.add_pow2] <;> simp [ppi.pow2, sppm.lenbit_two, this]
    · intro j hj pj lt2
      have hsqi : i < i^2 := lt_square_of_lt ppi.one_lt
      have hmi : m < i^2 := lt_of_lt_of_le hm <| two_mul_le_sq <| one_lt_iff_two_le.mp <| sppm.one_lt hi
      calc
        LenBit j (m + i^2) ↔ j = i^2 ∨ LenBit j m                   := LenBit.add_pow2_iff_of_lt pj (by simpa using ppi.pow2) hmi
        _                  ↔ (√j) ^ 2 = j ∧ LenBit (√j) (m + i ^ 2) := ⟨?_, ?_⟩
      · rintro (rfl | hj)
        · simp only [sqrt_sq, true_and]; rw [LenBit.add_pow2] <;> simp [hi, ppi.pow2, hsqi]
        · have : (√j)^2 = j := sppm.sq_sqrt_eq hj pj (ne_of_gt lt2)
          rw [LenBit.add_pow2_iff_of_lt] <;> try simp [ppi.pow2, pj.sqrt this, hmi]
          simp [sppm.sqrt hj pj (ne_of_gt lt2), this]
      · rintro ⟨ej, lb⟩
        have hsqj : √j < i^2 := lt_of_mul_lt_mul_left (a := 2) (by calc
          2 * √j ≤ (√j)^2  := two_mul_le_sq
                                  (one_lt_iff_two_le.mp <| one_lt_sq_iff.mp <| by
                                    rw [ej]; exact lt_trans one_lt_two lt2)
          _      ≤ j       := by simp
          _      ≤ m + i^2 := hj
          _      < 2 * i^2 := by simp [two_mul, hmi])
        have hsqj : LenBit (√j) m := (LenBit.add_pow2 (pj.sqrt ej) ppi.pow2.sq hsqj).mp lb
        by_cases hjm : j ≤ m
        · exact Or.inr <| sppm.of_sqrt pj hjm ej hsqj
        · have : i = √j := sppm.last_uniq ppi.pow2 (pj.sqrt ej) hi hsqj hmi (by simpa [ej] using hjm)
          left; simp [this, ej]
  by_cases ne1 : i = 1
  · rcases ne1; simpa using ppi
  have : m < i^2 :=
    lt_of_lt_of_le hm
      (two_mul_le_sq $ one_lt_iff_two_le.mp $ lt_of_le_of_ne (pos_iff_one_le.mp $ ppi.pos) (Ne.symm ne1))
  exact ⟨ppi.pow2.sq, m + i^2,
    by simp [two_mul, this],
    sppm', LenBit.add_self this⟩

@[simp] lemma two : PPow2 (2 : V) := ⟨by simp, 2, by simp⟩

@[simp] lemma not_zero : ¬PPow2 (0 : V) := by intro h; simpa using h.pow2

@[simp] lemma not_one : ¬PPow2 (1 : V) := by
  rintro ⟨_, m, hm, H, _⟩
  have : m ≤ 1 := lt_two_iff_le_one.mp (by simpa using hm)
  rcases le_one_iff_eq_zero_or_one.mp this with (rfl | rfl) <;> simp at H

lemma elim {i : V} : PPow2 i ↔ i = 2 ∨ ∃ b, i = b^2 ∧ PPow2 b := by
  by_cases ei : i = 2
  · rcases ei with rfl; simp
  · simp only [ei, false_or]
    constructor
    · rintro ppi
      exact ⟨√i, Eq.symm <| ppi.sq_sqrt_eq ei, ppi.sqrt ei⟩
    · rintro ⟨j, rfl, ppj⟩
      exact ppj.sq

lemma elim' {i : V} : PPow2 i ↔ i = 2 ∨ 2 < i ∧ ∃ j, i = j^2 ∧ PPow2 j := by
  by_cases ha : 2 < i
  · simp [ha, ←elim]
  · have : i = 0 ∨ i = 1 ∨ i = 2 := by simpa [le_two_iff_eq_zero_or_one_or_two] using ha
    rcases this with (rfl | rfl | rfl) <;> simp

@[simp] lemma four : PPow2 (4 : V) := elim.mpr (Or.inr <| ⟨2, by simp [two_pow_two_eq_four]⟩)

lemma two_le {i : V} (hi : PPow2 i) : 2 ≤ i := by
  simp [←one_add_one_eq_two, ←lt_iff_succ_le, hi.one_lt]

lemma not_three : ¬PPow2 (3 : V) := by
  intro h; simpa [sqrt_three] using h.sqrt (by simp)

lemma two_lt {i : V} (hi : PPow2 i) (ne : i ≠ 2) : 2 < i := by
  by_contra A
  rcases show i = 0 ∨ i = 1 by
    simpa [ne, le_iff_lt_or_eq, lt_two_iff_le_one] using A with (rfl | rfl) <;> simp at hi

lemma four_le {i : V} (hi : PPow2 i) (ne : i ≠ 2) : 4 ≤ i := by
  by_contra A
  have : i ≤ 3 := by simpa [←three_add_one_eq_four, ←le_iff_lt_succ] using A
  rcases le_three_iff_eq_zero_or_one_or_two_or_three.mp this with (rfl | rfl | rfl | rfl) <;> simp at ne hi
  · have : PPow2 (1 : V) := by simpa [sqrt_three] using hi.sqrt (by simp)
    simp at this

lemma four_lt {i : V} (hi : PPow2 i) (ne2 : i ≠ 2) (ne4 : i ≠ 4) : 4 < i :=
  Ne.lt_of_le (Ne.symm ne4) (hi.four_le ne2)

lemma sq_ne_two {i : V} (hi : PPow2 i) : i^2 ≠ 2 := by
  intro e; have : i < 2 := by simpa [←e] using lt_square_of_lt hi.one_lt
  exact not_le.mpr this hi.two_le

lemma sqrt_ne_two {i : V} (hi : PPow2 i) (ne2 : i ≠ 2) (ne4 : i ≠ 4) : √i ≠ 2 := by
  intro e
  have : i = 4 := by simpa [e, two_pow_two_eq_four] using Eq.symm <| hi.sq_sqrt_eq ne2
  contradiction

lemma sq_ne_four {i : V} (hi : PPow2 i) (ne2 : i ≠ 2) : i^2 ≠ 4 := by
  simpa [two_pow_two_eq_four] using ne_of_gt (sq_lt_sq.mpr (hi.two_lt ne2))

lemma sq_le_of_lt {i j : V} (hi : PPow2 i) (hj : PPow2 j) : i < j → i^2 ≤ j := by
  intro hij
  suffices ∀ i < j, PPow2 i → PPow2 j → i^2 ≤ j from this i hij hi hj
  clear hi hij hj
  induction j using ISigma0.order_induction
  · definability
  case ind j IH =>
    intro i hij hi hj
    by_cases ej : j = 2
    · have : 2 ≤ i := by simpa [one_add_one_eq_two] using lt_iff_succ_le.mp hi.one_lt
      exact False.elim ((not_lt.mpr this) (by simpa [ej] using hij))
    · by_cases ei : i = 2
      · rcases ei with rfl
        simpa [sq, two_mul_two_eq_four] using hj.four_le ej
      · have : √i < √j := by
          by_contra A
          have : j ≤ i := by simpa [hi.sq_sqrt_eq ei, hj.sq_sqrt_eq ej] using sq_le_sq.mpr (show √j ≤ √i from by simpa using A)
          exact False.elim ((not_lt.mpr this) (by simpa using hij))
        have : i ≤ √j := by
          simpa [hi.sq_sqrt_eq ei] using
            IH (√j) (sqrt_lt_self_of_one_lt hj.one_lt) (√i) this (hi.sqrt ei) (hj.sqrt ej)
        simpa [hj.sq_sqrt_eq ej] using sq_le_sq.mpr this

lemma sq_uniq {y i j : V} (py : Pow2 y) (ppi : PPow2 i) (ppj : PPow2 j)
    (hi : y < i ∧ i ≤ y^2) (hj : y < j ∧ j ≤ y^2) : i = j := by
  by_contra ne
  wlog hij : i < j
  · exact this py ppj ppi hj hi (Ne.symm ne) (Ne.lt_of_le' ne (by simpa using hij))
  have : y^2 < y^2 := calc
    y^2 < i^2 := sq_lt_sq.mpr hi.1
    _   ≤ j   := sq_le_of_lt ppi ppj hij
    _   ≤ y^2 := hj.2
  simp_all

lemma two_mul_sq_uniq {y i j : V} (py : Pow2 y) (ppi : PPow2 i) (ppj : PPow2 j)
    (hi : y < i ∧ i ≤ 2 * y^2) (hj : y < j ∧ j ≤ 2 * y^2) : i = j := by
  by_contra ne
  wlog hij : i < j
  · exact this py ppj ppi hj hi (Ne.symm ne) (Ne.lt_of_le' ne (by simpa using hij))
  have : i^2 < (2 * y)^2 := calc
    i^2 ≤ j                 := sq_le_of_lt ppi ppj hij
    _   ≤ 2 * y^2           := hj.2
    _   = 2 * (y * y)       := by simp [sq]
    _   < 2 * (2 * (y * y)) := lt_mul_of_pos_of_one_lt_left (by simpa using pos_iff_ne_zero.mp py.pos) (by simp)
    _   = (2 * y)^2         := by simp [sq, mul_assoc, mul_left_comm]
  have : i < 2 * y := sq_lt_sq.mp this
  have : y < y := lt_of_lt_of_le hi.1 ((ppi.pow2.le_iff_lt_two py).mpr this)
  simp_all

end PPow2

end LO.FirstOrder.Arithmetic
