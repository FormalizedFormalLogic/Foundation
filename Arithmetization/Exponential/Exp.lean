import Arithmetization.Exponential.PPow2
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

lemma ext_rem {i j z : M} (ppi : PPow2 i) (ppj : PPow2 j) (hij : i < j) : ext i (z mod j) = ext i z := by
  have := ediv_add_remainder z j
  have : i^2 ∣ j := ppi.pow2.sq.dvd_of_le ppj.pow2 (PPow2.sq_le_of_lt ppi ppj hij)
  calc
    ext i (z mod j) = ext i (j * (z /ₑ j) + (z mod j)) := by symm; exact ext_add_of_dvd_sq_left ppi.pos (Dvd.dvd.mul_right this (z /ₑ j))
    _               = ext i z                          := by simp [ediv_add_remainder]

def Exp.Seq₀ (X Y : M) : Prop := ext 4 X = 1 ∧ ext 4 Y = 2

def Exp.Seqₛ.Even (X Y u : M) : Prop := ext (u^2) X = 2 * ext u X ∧ ext (u^2) Y = (ext u Y)^2

def Exp.Seqₛ.Odd (X Y u : M) : Prop := ext (u^2) X = 2 * ext u X + 1 ∧ ext (u^2) Y = 2 * (ext u Y)^2

def Exp.Seqₛ (y X Y : M) : Prop := ∀ u ≤ y, u ≠ 2 → PPow2 u → Seqₛ.Even X Y u ∨ Seqₛ.Odd X Y u

def Exp.Seqₘ (x y X Y : M) : Prop := ∃ u ≤ y^2, u ≠ 2 ∧ PPow2 u ∧ ext u X = x ∧ ext u Y = y

def Exp (x y : M) : Prop := (x = 0 ∧ y = 1) ∨ ∃ X ≤ y^4, ∃ Y ≤ y^4, Exp.Seq₀ X Y ∧ Exp.Seqₛ y X Y ∧ Exp.Seqₘ x y X Y

lemma Exp.Seqₛ.iff (y X Y : M) :
  Exp.Seqₛ y X Y ↔
  ∀ u ≤ y, u ≠ 2 → PPow2 u →
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
      (∃ u ≤ y^2, u ≠ 2 ∧ PPow2 u ∧ x = ext u X ∧ y = ext u Y) :=
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

lemma Seq₀.rem {X Y i : M} (h : Seq₀ X Y) (ppi : PPow2 i) (hi : 4 < i) :
    Seq₀ (X mod i) (Y mod i) := by
  rw [Seq₀, ext_rem, ext_rem] <;> try simp [ppi, hi]
  exact h

lemma Seqₛ.rem {y y' X Y i : M} (h : Seqₛ y X Y) (ppi : PPow2 i) (hi : y'^2 < i) (hy : y' ≤ y) :
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

lemma ext_append_of_lt {i j : M} (hi : PPow2 i) (hj : PPow2 j) (hij : i < j) (X z : M) :
    ext i (append j X z) = ext i X := by
  have : i^2 ∣ j := Pow2.dvd_of_le hi.pow2.sq hj.pow2 (PPow2.sq_le_of_lt hi hj hij)
  calc
    ext i (append j X z) = ext i ((X mod j) + z * j)        := rfl
    _                    = ext i (X mod j)                  := ext_add_of_dvd_sq_right hi.pos (Dvd.dvd.mul_left this z)
    _                    = ext i (j * (X /ₑ j) + (X mod j)) := by rw [add_comm]
                                                                  refine Eq.symm <| ext_add_of_dvd_sq_right hi.pos (Dvd.dvd.mul_right this _)
    _                    = ext i X                          := by simp [ediv_add_remainder]

lemma Seq₀.append {X Y i x y : M} (H : Seq₀ X Y) (ppi : PPow2 i) (hi : 4 < i) :
    Seq₀ (append i X x) (append i Y y) := by
  rw [Seq₀, ext_append_of_lt, ext_append_of_lt] <;> try simp [ppi, hi]
  exact H

lemma Seqₛ.append {z x y X Y i : M} (h : Seqₛ z X Y) (ppi : PPow2 i) (hz : z < i) :
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
    {i} (ne2 : i ≠ 2) (hi : i ≤ y^2) (ppi : PPow2 i) : Pow2 (ext i Y) := by
  refine hierarchy_order_induction₂ M Σ 0 (fun y Y i ↦ i ≠ 2 → i ≤ y^2 → PPow2 i → Pow2 (ext i Y))
    ⟨⟨“#2 ≠ 2 → #2 ≤ #0 * #0 → !ppow2def [#2] → ∃[#0 < #2 + 1] (!extdef [#0, #3, #2] ∧ !pow2def [#0])”, by simp⟩,
     by intro v
        simp [sq, Semiformula.eval_substs, pow2_defined.pval, ppow2_defined.pval, ext_defined.pval]
        apply imp_congr_right; intro _; apply imp_congr_right; intro _; apply imp_congr_right; intro _
        exact ⟨fun h ↦ ⟨ext (v 2) (v 1), by simp [← le_iff_lt_succ, h]⟩,
          by rintro ⟨x, _, rfl, h⟩; exact h⟩⟩ y Y ?_ i ne2 hi ppi
  simp; intro i IH ne2 hi ppi
  by_cases ei : i = 4
  · rcases ei with rfl; simp [h₀.2]
  · have ppsq : Pow2 (ext (√i) Y) :=
      IH (√i) (sqrt_lt_self_of_one_lt ppi.one_lt) (ppi.sqrt_ne_two ne2 ei) (le_trans (by simp) hi) (ppi.sqrt ne2)
    rcases show Seqₛ.Even X Y (√i) ∨ Seqₛ.Odd X Y (√i) from
      hₛ (√i) (sqrt_le_of_le_sq $ hi) (ppi.sqrt_ne_two ne2 ei) (ppi.sqrt ne2) with (heven | hodd)
    · have : ext i Y = (ext (√i) Y)^2 := by simpa [ppi.sq_sqrt_eq ne2] using heven.2
      simp [this, ppsq]
    · have : ext i Y = 2*(ext (√i) Y)^2 := by simpa [ppi.sq_sqrt_eq ne2] using hodd.2
      simp [this, ppsq]

lemma range_pow2 {x y : M} (h : Exp x y) : Pow2 y := by
  rcases h with (⟨rfl, rfl⟩ | ⟨X, bX, Y, bY, H₀, Hₛ, ⟨u, hu, ne2, ppu, rfl, rfl⟩⟩)
  · simp
  · exact pow2_ext_of_seq₀_of_seqₛ H₀ Hₛ ne2 hu ppu

lemma le_sq_ext_of_seq₀_of_seqₛ {y X Y : M} (h₀ : Exp.Seq₀ X Y) (hₛ : Exp.Seqₛ y X Y)
    {i} (ne2 : i ≠ 2) (hi : i ≤ y^2) (ppi : PPow2 i) : i ≤ (ext i Y)^2 := by
  refine hierarchy_order_induction₂ M Σ 0 (fun y Y i ↦ i ≠ 2 → i ≤ y^2 → PPow2 i → i ≤ (ext i Y)^2)
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
    {i} (ne2 : i ≠ 2) (hi : i ≤ y^2) (ppi : PPow2 i) : 2 * ext i Y ≤ i := by
  refine hierarchy_order_induction₂ M Σ 0 (fun y Y i ↦ i ≠ 2 → i ≤ y^2 → PPow2 i → 2 * (ext i Y) ≤ i)
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
        have : Pow2 y := by simpa [hYy] using pow2_ext_of_seq₀_of_seqₛ hseq₀ hseqₛ ne2 hi ppi
        exact PPow2.sq_uniq this ppi ppj
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
        have : Pow2 y := by simpa [hYy] using pow2_ext_of_seq₀_of_seqₛ hseq₀ hseqₛ ne2 hi ppi
        exact PPow2.two_mul_sq_uniq this ppi ppj
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
    {i} (ne2 : i ≠ 2) (hi : i ≤ y^2) (ppi : PPow2 i) : 2 ≤ ext i Y := by
  refine hierarchy_order_induction₂ M Σ 0 (fun y Y i ↦ i ≠ 2 → i ≤ y^2 → PPow2 i → 2 ≤ ext i Y)
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
    {i} (ne2 : i ≠ 2) (hi : i ≤ y^2) (ppi : PPow2 i) : ext i X < ext i Y := by
  refine hierarchy_order_induction₃ M Σ 0 (fun y X Y i ↦ i ≠ 2 → i ≤ y^2 → PPow2 i → ext i X < ext i Y)
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

lemma one_le_ext_of_seq₀_of_seqₛ {y X Y : M} (h₀ : Exp.Seq₀ X Y) (hₛ : Exp.Seqₛ y X Y)
    {i} (ne2 : i ≠ 2) (hi : i ≤ y^2) (ppi : PPow2 i) : 1 ≤ ext i X := by
  refine hierarchy_order_induction₂ M Σ 0 (fun y X i ↦ i ≠ 2 → i ≤ y^2 → PPow2 i → 1 ≤ ext i X)
    ⟨⟨“#2 ≠ 2 → #2 ≤ #0 * #0 → !ppow2def [#2] →
        ∃[#0 < #2 + 1] (!extdef [#0, #3, #2] ∧ 1 ≤ #0)”, by simp⟩,
     by intro v
        simp [sq, ppow2_defined.pval, ext_defined.pval, ←le_iff_lt_succ]
        apply imp_congr_right; intro _; apply imp_congr_right; intro _; apply imp_congr_right; intro _
        exact ⟨fun h ↦ ⟨ext (v 2) (v 1), by simp [h]⟩,
          by rintro ⟨_, _, rfl, h⟩; exact h⟩⟩ y X ?_ i ne2 hi ppi
  simp; intro i IH ne2 hi ppi
  by_cases ne4 : i = 4
  · rcases ne4 with rfl; simp [h₀.1, h₀.2, one_lt_two]
  · have IH : 1 ≤ ext (√i) X :=
    IH (√i) (sqrt_lt_self_of_one_lt ppi.one_lt) (ppi.sqrt_ne_two ne2 ne4) (le_trans (by simp) hi) (ppi.sqrt ne2)
    rcases show Seqₛ.Even X Y (√i) ∨ Seqₛ.Odd X Y (√i) from
      hₛ (√i) (sqrt_le_of_le_sq $ hi) (ppi.sqrt_ne_two ne2 ne4) (ppi.sqrt ne2) with (heven | hodd)
    · have : ext i X = 2 * ext (√i) X := by simpa [ppi.sq_sqrt_eq ne2] using heven.1
      exact le_trans IH (by simp [this])
    · have : ext i X = 2 * ext (√i) X + 1 := by simpa [ppi.sq_sqrt_eq ne2] using hodd.1
      simp [this]

lemma zero_uniq {y : M} (h : Exp 0 y) : y = 1 := by
  rcases h with (⟨_, rfl⟩ | ⟨X, _, Y, _, H₀, Hₛ, ⟨u, hu, ne2, ppu, hX, _⟩⟩)
  · rfl
  · have : 1 ≤ ext u X  := one_le_ext_of_seq₀_of_seqₛ H₀ Hₛ ne2 hu ppu
    simp [hX] at this

lemma succ_lt_s {y : M} (h : Exp (x + 1) y) : 2 ≤ y := by
  rcases h with (⟨h, rfl⟩ | ⟨X, _, Y, _, H₀, Hₛ, ⟨u, hu, ne2, ppu, _, hY⟩⟩)
  · simp at h
  · simpa [hY] using two_le_ext_of_seq₀_of_seqₛ H₀ Hₛ ne2 hu ppu

lemma zero_or_succ (a : M) : a = 0 ∨ ∃ a', a = a' + 1 := by
  rcases zero_le a with (rfl | pos)
  · simp
  · right; exact ⟨a ∸ 1, by rw [msub_add_self_of_le]; simp [pos_iff_one_le.mp pos]⟩

protected lemma uniq {x y₁ y₂ : M} : Exp x y₁ → Exp x y₂ → y₁ = y₂ := by
  intro h₁ h₂
  wlog h : y₁ ≤ y₂
  · exact Eq.symm <| this h₂ h₁ (show y₂ ≤ y₁ from le_of_not_ge h)
  refine hierarchy_order_induction₀ M Σ 0 (fun y₂ ↦ ∀ x < y₂, ∀ y₁ ≤ y₂, Exp x y₁ → Exp x y₂ → y₁ = y₂)
    ⟨⟨“∀[#0 < #1] ∀[#0 < #2 + 1] (!Exp.def [#1, #0] → !Exp.def [#1, #2] → #0 = #2)”,
       by simp [Hierarchy.pi_zero_iff_sigma_zero]⟩,
     by intro v; simp [Exp.defined.pval, ←le_iff_lt_succ]⟩
    ?_ y₂ x h₂.dom_lt_range y₁ h h₁ h₂
  simp; intro y₂ H x _ y₁ h h₁ h₂
  rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
  · simp [h₁.zero_uniq, h₂.zero_uniq]
  · rcases exp_succ.mp h₁ with ⟨y₁, rfl, h₁'⟩
    rcases exp_succ.mp h₂ with ⟨y₂, rfl, h₂'⟩
    have : y₁ = y₂ := H y₂ (lt_mul_of_pos_of_one_lt_left h₂'.range_pos one_lt_two)
      x h₂'.dom_lt_range y₁ (by simpa using h) h₁' h₂'
    simp [this]

protected lemma inj {x₁ x₂ y : M} : Exp x₁ y → Exp x₂ y → x₁ = x₂ := by
  intro h₁ h₂
  refine hierarchy_order_induction₀ M Σ 0 (fun y ↦ ∀ x₁ < y, ∀ x₂ < y, Exp x₁ y → Exp x₂ y → x₁ = x₂)
    ⟨⟨“∀[#0 < #1] ∀[#0 < #2] (!Exp.def [#1, #2] → !Exp.def [#0, #2] → #1 = #0)”,
       by simp [Hierarchy.pi_zero_iff_sigma_zero]⟩,
     by intro v
        simp [sq, Semiformula.eval_substs, Exp.defined.pval, ←le_iff_lt_succ]⟩
    ?_ y x₁ h₁.dom_lt_range x₂ h₂.dom_lt_range h₁ h₂
  simp; intro y H x₁ _ x₂ _ h₁ h₂
  rcases zero_or_succ x₁ with (rfl | ⟨x₁, rfl⟩) <;> rcases zero_or_succ x₂ with (rfl | ⟨x₂, rfl⟩)
  · rfl
  · rcases h₁.zero_uniq
    rcases exp_succ.mp h₂ with ⟨z, hz⟩
    simp at hz
  · rcases h₂.zero_uniq
    rcases exp_succ.mp h₁ with ⟨z, hz⟩
    simp at hz
  · rcases exp_succ.mp h₁ with ⟨y, rfl, hy₁⟩
    have hy₂ : Exp x₂ y := exp_succ_mul_two.mp h₂
    have : x₁ = x₂ :=
      H y (lt_mul_of_pos_of_one_lt_left hy₁.range_pos one_lt_two)
        x₁ hy₁.dom_lt_range x₂ hy₂.dom_lt_range hy₁ hy₂
    simp [this]

end Exp

end ISigma₀

section ISigma₁

variable [𝐈𝚺₁.Mod M]

namespace Exp

lemma range_exists (x : M) : ∃ y, Exp x y := by
  refine hierarchy_induction₀ M Σ 1 (fun x ↦ ∃ y, Exp x y)
    ⟨⟨“∃ !Exp.def [#1, #0]”, by simp [Hierarchy.pi_zero_iff_sigma_zero]⟩,
     by intro v; simp [Exp.defined.pval]⟩
    ?_ ?_ x
  · exact ⟨1, by simp⟩
  · simp; intro x y h; exact ⟨2 * y, exp_succ_mul_two.mpr h⟩

lemma range_exists_unique (x : M) : ∃! y, Exp x y := by
  rcases range_exists x with ⟨y, h⟩
  exact ExistsUnique.intro y h (by intro y' h'; exact h'.uniq h)

end Exp

def exponential (a : M) : M := Classical.choose! (Exp.range_exists_unique a)

prefix:max "exp " => exponential

section exponential

lemma exp_exponential (a : M) : Exp a (exp a) := Classical.choose!_spec (Exp.range_exists_unique a)

lemma exponential_graph {a b : M} : a = exp b ↔ Exp b a := Classical.choose!_eq_iff _

def expdef : Σᴬ[0] 2 := ⟨“!Exp.def [#1, #0]”, by simp⟩

lemma exp_defined : Σᴬ[0]-Function₁ (exponential : M → M) expdef := by
  intro v; simp [expdef, exponential_graph, Exp.defined.pval]

lemma exponential_of_exp {a b : M} (h : Exp a b) : exp a = b :=
  Eq.symm <| exponential_graph.mpr h

lemma exponential_inj : Function.Injective (exponential : M → M) := λ a _ H ↦
  (exp_exponential a).inj (exponential_graph.mp H)

@[simp] lemma exp_zero : exp (0 : M) = 1 := exponential_of_exp (by simp)

@[simp] lemma exp_one : exp (1 : M) = 2 := exponential_of_exp (by simp)

lemma exp_succ (a : M) : exp (a + 1) = 2 * exp a :=
  exponential_of_exp <| Exp.exp_succ_mul_two.mpr <| exp_exponential a

lemma exp_even (a : M) : exp (2 * a) = (exp a)^2 :=
  exponential_of_exp <| Exp.exp_even_sq.mpr <| exp_exponential a

@[simp] lemma lt_exp (a : M) : a < exp a := (exp_exponential a).dom_lt_range

@[simp] lemma exp_pos (a : M) : 0 < exp a := (exp_exponential a).range_pos

@[simp] lemma exp_pow2 (a : M) : Pow2 (exp a) := (exp_exponential a).range_pow2

end exponential

def Bit (i a : M) : Prop := LenBit (exp i) a

infix:50 " ∈ᵇ " => Bit

notation:50 a:50 " ∉ᵇ " b:50 => ¬ (a ∈ᵇ b)

def bitdef : Σᴬ[0] 2 := ⟨“∃[#0 < #2 + 1] (!expdef [#0, #1] ∧ !lenbitdef [#0, #2])”, by simp⟩

lemma bit_defined : Σᴬ[0]-Relation (Bit : M → M → Prop) bitdef := by
  intro v; simp [bitdef, lenbit_defined.pval, exp_defined.pval, ←le_iff_lt_succ]
  constructor
  · intro h; exact ⟨exp (v 0), by simp [h.le], rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

namespace Bit

@[simp] lemma not_mem_zero (i : M) : i ∉ᵇ 0 := by simp [Bit]

open Classical in
noncomputable def insert (i a : M) : M := if i ∈ᵇ a then a else a + exp i



end Bit

end ISigma₁

end Model

end

end Arith

end LO.FirstOrder
