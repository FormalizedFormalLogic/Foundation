module

public import Foundation.FirstOrder.Arithmetic.Omega1.Basic

@[expose] public section
namespace LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₀ + 𝝮₁]

namespace Nuon

@[simp] lemma llen_lt_len_smash_len (K : V) : ‖‖K‖‖ < ‖K ⨳ ‖K‖‖ := by
  suffices ‖‖K‖‖ ≤ ‖K‖ * ‖‖K‖‖ by simpa [length_smash, lt_succ_iff_le]
  rcases Arithmetic.zero_le ‖K‖ with (hK | pos)
  · simp [←hK]
  · exact le_mul_of_pos_left pos

lemma mul_len_lt_len_smash {i I L : V} (hi : i ≤ ‖I‖) : i * ‖L‖ < ‖I ⨳ L‖ := by
  simpa [length_smash, lt_succ_iff_le] using _root_.mul_le_mul_left hi ‖L‖

lemma mul_len_lt_len_smash' {i K z : V} (hi : i ≤ ‖z‖) : i * ‖‖K‖‖ < ‖z ⨳ ‖K‖‖ := by
  simpa [length_smash, lt_succ_iff_le] using _root_.mul_le_mul_left hi ‖‖K‖‖

noncomputable def ext (L S i : V) : V := S / bexp S (i * ‖L‖) % (L ⨳ 1)

local notation S "{" L "}[" i "]" => ext L S i

lemma ext_eq_zero_of_lt {L S i : V} (h : ‖S‖ ≤ i * ‖L‖) : S{L}[i] = 0 := by simp [ext, bexp_eq_zero_of_le h]

@[simp] lemma ext_le_self (L S i : V) : S{L}[i] ≤ S := le_trans (mod_le _ _) (by simp)

lemma ext_graph_aux (z S L i : V) : z = S{L}[i] ↔ (‖S‖ ≤ i * ‖L‖ → z = 0) ∧ (i * ‖L‖ < ‖S‖ → ∃ b ≤ S, Exponential (i * ‖L‖) b ∧ z = S / b % (L ⨳ 1)) := by
  rcases show ‖S‖ ≤ i * ‖L‖ ∨ i * ‖L‖ < ‖S‖ from le_or_gt _ _ with (le | lt)
  · simp [ext_eq_zero_of_lt le, le, not_lt.mpr le]
  · suffices z = S / bexp S (i * ‖L‖) % L ⨳ 1 ↔ ∃ b ≤ S, Exponential (i * ‖L‖) b ∧ z = S / b % L ⨳ 1 by
      simpa [lt, not_le.mpr lt, ext]
    have := exp_bexp_of_lt lt
    constructor
    · rintro rfl; exact ⟨bexp S (i * ‖L‖), by simp, exp_bexp_of_lt lt, rfl⟩
    · rintro ⟨b, _, H, rfl⟩
      rcases H.uniq (exp_bexp_of_lt lt); rfl

lemma ext_graph (z S L i : V) : z = S{L}[i] ↔
    ∃ lS ≤ S, lS = ‖S‖ ∧ ∃ lL ≤ L, lL = ‖L‖ ∧
      (lS ≤ i * lL → z = 0) ∧
      (i * lL < lS →
        ∃ b ≤ S, Exponential (i * lL) b ∧ ∃ hL ≤ 2 * L + 1, Exponential lL hL ∧ ∃ divS ≤ S, divS = S / b ∧ z = divS % hL) := by
  rw [ext_graph_aux]
  rcases show ‖S‖ ≤ i * ‖L‖ ∨ i * ‖L‖ < ‖S‖ from le_or_gt _ _ with (le | lt)
  · simp [le, not_lt.mpr le]
  · suffices (∃ b ≤ S, Exponential (i * ‖L‖) b ∧ z = S / b % L ⨳ 1)
      ↔ ∃ b ≤ S, Exponential (i * ‖L‖) b ∧ ∃ hL ≤ 2 * L + 1, Exponential ‖L‖ hL ∧ z = S / b % hL
    by simpa [lt, not_le.mpr lt]
    constructor
    · rintro ⟨b, hb, Hb, rfl⟩;
      refine ⟨b, hb, Hb, L ⨳ 1, by simp, exponential_smash_one L, rfl⟩
    · rintro ⟨b, hb, Hb, hL, _, HhL, _, _, rfl, rfl⟩
      exact ⟨b, hb, Hb, by rw [HhL.uniq (exponential_smash_one L)]⟩

def extDef : 𝚺₀.Semisentence 4 := .mkSigma
  “z L S i.
    ∃ lS <⁺ S, !lengthDef lS S ∧ ∃ lL <⁺ L, !lengthDef lL L ∧
      (lS ≤ i * lL → z = 0) ∧
      (i * lL < lS →
        ∃ b <⁺ S, !exponentialDef (i * lL) b ∧
          ∃ hL <⁺ 2 * L + 1, !exponentialDef lL hL ∧
            ∃ divS <⁺ S, !divDef divS S b ∧ !remDef z divS hL)”
  (by simp)

@[simp] lemma cons_app_seven {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ.succ → α) : (a :> s) 7 = s 6 := rfl

@[simp] lemma cons_app_eight {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ.succ.succ → α) : (a :> s) 8 = s 7 := rfl

@[simp] lemma cons_app_nine {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ.succ.succ.succ → α) : (a :> s) 9 = s 8 := rfl

instance ext_defined : 𝚺₀-Function₃ (ext : V → V → V → V) via extDef := .mk fun v ↦ by simp [extDef, ext_graph, numeral_eq_natCast]

instance ext_Definable : 𝚺₀-Function₃ (ext : V → V → V → V) := ext_defined.to_definable

instance : Bounded₃ (ext : V → V → V → V) := ⟨#1, λ _ ↦ by simp⟩

@[simp] lemma ext_zero (L i : V) : 0{L}[i] = 0 := by simp [ext]

lemma ext_zero_eq_self_of_le {L S : V} (h : ‖S‖ ≤ ‖L‖) : S{L}[0] = S := by
  rcases Arithmetic.zero_le S with (rfl | pos)
  · simp [ext]
  · simp [ext]
    have : bexp S 0 = 1 := (exp_bexp_of_lt (show 0 < ‖S‖ from by simp [pos])).zero_uniq
    simp [this, lt_smash_one_iff.mpr h]

lemma ext_eq_of_ge {L S S' i : V} (h : S ≤ S') : S / bexp S' (i * ‖L‖) % (L ⨳ 1) = S{L}[i] := by
  rcases show i * ‖L‖ < ‖S‖ ∨ ‖S‖ ≤ i * ‖L‖ from lt_or_ge (i * ‖L‖) ‖S‖ with (lt | le)
  · unfold ext; congr 2; exact bexp_eq_of_lt_length (lt_of_lt_of_le lt $ length_monotone h) lt
  · simp only [ext_eq_zero_of_lt le]
    rcases show i * ‖L‖ < ‖S'‖ ∨ ‖S'‖ ≤ i * ‖L‖ from lt_or_ge (i * ‖L‖) ‖S'‖ with (lt' | le')
    · have : S < bexp S' (i * ‖L‖) := ((exp_bexp_of_lt lt').lt_iff_len_le).mpr le
      simp [this]
    · simp [bexp_eq_zero_of_le le']

lemma ext_eq_of_gt {L S S' i : V} (h : i * ‖L‖ < ‖S'‖) : S / bexp S' (i * ‖L‖) % (L ⨳ 1) = S{L}[i] := by
  rcases show i * ‖L‖ < ‖S‖ ∨ ‖S‖ ≤ i * ‖L‖ from lt_or_ge (i * ‖L‖) ‖S‖ with (lt | le)
  · unfold ext; congr 2; exact bexp_eq_of_lt_length h lt
  · simp only [ext_eq_zero_of_lt le]
    have : S < bexp S' (i * ‖L‖) := ((exp_bexp_of_lt h).lt_iff_len_le).mpr le
    simp [this]

lemma ext_eq_smash_of_le {L S i : V} (h : i ≤ ‖I‖) : S / bexp (I ⨳ L) (i * ‖L‖) % (L ⨳ 1) = S{L}[i] :=
  ext_eq_of_gt (mul_len_lt_len_smash h)

lemma ext_add₁_pow2 {L i S₁ S₂ p : V} (pp : Pow2 p) (h : (i + 1) * ‖L‖ < ‖p‖) :
    (S₁ + S₂ * p){L}[i] = S₁{L}[i] := by
  rcases Arithmetic.zero_le S₂ with (rfl | pos₂)
  · simp
  have lt_len : i * ‖L‖ < ‖S₁ + S₂ * p‖ := calc
        i * ‖L‖ ≤ (i + 1) * ‖L‖ := mul_le_mul_right (by simp)
        _       < ‖p‖           := h
        _       ≤ ‖S₁ + S₂ * p‖ := length_monotone (le_add_left (le_mul_of_pos_left pos₂))
  have : Exponential ((i + 1) * ‖L‖) (bexp (S₁ + S₂ * p) (i * ‖L‖) * L ⨳ 1) := by
    simpa [add_mul]
      using Exponential.add_mul (by simp [lt_len]) (by simpa using exponential_smash L 1)
  have : bexp (S₁ + S₂ * p) (i * ‖L‖) * L ⨳ 1 ∣ p :=
    Pow2.dvd_of_le (by simpa using bexp_pow2 lt_len) pp (this.monotone_le (exponential_of_pow2 pp) (le_log_of_lt_length h))
  rcases this with ⟨q, hq⟩
  calc
    (S₁ + S₂ * p){L}[i] = (S₁ + p * S₂) / bexp (S₁ + S₂ * p) (i * ‖L‖) % L ⨳ 1         := by simp [ext, mul_comm S₂]
    _                   = (S₁ + bexp (S₁ + S₂ * p) (i * ‖L‖) * (L ⨳ 1 * q * S₂)) / bexp (S₁ + S₂ * p) (i * ‖L‖) % L ⨳ 1 := by simp [←mul_assoc, ←hq]
    _                   = (S₁ / bexp (S₁ + S₂ * p) (i * ‖L‖) + L ⨳ 1 * q * S₂) % L ⨳ 1 := by rw [div_add_mul_self' _ _ (bexp_pos lt_len)]
    _                   = S₁ / bexp (S₁ + S₂ * p) (i * ‖L‖) % L ⨳ 1                    := by simp [mul_assoc]
    _                   = S₁{L}[i]                                                     := ext_eq_of_ge le_self_add

lemma ext_add₁_bexp {L i j S₁ S₂ : V} (hi : i ≤ ‖I‖) (hij : j < i) :
    (S₁ + S₂ * bexp (I ⨳ L) (i * ‖L‖)){L}[j] = S₁{L}[j] :=
  ext_add₁_pow2 (bexp_pow2 $ mul_len_lt_len_smash hi)
    (by rw [len_bexp (mul_len_lt_len_smash hi), lt_succ_iff_le]; exact mul_le_mul_right (succ_le_iff_lt.mpr hij))

lemma ext_add₂_bexp {I i j S₁ S₂ : V} (hij : i + j ≤ ‖I‖) (hS₁ : ‖S₁‖ ≤ i * ‖L‖) :
    (S₁ + S₂ * bexp (I ⨳ L) (i * ‖L‖)){L}[i + j] = S₂{L}[j] := by
  have hie : Exponential (i * ‖L‖) (bexp (I ⨳ L) (i * ‖L‖)) := exp_bexp_of_lt (mul_len_lt_len_smash $ le_trans le_self_add hij)
  calc  (S₁ + S₂ * bexp (I ⨳ L) (i * ‖L‖)){L}[i + j]
      = (S₁ + S₂ * bexp (I ⨳ L) (i * ‖L‖)) / bexp (I ⨳ L) ((i + j) * ‖L‖) % (L ⨳ 1)                    := by rw [ext_eq_smash_of_le hij]
    _ = (S₁ + S₂ * bexp (I ⨳ L) (i * ‖L‖)) / bexp (I ⨳ L) (i * ‖L‖) / bexp (I ⨳ L) (j * ‖L‖) % (L ⨳ 1) := by
      simp only [add_mul, ← Arithmetic.div_mul]; congr 2; exact bexp_add (by simp [←add_mul, mul_len_lt_len_smash hij])
    _ = S₂ / bexp (I ⨳ L) (j * ‖L‖) % (L ⨳ 1)                                                          := by
      congr 2; rw [div_add_mul_self, div_eq_zero_of_lt] <;> simp [hie.lt_iff_len_le.mpr hS₁, hie.range_pos]
    _ = S₂{L}[j]                                                                                       := ext_eq_smash_of_le (le_trans le_add_self hij)

noncomputable def append (I L S i X : V) : V := S % bexp (I ⨳ L) (i * ‖L‖) + X * bexp (I ⨳ L) (i * ‖L‖)

lemma append_nil (I L S i : V) : append I L S i 0 = S % bexp (I ⨳ L) (i * ‖L‖) := by simp [append]

lemma len_append (I L S : V) {i X} (hi : i ≤ ‖I‖) (hX : 0 < X) : ‖append I L S i X‖ = ‖X‖ + i * ‖L‖ := calc
  ‖append I L S i X‖ = ‖X * bexp (I ⨳ L) (i * ‖L‖) + S % bexp (I ⨳ L) (i * ‖L‖)‖ := by simp [append, add_comm]
  _                  = ‖X‖ + log (bexp (I ⨳ L) (i * ‖L‖))                        := length_mul_pow2_add_of_lt hX
                                                                                      (bexp_pow2 $ mul_len_lt_len_smash hi)
                                                                                      (mod_lt _ $ bexp_pos $ mul_len_lt_len_smash hi)
  _                  = ‖X‖ + i * ‖L‖                                             := by simp [log_bexp (mul_len_lt_len_smash hi)]

lemma append_lt_smash (I L S : V) {i X} (hi : i < ‖I‖) (hX : ‖X‖ ≤ ‖L‖) : append I L S i X < I ⨳ L := by
  rcases Arithmetic.zero_le X with (rfl | pos)
  · simpa [append_nil]
      using lt_of_lt_of_le (mod_lt _ (bexp_pos $ mul_len_lt_len_smash $ le_of_lt hi)) (by simp)
  · suffices ‖X‖ + i * ‖L‖ ≤ ‖I‖ * ‖L‖ by simpa [lt_smash_iff, len_append I L S (le_of_lt hi) pos]
    calc
      ‖X‖ + i * ‖L‖ ≤ (i + 1) * ‖L‖ := by simp [add_mul, add_comm (i * ‖L‖), hX]
      _             ≤ ‖I‖ * ‖L‖     := mul_le_mul_right (succ_le_iff_lt.mpr hi)

lemma append_lt_sq_smash (I L S : V) {i X} (hi : i ≤ ‖I‖) (hX : ‖X‖ ≤ ‖L‖) (Ipos : 0 < I) : append I L S i X < (I ⨳ L)^2 := by
  rcases hi with (rfl | hi)
  · calc
      append I L S ‖I‖ X = S % I ⨳ L + X * I ⨳ L := by simp [append, bexp_eq_smash]
      _                  < (X + 1) * I ⨳ L       := by simp [add_mul, add_comm]
      _                  ≤ L ⨳ 1 * I ⨳ L         := mul_le_mul_right (succ_le_iff_lt.mpr $ lt_smash_one_iff.mpr hX)
      _                  ≤ (I ⨳ L) ^ 2           := by simpa [sq, smash_comm L 1] using smash_monotone (pos_iff_one_le.mp Ipos) (by rfl)
  · exact lt_of_lt_of_le (append_lt_smash I L S hi hX) (by simp)

lemma ext_append_last (I L S : V) {i X} (hi : i ≤ ‖I‖) (hX : ‖X‖ ≤ ‖L‖) : (append I L S i X){L}[i] = X := calc
  (append I L S i X){L}[i] = (S % bexp (I ⨳ L) (i * ‖L‖) + X * bexp (I ⨳ L) (i * ‖L‖)){L}[i + 0] := by simp [append]
  _                        =  X{L}[0]                                                            := ext_add₂_bexp (by simpa using hi)
                                                                                                      ((exp_bexp_of_lt (mul_len_lt_len_smash hi)).lt_iff_len_le.mp
                                                                                                        (mod_lt _ $ bexp_pos $ mul_len_lt_len_smash hi))
  _                        =  X                                                                  := ext_zero_eq_self_of_le hX

lemma ext_append_lt (I L S : V) {i j X} (hi : i ≤ ‖I‖) (hij : j < i) :
    (append I L S i X){L}[j] = S{L}[j] := calc
  (append I L S i X){L}[j] = (S % bexp (I ⨳ L) (i * ‖L‖) + X * bexp (I ⨳ L) (i * ‖L‖)){L}[j] := rfl
  _                        = (S % bexp (I ⨳ L) (i * ‖L‖)){L}[j]                              := ext_add₁_bexp hi hij
  _                        = (S % bexp (I ⨳ L) (i * ‖L‖) + (S / bexp (I ⨳ L) (i * ‖L‖)) * bexp (I ⨳ L) (i * ‖L‖)){L}[j] := Eq.symm <| ext_add₁_bexp hi hij
  _                        = S{L}[j]                                                         := by rw [add_comm, mul_comm, div_add_mod]

section

variable {L A : V}

def IsSegment (L A start intv S : V) : Prop := ∀ i < intv, S{L}[i + 1] = S{L}[i] + fbit A (start + i)

def Segment (U L A start intv nₛ nₑ : V) : Prop := ∃ S < U, IsSegment L A start intv S ∧ S{L}[0] = nₛ ∧ S{L}[intv] = nₑ

def IsSeries (U I L A iter T : V) : Prop := ∀ l < iter, Segment U L A (‖I‖ * l) ‖I‖ (T{L}[l]) (T{L}[l + 1])

def Series (U I L A iter n : V) : Prop := ∃ T < U, IsSeries U I L A iter T ∧ T{L}[0] = 0 ∧ T{L}[iter] = n

def SeriesSegment (U I L A k n : V) : Prop := ∃ nₖ ≤ n, Series U I L A (k / ‖I‖) nₖ ∧ Segment U L A (‖I‖ * (k / ‖I‖)) (k % ‖I‖) nₖ n

lemma SeriesSegment.series {U I L A k n : V} (H : SeriesSegment U I L A k n) :
    ∃ T S, IsSeries U I L A (k / ‖I‖) T ∧ IsSegment L A (‖I‖ * (k / ‖I‖)) (k % ‖I‖) S ∧ T{L}[0] = 0 ∧ T{L}[k / ‖I‖] = S{L}[0] ∧ S{L}[k % ‖I‖] = n := by
  rcases H with ⟨_, _, ⟨T, _, hT, hTₛ, hTₑ⟩, ⟨S, _, hS, rfl, rfl⟩⟩
  exact ⟨T, S, hT, hS, hTₛ, hTₑ, rfl⟩

lemma IsSegment.le_add {L A start intv S : V} (H : IsSegment L A start intv S) : ∀ i ≤ intv, S{L}[i] ≤ S{L}[0] + i := by
  intro i
  induction i using ISigma0.succ_induction
  · definability
  case zero => simp
  case succ i IH =>
    intro h
    have IH : S{L}[i] ≤ S{L}[0] + i := IH (le_trans (by simp) h)
    calc
      S{L}[i + 1] = S{L}[i] + fbit A (start + i) := H i (succ_le_iff_lt.mp h)
      _           ≤ S{L}[i] + 1                  := by simp
      _           ≤ S{L}[0] + (i + 1)            := by simp [←add_assoc, IH]

-- lemma Segment.refl (U L A start n : V) (hU : n < U) (hn : ‖n‖ ≤ ‖L‖) : Segment U L A start 0 n n :=
--   ⟨n, hU, by intro; simp, ext_zero_eq_self_of_le hn, ext_zero_eq_self_of_le hn⟩

lemma Segment.refl (U L A start n : V) (hL : L ⨳ 1 ≤ U) (hn : ‖n‖ ≤ ‖L‖) : Segment U L A start 0 n n :=
  ⟨n, lt_of_lt_of_le (lt_smash_one_iff.mpr hn) hL, by intro; simp, ext_zero_eq_self_of_le hn, ext_zero_eq_self_of_le hn⟩

lemma Segment.le_add {U L A start intv nₛ nₑ : V} (H : Segment U L A start intv nₛ nₑ) : nₑ ≤ nₛ + intv := by
  rcases H with ⟨S, _, hS, rfl, rfl⟩; exact hS.le_add intv (by rfl)

lemma Segment.uniq {U L A start intv nₛ nₑ₁ nₑ₂ : V}
    (H₁ : Segment U L A start intv nₛ nₑ₁) (H₂ : Segment U L A start intv nₛ nₑ₂) : nₑ₁ = nₑ₂ := by
  rcases H₁ with ⟨S₁, _, HS₁, Hₛ, rfl⟩
  rcases H₂ with ⟨S₂, _, HS₂, rfl, rfl⟩
  suffices ∀ i ≤ intv, S₁{L}[i] = S₂{L}[i] from this intv (by rfl)
  intro i; induction i using ISigma0.succ_induction
  · definability
  case zero => intro _; exact Hₛ
  case succ i IH =>
    intro hi
    have h₁ : S₁{L}[i + 1] = S₁{L}[i] + fbit A (start + i) := HS₁ i (lt_iff_succ_le.mpr hi)
    have h₂ : S₂{L}[i + 1] = S₂{L}[i] + fbit A (start + i) := HS₂ i (lt_iff_succ_le.mpr hi)
    simp [IH (le_trans (by simp) hi), h₁, h₂]

lemma IsSeries.le_add {U I L A iter T : V} (H : IsSeries U I L A iter T) : ∀ l ≤ iter, T{L}[l] ≤ T{L}[0] + ‖I‖ * l := by
  intro l
  induction l using ISigma0.succ_induction
  · definability
  case zero => simp
  case succ l IH =>
    intro h
    have IH : T{L}[l] ≤ T{L}[0] + ‖I‖ * l := IH (le_trans (by simp) h)
    calc
      T{L}[l + 1] ≤ T{L}[l] + ‖I‖           := (H l (succ_le_iff_lt.mp h)).le_add
      _           ≤ T{L}[0] + ‖I‖ * (l + 1) := by simpa [mul_add, ←add_assoc] using IH

lemma Series.le_add {U I L A iter n : V} (H : Series U I L A iter n) : n ≤ ‖I‖ * iter := by
  rcases H with ⟨T, _, hT, hzero, rfl⟩; simpa [hzero] using hT.le_add iter (by rfl)

lemma Series.uniq {U I L A iter n₁ n₂ : V} (H₁ : Series U I L A iter n₁) (H₂ : Series U I L A iter n₂) : n₁ = n₂ := by
  rcases H₁ with ⟨T₁, _, HT₁, Hₛ₁, rfl⟩
  rcases H₂ with ⟨T₂, _, HT₂, Hₛ₂, rfl⟩
  suffices ∀ i ≤ iter, T₁{L}[i] = T₂{L}[i] from this iter (by rfl)
  intro i; induction i using ISigma0.succ_induction
  · definability
  case zero => intro _; simp [Hₛ₁, Hₛ₂]
  case succ i IH =>
    intro hi
    have IH : T₁{L}[i] = T₂{L}[i] := IH (le_trans (by simp) hi)
    have h₁ : Segment U L A (‖I‖ * i) ‖I‖ (T₁{L}[i]) (T₁{L}[i + 1]) := HT₁ i (lt_iff_succ_le.mpr hi)
    have h₂ : Segment U L A (‖I‖ * i) ‖I‖ (T₁{L}[i]) (T₂{L}[i + 1]) := by simpa [IH] using HT₂ i (lt_iff_succ_le.mpr hi)
    exact h₁.uniq h₂

lemma SeriesSegment.le {U I L A k n : V} (H : SeriesSegment U I L A k n) :
    n ≤ k := by
  rcases H with ⟨nₖ, _, hT, hS⟩
  calc
    n ≤ nₖ + k % ‖I‖              := hS.le_add
    _ ≤ ‖I‖ * (k / ‖I‖) + k % ‖I‖ := by simpa [mul_comm] using hT.le_add
    _ = k                         := div_add_mod k ‖I‖

lemma SeriesSegment.initial {U I L A : V} (Upos : 0 < U) : SeriesSegment U I L A 0 0 :=
  ⟨0, by rfl, ⟨0, Upos, by simp [IsSeries]⟩, ⟨0, Upos, by simp [IsSegment]⟩⟩

lemma SeriesSegment.zero {U I L k : V} (Upos : 0 < U) : SeriesSegment U I L 0 k 0 :=
  ⟨0, by rfl, ⟨0, Upos, fun _ _ ↦ ⟨0, Upos, fun _ _ ↦ by simp, by simp⟩, by simp⟩, ⟨0, Upos, fun _ _ ↦ by simp, by simp⟩⟩

lemma SeriesSegment.uniq {U I L A k n₁ n₂ : V} (H₁ : SeriesSegment U I L A k n₁) (H₂ : SeriesSegment U I L A k n₂) :
    n₁ = n₂ := by
  rcases H₁ with ⟨nₘ₁, _, hT₁, hS₁⟩
  rcases H₂ with ⟨nₘ₂, _, hT₂, hS₂⟩
  rcases show nₘ₁ = nₘ₂ from hT₁.uniq hT₂
  exact hS₁.uniq hS₂

variable {U I L A : V}

lemma Segment.succ (hU : (I ⨳ L)^2 ≤ U) {start intv nₛ nₑ : V} (H : Segment U L A start intv nₛ nₑ) (hintv : intv < ‖I‖) (hnₛ : ‖nₛ + ‖I‖‖ ≤ ‖L‖) :
    Segment U L A start (intv + 1) nₛ (nₑ + fbit A (start + intv)) := by
  rcases H with ⟨S, _, H, rfl, rfl⟩
  let S' := append I L S (intv + 1) (S{L}[intv] + fbit A (start + intv))
  have le_len_L : ‖S{L}[intv] + fbit A (start + intv)‖ ≤ ‖L‖ := calc
    ‖S{L}[intv] + fbit A (start + intv)‖ ≤ ‖S{L}[intv] + 1‖     := length_monotone <| by simp
    _                                    ≤ ‖S{L}[0] + intv + 1‖ := length_monotone <| by simpa using H.le_add intv (by rfl)
    _                                    ≤ ‖S{L}[0] + ‖I‖‖      := length_monotone <| by simp [add_assoc, succ_le_iff_lt, hintv]
    _                                    ≤ ‖L‖                  := hnₛ
  have H' : IsSegment L A start (intv + 1) S' := by
    intro i hi
    rcases show i ≤ intv from lt_succ_iff_le.mp hi with (rfl | hi)
    · calc
        S'{L}[i + 1] = S{L}[i] + fbit A (start + i)  := ext_append_last I L S (succ_le_iff_lt.mpr hintv) le_len_L
        _            = S'{L}[i] + fbit A (start + i) := by congr 1; symm; exact ext_append_lt I L S (succ_le_iff_lt.mpr hintv) (by simp)
    · calc
        S'{L}[i + 1] = S{L}[i + 1]                   := ext_append_lt I L S (succ_le_iff_lt.mpr hintv) (by simpa using hi)
        _            = S{L}[i] + fbit A (start + i)  := H i hi
        _            = S'{L}[i] + fbit A (start + i) := by congr 1; symm; apply ext_append_lt I L S (succ_le_iff_lt.mpr hintv) (by assumption)
  exact
    ⟨ S',
      lt_of_lt_of_le (append_lt_sq_smash I L S (succ_le_iff_lt.mpr hintv) le_len_L (by simpa using pos_of_gt hintv)) hU,
      H',
      ext_append_lt I L S (succ_le_iff_lt.mpr hintv) (by simp),
      ext_append_last I L S (succ_le_iff_lt.mpr hintv) le_len_L ⟩

lemma Series.succ (hU : (I ⨳ L)^2 ≤ U) (hIL : ‖‖I‖^2‖ ≤ ‖L‖)
    {iter n n' : V} (HT : Series U I L A iter n) (HS : Segment U L A (‖I‖ * iter) ‖I‖ n n') (hiter : iter < ‖I‖) :
    Series U I L A (iter + 1) n' := by
  have Hn : n ≤ ‖I‖ * iter := HT.le_add
  rcases HT with ⟨T, _, HT, Tₛ, rfl⟩
  let T' := append I L T (iter + 1) n'
  have hn'L : ‖n'‖ ≤ ‖L‖ := calc
    ‖n'‖ ≤ ‖T{L}[iter] + ‖I‖‖ := length_monotone HS.le_add
    _    ≤ ‖(iter + 1) * ‖I‖‖ := length_monotone <| by simp [add_mul, mul_comm iter, Hn]
    _    ≤ ‖‖I‖^2‖            := length_monotone <| by simpa [sq] using mul_le_mul_right (succ_le_iff_lt.mpr hiter)
    _    ≤ ‖L‖                := hIL
  have hTlast : T'{L}[iter + 1] = n' := ext_append_last I L T (succ_le_iff_lt.mpr hiter) hn'L
  have hTofLt : ∀ l ≤ iter, T'{L}[l] = T{L}[l] := fun l hl ↦ ext_append_lt I L T (succ_le_iff_lt.mpr hiter) (by simp [lt_succ_iff_le, hl])
  have HT' : IsSeries U I L A (iter + 1) T' := by
    intro l hl
    rcases show l ≤ iter from lt_succ_iff_le.mp hl with (rfl | hl)
    · simpa [hTofLt l (by simp), hTlast] using HS
    · have : T'{L}[l] = T{L}[l] := hTofLt l (le_of_lt hl)
      have : T'{L}[l + 1] = T{L}[l + 1] := hTofLt (l + 1) (succ_le_iff_lt.mpr hl)
      simpa [*] using HT l hl
  exact
  ⟨ T',
    lt_of_lt_of_le (append_lt_sq_smash I L T (succ_le_iff_lt.mpr hiter) hn'L (by simpa using pos_of_gt hiter)) hU,
    HT',
    Eq.trans (ext_append_lt I L T (succ_le_iff_lt.mpr hiter) (by simp)) Tₛ,
    hTlast ⟩

lemma div_mod_succ (a b : V) : ((a + 1) / b = a / b + 1 ∧ (a + 1) % b = 0 ∧ a % b + 1 = b) ∨ ((a + 1) / b = a / b ∧ (a + 1) % b = a % b + 1) := by
  rcases Arithmetic.zero_le b with (rfl | pos)
  · simp
  have : a % b + 1 ≤ b := lt_iff_succ_le.mp <| mod_lt a (by simp [pos])
  rcases this with (hb | ltb)
  · left
    have : b * (a / b + 1) = a + 1 := calc
      b * (a / b + 1) = b * (a / b) + a % b + 1 := by simp [hb, add_assoc, mul_add]
      _               = a + 1                   := by simp [div_add_mod a b]
    constructor <;> { rw [←this]; simp [pos, hb] }
  · right
    have : b * (a / b) + (a % b + 1) = a + 1 := by simp [←add_assoc, div_add_mod a b]
    constructor
    · rw [←this, mul_comm b, div_mul_add_self (a / b) (a % b + 1) pos]
      simp [ltb]
    · rw [←this, mul_comm b, mod_mul_add _ _ pos]
      simp [ltb]

lemma SeriesSegment.succ (hU : (I ⨳ L)^2 ≤ U) (hIL : ‖‖I‖^2‖ ≤ ‖L‖)
    {k n : V} (hk : k < ‖I‖^2) (H : SeriesSegment U I L A k n) :
    SeriesSegment U I L A (k + 1) (n + fbit A k) := by
  have hhk : (k + 1)/‖I‖ ≤ ‖I‖ := by simpa using div_monotone (succ_le_iff_lt.mpr hk) ‖I‖
  have hnk : n ≤ k := H.le
  have Ipos : 0 < I := by simpa using pos_of_gt hk
  rcases H with ⟨nₘ, hnₘn, HT, HS⟩
  have hnₘL : ‖nₘ + ‖I‖‖ ≤ ‖L‖ := by
    have : k / ‖I‖ < ‖I‖ := div_lt_of_lt_mul (by simpa [sq] using hk)
    calc
      ‖nₘ + ‖I‖‖ ≤ ‖‖I‖ * (k / ‖I‖ + 1)‖ := length_monotone <| by simp [mul_add, HT.le_add]
      _        ≤ ‖‖I‖^2‖                 := length_monotone <| by simpa [sq] using mul_le_mul_left (lt_iff_succ_le.mp this)
      _        ≤ ‖L‖                     := hIL
  rcases div_mod_succ k ‖I‖ with (⟨hdiv, hmodsucc, hmod⟩ | ⟨hdiv, hmod⟩)
  · have : Segment U L A (‖I‖ * (k / ‖I‖)) ‖I‖ nₘ (n + fbit A k) := by
      simpa [div_add_mod, hmod] using HS.succ hU (mod_lt _ $ by simp [Ipos]) hnₘL
    have : Series U I L A ((k + 1) / ‖I‖) (n + fbit A k) := by
      simpa [hdiv] using HT.succ hU hIL this (lt_iff_succ_le.mpr $ by simpa [hdiv] using hhk)
    exact ⟨n + fbit A k, by rfl, this, by
      simp only [hmodsucc]; apply Segment.refl U L A
      · calc
          L ⨳ 1 ≤ I ⨳ L     := by rw [smash_comm L 1]; apply smash_monotone (pos_iff_one_le.mp Ipos) (by rfl)
          _     ≤ (I ⨳ L)^2 := by simp
          _     ≤ U         := hU
      · calc
          ‖n + fbit A k‖ ≤ ‖n + 1‖ := length_monotone <| by simp
          _              ≤ ‖k + 1‖ := length_monotone <| by simp [hnk]
          _              ≤ ‖‖I‖^2‖ := length_monotone <| succ_le_iff_lt.mpr hk
          _              ≤ ‖L‖     := hIL⟩
  · have HS' : Segment U L A (‖I‖ * ((k + 1) / ‖I‖)) ((k + 1) % ‖I‖) nₘ (n + fbit A k) := by
      simpa [div_add_mod, hdiv, hmod] using HS.succ hU (mod_lt _ $ by simp [Ipos]) hnₘL
    have HT' : Series U I L A ((k + 1) / ‖I‖) nₘ := by simpa [hdiv] using HT
    exact ⟨nₘ, le_trans hnₘn le_self_add, HT', HS'⟩

end

section

/-- Define $I$, $L$, $U$ to satisfy the following:
  1. $I$, $L$, $U$ are polynomial of $A$.
  2. $(I \⨳ L)^2 \le U$
  3. $\| \| I \|^2 \| \le \|L\|$
  4. $\| A \| < \|I\|^2$
-/

noncomputable def polyI (A : V) : V := bexp (2 * A) (√‖A‖)

noncomputable def polyL (A : V) : V := ‖polyI A‖ ^ 2

def polyU (A : V) : V := (2 * A + 1) ^ 128

lemma len_polyI {A : V} (pos : 0 < A) : ‖polyI A‖ = √‖A‖ + 1 :=
  len_bexp (show √‖A‖ < ‖2 * A‖ from by simp [length_two_mul_of_pos pos, lt_succ_iff_le])

lemma polyI_le {A : V} (pos : 0 < A) : ‖A‖ < ‖polyI A‖ ^ 2 := by simp [len_polyI pos]

lemma two_add_two_eq_four : 2 + 2 = (4 : V) := by simp [←three_add_one_eq_four, ←two_add_one_eq_three, ←one_add_one_eq_two, add_assoc]

lemma four_mul_eq_two_mul_two_mul (a : V) : 4 * a = 2 * (2 * a) := by simp [←two_add_two_eq_four, add_mul, two_mul]

@[simp] lemma two_mul_sqrt_le_self (a : V) : 2 * √a ≤ a + 1 := le_trans (two_mul_le_sq_add_one (√a)) (by simp)

lemma four_mul_smash_self (a : V) : (4 * a) ⨳ (4 * a) ≤ (a ⨳ a) ^ 16 := calc
  (4 * a) ⨳ (4 * a) ≤ ((4 * a) ⨳ (2 * a)) ^ 2 := by simp [four_mul_eq_two_mul_two_mul, smash_two_mul_le_sq_smash]
  _                 ≤ ((4 * a) ⨳ a) ^ 4       := by simp [pow_four_eq_sq_sq, smash_two_mul_le_sq_smash]
  _                 ≤ ((a ⨳ (2 * a)) ^ 2) ^ 4 := by rw [smash_comm (4 * a) a]
                                                    simp [four_mul_eq_two_mul_two_mul, pow_four_eq_sq_sq, smash_two_mul_le_sq_smash]
  _                 ≤ ((a ⨳ a) ^ 4) ^ 4       := by simp [pow_four_eq_sq_sq, smash_two_mul_le_sq_smash]
  _                 ≤ (a ⨳ a) ^ 16       := by simp [←pow_mul]

@[simp] lemma pos_sq_iff {a : V} : 0 < √a ↔ 0 < a :=
  ⟨fun h ↦ lt_of_lt_of_le h (by simp),
    by intro h; by_contra A; simp at A;
       simp [show a = 0 from by simpa [A] using sqrt_lt_sq a] at h⟩

@[simp] lemma pow_four_le_pow_four {a b : V} : a ^ 4 ≤ b ^ 4 ↔ a ≤ b := by simp [pow_four_eq_sq_sq]

lemma bexp_four_mul {a a' x : V} (hx : 4 * x < ‖a‖) (hx' : x < ‖a'‖) :
    bexp a (4 * x) = (bexp a' x) ^ 4 := by
  rw [four_mul_eq_two_mul_two_mul, bexp_two_mul (a' := a), bexp_two_mul (a := a), pow_four_eq_sq_sq]
  · exact lt_of_le_of_lt (by simp [four_mul_eq_two_mul_two_mul]) hx
  · exact hx'
  · simpa [four_mul_eq_two_mul_two_mul] using hx
  · exact lt_of_le_of_lt (by simp [four_mul_eq_two_mul_two_mul]) hx

lemma polyI_smash_self_polybounded {A : V} (pos : 0 < A) : (polyI A) ⨳ (polyI A) ≤ (2 * A + 1) ^ 4 := calc
  (polyI A) ⨳ (polyI A) = bexp ((polyI A) ⨳ (polyI A)) ((√‖A‖ + 1) ^ 2) := Eq.symm <| by simpa [sq, len_polyI pos] using bexp_eq_smash (polyI A) (polyI A)
  _                     ≤ bexp ((2 * A) ⨳ (2 * A)) ((2 * √‖A‖) ^ 2)     :=
    (bexp_monotone_le
      (by simp [length_smash, ←sq, len_polyI pos])
      (by simp [length_smash, lt_succ_iff_le, ←sq, length_two_mul_of_pos pos])).mpr
    (by simp [two_mul, ←pos_iff_one_le, pos])
  _                     ≤ bexp ((2 * A) ⨳ (2 * A)) (4 * (√‖A‖) ^ 2)     := by simp [mul_pow, two_pow_two_eq_four]
  _                     = (bexp (A ⨳ 1) ((√‖A‖) ^ 2)) ^ 4               :=
    bexp_four_mul
      (by simp [length_smash, lt_succ_iff_le, ←sq, length_two_mul_of_pos pos, ←two_pow_two_eq_four, ←mul_pow])
      (by simp [length_smash, lt_succ_iff_le])
  _                     ≤ (bexp (A ⨳ 1) ‖A‖) ^ 4                        := by
    simpa using (bexp_monotone_le (by simp [length_smash, lt_succ_iff_le]) (by simp [length_smash])).mpr (by simp)
  _                     = (A ⨳ 1) ^ 4                                   := by congr 1; simpa using bexp_eq_smash A 1
  _                     ≤ (2 * A + 1) ^ 4                               := by simp

lemma polyI_smash_polyL_polybounded {A : V} (pos : 0 < A) : (polyI A) ⨳ (polyL A) ≤ (2 * A + 1) ^ 64 := calc
  (polyI A) ⨳ (polyL A) ≤ (polyI A) ⨳ (3 * polyI A)         := smash_monotone (by rfl) (by simp [polyL, sq_len_le_three_mul])
  _                     ≤ (4 * polyI A) ⨳ (4 * polyI A)     := smash_monotone (le_mul_of_pos_left $ by simp) (mul_le_mul_right $ by simp [←three_add_one_eq_four])
  _                     ≤ ((polyI A) ⨳ (polyI A)) ^ (4 * 4) := by simpa using four_mul_smash_self _
  _                     ≤ ((2 * A + 1) ^ 4) ^ (4 * 4)       := by simp only [pow_mul, pow_four_le_pow_four, polyI_smash_self_polybounded pos]
  _                     = (2 * A + 1) ^ 64         := by simp [←pow_mul]

lemma sq_polyI_smash_polyL_polybounded {A : V} (pos : 0 < A) : ((polyI A) ⨳ (polyL A)) ^ 2 ≤ polyU A := calc
  ((polyI A) ⨳ (polyL A)) ^ 2 ≤ ((2 * A + 1) ^ 64) ^ 2 := by simp [polyI_smash_polyL_polybounded pos]
  _                           = polyU A                         := by simp [polyU, ←pow_mul]

def NuonAux (A k n : V) : Prop := SeriesSegment (polyU A) (polyI A) (polyL A) A k n

def isSegmentDef : 𝚺₀.Semisentence 5 := .mkSigma
  “L A start intv S.
    ∀ i < intv,
      ∃ S_L_i_succ <⁺ S, !extDef S_L_i_succ L S (i + 1) ∧
      ∃ S_L_i <⁺ S, !extDef S_L_i L S i ∧
      ∃ fb < 2, !fbitDef fb A (start + i) ∧
        S_L_i_succ = S_L_i + fb”
  (by simp)

set_option linter.flexible false in
instance isSegmentDef_defined : 𝚺₀.Defined (V := V) (λ v ↦ IsSegment (v 0) (v 1) (v 2) (v 3) (v 4)) isSegmentDef := .mk fun v ↦ by
  simp [IsSegment, isSegmentDef, numeral_eq_natCast]
  apply forall₂_congr; intro x _
  constructor
  · rintro ⟨_, h⟩; exact h.symm
  · intro h; exact ⟨by simp [←h], h.symm⟩

def segmentDef : 𝚺₀.Semisentence 7 := .mkSigma
  “U L A start intv nₛ nₑ. ∃ S < U, !isSegmentDef L A start intv S ∧ !extDef nₛ L S 0 ∧ !extDef nₑ L S intv”

instance segmentDef_defined : 𝚺₀.Defined (V := V) (λ v ↦ Segment (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) segmentDef := .mk fun v ↦ by
  simp [Segment, segmentDef, @Eq.comm _ (v 5), @Eq.comm _ (v 6)]

def isSeriesDef : 𝚺₀.Semisentence 6 := .mkSigma
  “U I L A iter T.
    ∀ l < iter,
      ∃ lI <⁺ I, !lengthDef lI I ∧
      ∃ x <⁺ T, !extDef x L T l ∧
      ∃ y <⁺ T, !extDef y L T (l + 1) ∧
        !segmentDef U L A (lI * l) lI x y”

omit [V ⊧ₘ* 𝗜𝚺₀ + 𝝮₁] in
lemma bexs_eq_le_iff {p : V → Prop} {b : V} :
    (∃ a ≤ z, a = b ∧ p a) ↔ (b ≤ z ∧ p b) :=
  ⟨by rintro ⟨a, hp, rfl, hr⟩; exact ⟨hp, hr⟩, by rintro ⟨hp, hr⟩; exact ⟨b, hp, rfl, hr⟩⟩

omit [V ⊧ₘ* 𝗜𝚺₀ + 𝝮₁] in
lemma bexs_eq_lt_iff {p : V → Prop} {b : V} :
    (∃ a < z, a = b ∧ p a) ↔ (b < z ∧ p b) :=
  ⟨by rintro ⟨a, hp, rfl, hr⟩; exact ⟨hp, hr⟩, by rintro ⟨hp, hr⟩; exact ⟨b, hp, rfl, hr⟩⟩

instance isSerieDef_defined : 𝚺₀.Defined (V := V) (λ v ↦ IsSeries (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) isSeriesDef := .mk fun v ↦ by
  simp [IsSeries, isSeriesDef]

def seriesDef : 𝚺₀.Semisentence 6 := .mkSigma
  “U I L A iter n. ∃ T < U, !isSeriesDef U I L A iter T ∧ !extDef 0 L T 0 ∧ !extDef n L T iter”

set_option linter.flexible false in
instance seriesDef_defined : 𝚺₀.Defined (V := V) (λ v ↦ Series (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) seriesDef := .mk fun v ↦ by
  simp [Series, seriesDef]
  apply exists_congr; intro T
  apply and_congr_right; intros
  apply and_congr_right; intros
  simp [Eq.comm]

def seriesSegmentDef : 𝚺₀.Semisentence 6 := .mkSigma
  “U I L A k n.
    ∃ nₖ <⁺ n,
      ∃ l <⁺ I, !lengthDef l I ∧
      ∃ d <⁺ k, !divDef d k l ∧
      ∃ r <⁺ k, !remDef r k l ∧
      !seriesDef U I L A d nₖ ∧ !segmentDef U L A (l * d) r nₖ n”
  (by simp)

instance seriesSegmentDef_defined : 𝚺₀.Defined (V := V) (λ v ↦ SeriesSegment (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) seriesSegmentDef := .mk fun v ↦ by
  simp [SeriesSegment, seriesSegmentDef]

def nuonAuxDef : 𝚺₀.Semisentence 3 := .mkSigma
  “A k n.
    ∃ lA <⁺ A, !lengthDef lA A ∧
    ∃ sA <⁺ lA, !sqrtDef sA lA ∧
    ∃ g <⁺ 2 * A, !bexpDef g (2 * A) sA ∧
    ∃ lg <⁺ g, !lengthDef lg g ∧
      !seriesSegmentDef ((2 * A + 1) ^' 128) g (lg ²) A k n”

instance nuonAux_defined : 𝚺₀-Relation₃ (NuonAux : V → V → V → Prop) via nuonAuxDef := .mk fun v ↦ by
  simp [NuonAux, polyU, polyI, polyL, nuonAuxDef, numeral_eq_natCast]

instance nuonAux_definable : 𝚺₀-Relation₃ (NuonAux : V → V → V → Prop) := nuonAux_defined.to_definable

instance : Bounded₃ (ext : V → V → V → V) := ⟨#1, λ _ ↦ by simp⟩

@[simp] lemma NuonAux.initial (A : V) : NuonAux A 0 0 := SeriesSegment.initial (by simp [polyU])

@[simp] lemma NuonAux.initial_iff (A n : V) : NuonAux A 0 n ↔ n = 0 := ⟨fun h ↦ h.uniq (NuonAux.initial A), by rintro rfl; simp⟩

@[simp] lemma NuonAux.zero (k : V) : NuonAux 0 k 0 := SeriesSegment.zero (by simp [polyU])

lemma NuonAux.le {A k n : V} (H : NuonAux A k n) : n ≤ k := SeriesSegment.le H

lemma NuonAux.uniq {A k n₁ n₂ : V} (H₁ : NuonAux A k n₁) (H₂ : NuonAux A k n₂) : n₁ = n₂ := SeriesSegment.uniq H₁ H₂

lemma NuonAux.succ {A k : V} (H : NuonAux A k n) (hk : k ≤ ‖A‖) : NuonAux A (k + 1) (n + fbit A k) := by
  rcases Arithmetic.zero_le A with (rfl | pos)
  · rcases show n = 0 from H.uniq (NuonAux.zero k); simp
  exact SeriesSegment.succ (sq_polyI_smash_polyL_polybounded pos) (by simp [polyL]) (lt_of_le_of_lt hk $ polyI_le pos) H

lemma NuonAux.exists {k : V} (hk : k ≤ ‖A‖) : ∃ n, NuonAux A k n := by
  suffices ∃ n ≤ k, NuonAux A k n by
    rcases this with ⟨n, _, h⟩; exact ⟨n, h⟩
  revert hk
  induction k using ISigma0.succ_induction
  · definability
  case zero =>
    intro _; exact ⟨0, by simp⟩
  case succ k IH =>
    intro hk
    rcases IH (le_trans (by simp) hk) with ⟨n, hn, Hn⟩
    exact ⟨n + fbit A k, add_le_add hn (by simp), Hn.succ (le_trans (by simp) hk)⟩

lemma NuonAux.succ_elim {A k : V} (hk : k ≤ ‖A‖) (H : NuonAux A (k + 1) n) : ∃ n', n = n' + fbit A k ∧ NuonAux A k n' := by
  rcases NuonAux.exists hk with ⟨n', H'⟩
  rcases H.uniq (H'.succ hk)
  exact ⟨n', rfl, H'⟩

lemma NuonAux.succ_iff {A k : V} (hk : k ≤ ‖A‖) : NuonAux A (k + 1) (n + fbit A k) ↔ NuonAux A k n := by
  constructor
  · intro H
    rcases NuonAux.exists hk with ⟨n', H'⟩
    rcases show n' = n from by simpa using (H'.succ hk).uniq H
    exact H'
  · exact (NuonAux.succ · hk)

lemma NuonAux.two_mul {k n : V} (hk : k ≤ ‖A‖) : NuonAux A k n → NuonAux (2 * A) (k + 1) n := by
  revert n hk
  suffices ∀ n ≤ k, k ≤ ‖A‖ → NuonAux A k n → NuonAux (2 * A) (k + 1) n by
    intro n hk H
    exact this n H.le hk H
  induction k using ISigma0.succ_induction
  · definability
  case zero =>
    simp; simpa using (NuonAux.initial (2 * A)).succ (by simp)
  case succ k IH =>
    intro n hn hk H
    rcases H.succ_elim (le_trans (by simp) hk) with ⟨n', rfl, H'⟩
    have IH : NuonAux (2 * A) (k + 1) n' := IH n' H'.le (le_trans (by simp) hk) H'
    simpa using IH.succ (le_trans hk (length_monotone $ by simp))

lemma NuonAux.two_mul_add_one {k n : V} (hk : k ≤ ‖A‖) : NuonAux A k n → NuonAux (2 * A + 1) (k + 1) (n + 1) := by
  revert n hk
  suffices ∀ n ≤ k, k ≤ ‖A‖ → NuonAux A k n → NuonAux (2 * A + 1) (k + 1) (n + 1) by
    intro n hk H
    exact this n H.le hk H
  induction k using ISigma0.succ_induction
  · definability
  case zero =>
    simpa using (NuonAux.initial (2 * A + 1)).succ (by simp)
  case succ k IH =>
    intro n hn hk H
    rcases H.succ_elim (le_trans (by simp) hk) with ⟨n', rfl, H'⟩
    have IH : NuonAux (2 * A + 1) (k + 1) (n' + 1) := IH n' H'.le (le_trans (by simp) hk) H'
    simpa [add_right_comm n' 1] using IH.succ (le_trans hk (by simp [length_two_mul_add_one]))

end

end Nuon

def Nuon (A n : V) : Prop := Nuon.NuonAux A ‖A‖ n

lemma Nuon.exists_unique (A : V) : ∃! n, Nuon A n := by
  rcases show ∃ n, Nuon A n from NuonAux.exists (by simp) with ⟨n, hn⟩
  exact ExistsUnique.intro n hn (fun n' hn' ↦ hn'.uniq hn)

noncomputable def nuon (a : V) : V := Classical.choose! (Nuon.exists_unique a)

@[simp] lemma nuon_nuon (a : V) : Nuon a (nuon a) := Classical.choose!_spec (Nuon.exists_unique a)

lemma Nuon.nuon_eq {a b : V} (h : Nuon a b) : nuon a = b := (nuon_nuon a).uniq h

lemma Nuon.nuon_eq_iff {a b : V} : b = nuon a ↔ Nuon a b := Classical.choose!_eq_iff_right (Nuon.exists_unique a)

lemma nuon_bit0 (a : V) : nuon (2 * a) = nuon a := by
  rcases Arithmetic.zero_le a with (rfl | pos)
  · simp
  · have : Nuon (2 * a) (nuon a) := by simpa [Nuon, length_two_mul_of_pos pos] using (nuon_nuon a).two_mul (by simp)
    exact this.nuon_eq

lemma nuon_bit1 (a : V) : nuon (2 * a + 1) = nuon a + 1 := by
  have : Nuon (2 * a + 1) (nuon a + 1) := by simpa [Nuon, length_two_mul_add_one] using (nuon_nuon a).two_mul_add_one (by simp)
  exact this.nuon_eq

@[simp] lemma nuon_zero : nuon (0 : V) = 0 := Nuon.nuon_eq (by simp [Nuon])

def _root_.LO.FirstOrder.Arithmetic.nuonDef : 𝚺₀.Semisentence 2 := .mkSigma
  “n A. ∃ l <⁺ A, !lengthDef l A ∧ !Nuon.nuonAuxDef A l n”

instance nuon_defined : 𝚺₀-Function₁ (nuon : V → V) via nuonDef := .mk fun v ↦ by simp [Nuon.nuon_eq_iff, Nuon, nuonDef]

instance nuon_definable : 𝚺₀-Function₁ (nuon : V → V) := nuon_defined.to_definable

end LO.FirstOrder.Arithmetic
