import Arithmetization.Exponential.Omega

namespace LO.FirstOrder

namespace Arith

noncomputable section

namespace Model

variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [𝐏𝐀⁻.Mod M] [𝐈𝚺₀.Mod M] [𝛀₁.Mod M]

namespace Nuon

@[simp] lemma llen_lt_len_hash_len (K : M) : ‖‖K‖‖ < ‖K # ‖K‖‖ := by
  simp [length_hash, lt_succ_iff_le]
  rcases zero_le ‖K‖ with (hK | pos)
  · simp [←hK]
  · exact le_mul_of_pos_left pos

lemma mul_len_lt_len_hash {i I L : M} (hi : i ≤ ‖I‖) : i * ‖L‖ < ‖I # L‖ := by
  simp [length_hash, lt_succ_iff_le]; exact mul_le_mul_right' hi ‖L‖

lemma mul_len_lt_len_hash' {i K Z : M} (hi : i ≤ ‖z‖) : i * ‖‖K‖‖ < ‖z # ‖K‖‖ := by
  simp [length_hash, lt_succ_iff_le]; exact mul_le_mul_right' hi ‖‖K‖‖

def ext (L S i : M) : M := S / bexp S (i * ‖L‖) % (L # 1)

local notation S "{" L "}[" i "]" => ext L S i

lemma ext_eq_zero_of_lt {L S i : M} (h : ‖S‖ ≤ i * ‖L‖) : S{L}[i] = 0 := by simp [ext, bexp_eq_zero_of_le h]

@[simp] lemma ext_le_self (L S i : M) : S{L}[i] ≤ S := le_trans (mod_le _ _) (by simp [ext])

lemma ext_graph_aux (z S L i : M) : z = S{L}[i] ↔ (‖S‖ ≤ i * ‖L‖ → z = 0) ∧ (i * ‖L‖ < ‖S‖ → ∃ b ≤ S, Exp (i * ‖L‖) b ∧ z = S / b % (L # 1)) := by
  rcases show ‖S‖ ≤ i * ‖L‖ ∨ i * ‖L‖ < ‖S‖ from le_or_lt _ _ with (le | lt)
  · simp [ext_eq_zero_of_lt le, le, not_lt.mpr le]
  · simp [lt, not_le.mpr lt, ext]
    have := exp_bexp_of_lt lt
    constructor
    · rintro rfl; exact ⟨bexp S (i * ‖L‖), by simp, exp_bexp_of_lt lt, rfl⟩
    · rintro ⟨b, _, H, rfl⟩
      rcases H.uniq (exp_bexp_of_lt lt); rfl

lemma ext_graph (z S L i : M) : z = S{L}[i] ↔
    ∃ lS ≤ S, lS = ‖S‖ ∧ ∃ lL ≤ L, lL = ‖L‖ ∧
      (lS ≤ i * lL → z = 0) ∧
      (i * lL < lS →
        ∃ b ≤ S, Exp (i * lL) b ∧ ∃ hL ≤ 2 * L + 1, Exp lL hL ∧ ∃ divS ≤ S, divS = S / b ∧ z = divS % hL) := by
  rw [ext_graph_aux]
  rcases show ‖S‖ ≤ i * ‖L‖ ∨ i * ‖L‖ < ‖S‖ from le_or_lt _ _ with (le | lt)
  · simp [ext_eq_zero_of_lt le, le, not_lt.mpr le]
    constructor
    · rintro rfl; exact ⟨‖S‖, by simp, rfl, ‖L‖, by simp, rfl, by simp [not_lt.mpr le]⟩
    · rintro ⟨_, _, rfl, _, _, rfl, h, _⟩; exact h le
  · simp [lt, not_le.mpr lt]
    constructor
    · rintro ⟨b, hb, Hb, rfl⟩; refine ⟨‖S‖, by simp, rfl, ‖L‖, by simp, rfl, ?_⟩
      simp [not_le.mpr lt, lt]
      exact ⟨b, hb, Hb, L # 1, by simp, exp_hash_one L, S / b, by simp, rfl, rfl⟩
    · rintro ⟨_, _, rfl, _, _, rfl, _, h⟩
      rcases h lt with ⟨b, hb, Hb, hL, _, HhL, _, _, rfl, rfl⟩
      exact ⟨b, hb, Hb, by rw [HhL.uniq (exp_hash_one L)]⟩

def extdef : Σᴬ[0] 4 :=
  ⟨ “∃[#0 < #3 + 1] (!binarylengthdef [#0, #3] ∧ ∃[#0 < #3 + 1] (!binarylengthdef [#0, #3] ∧
      (#1 ≤ #5 * #0 → #2 = 0) ∧
      (#5 * #0 < #1 →
        ∃[#0 < #5 + 1] (!Exp.def [#6 * #1, #0] ∧
          ∃[#0 < 2 * #5 + 1 + 1] (!Exp.def [#2, #0] ∧
            ∃[#0 < #7 + 1] (!divdef [#0, #7, #2] ∧ !remdef [#5, #0, #1]))))))”, by
    simp
    rw [Hierarchy.bex_iff]
    · simp
    · simp; decide ⟩

@[simp] lemma Fin.succ_two_eq_three : (2 : Fin 3).succ = 3 := rfl

@[simp] lemma cons_app_seven {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ.succ → α) : (a :> s) 7 = s 6 := rfl

@[simp] lemma cons_app_eight {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ.succ.succ → α) : (a :> s) 8 = s 7 := rfl

lemma ext_defined : Σᴬ[0]-Function₃ (ext : M → M → M → M) extdef := by
  intro v; simp [extdef, length_defined.pval, Exp.defined.pval, div_defined.pval, rem_defined.pval, lt_succ_iff_le, ext_graph]

instance {b s} : DefinableFunction₃ b s (ext : M → M → M → M) := defined_to_with_param₀ _ ext_defined

instance : PolyBounded₃ (ext : M → M → M → M) := ⟨#1, λ _ ↦ by simp⟩

@[simp] lemma ext_zero (L i : M) : 0{L}[i] = 0 := by simp [ext]

lemma ext_zero_eq_self_of_le {L S : M} (h : ‖S‖ ≤ ‖L‖) : S{L}[0] = S := by
  rcases zero_le S with (rfl | pos)
  · simp [ext]
  · simp [ext]
    have : bexp S 0 = 1 := (exp_bexp_of_lt (show 0 < ‖S‖ from by simp [pos])).zero_uniq
    simp [this, lt_hash_one_iff.mpr h]

lemma ext_eq_of_ge {L S S' i : M} (h : S ≤ S') : S / bexp S' (i * ‖L‖) % (L # 1) = S{L}[i] := by
  rcases show i * ‖L‖ < ‖S‖ ∨ ‖S‖ ≤ i * ‖L‖ from lt_or_ge (i * ‖L‖) ‖S‖ with (lt | le)
  · unfold ext; congr 2; exact bexp_eq_of_lt_length (lt_of_lt_of_le lt $ length_monotone h) lt
  · simp [ext_eq_zero_of_lt le]
    rcases show i * ‖L‖ < ‖S'‖ ∨ ‖S'‖ ≤ i * ‖L‖ from lt_or_ge (i * ‖L‖) ‖S'‖ with (lt' | le')
    · have : S < bexp S' (i * ‖L‖) := ((exp_bexp_of_lt lt').lt_iff_len_le).mpr le
      simp [this]
    · simp [bexp_eq_zero_of_le le']

lemma ext_eq_of_gt {L S S' i : M} (h : i * ‖L‖ < ‖S'‖) : S / bexp S' (i * ‖L‖) % (L # 1) = S{L}[i] := by
  rcases show i * ‖L‖ < ‖S‖ ∨ ‖S‖ ≤ i * ‖L‖ from lt_or_ge (i * ‖L‖) ‖S‖ with (lt | le)
  · unfold ext; congr 2; exact bexp_eq_of_lt_length h lt
  · simp [ext_eq_zero_of_lt le]
    have : S < bexp S' (i * ‖L‖) := ((exp_bexp_of_lt h).lt_iff_len_le).mpr le
    simp [this]

lemma ext_eq_hash_of_le {L S i : M} (h : i ≤ ‖I‖) : S / bexp (I # L) (i * ‖L‖) % (L # 1) = S{L}[i] :=
  ext_eq_of_gt (mul_len_lt_len_hash h)

lemma ext_add₁_pow2 {L i S₁ S₂ p : M} (pp : Pow2 p) (h : (i + 1) * ‖L‖ < ‖p‖) :
    (S₁ + S₂ * p){L}[i] = S₁{L}[i] := by
  rcases zero_le S₂ with (rfl | pos₂)
  · simp
  have lt_len : i * ‖L‖ < ‖S₁ + S₂ * p‖ := calc
        i * ‖L‖ ≤ (i + 1) * ‖L‖ := mul_le_mul_right (by simp)
        _       < ‖p‖           := h
        _       ≤ ‖S₁ + S₂ * p‖ := length_monotone (le_add_left (le_mul_of_pos_left pos₂))
  have : Exp ((i + 1) * ‖L‖) (bexp (S₁ + S₂ * p) (i * ‖L‖) * L # 1) := by
    simp [add_mul]
    exact Exp.add_mul (by simp [lt_len]) (by simpa using exp_hash L 1)
  have : bexp (S₁ + S₂ * p) (i * ‖L‖) * L # 1 ∣ p :=
    Pow2.dvd_of_le (by simp; apply bexp_pow2 lt_len) pp (this.monotone_le (exp_of_pow2 pp) (le_log_of_lt_length h))
  rcases this with ⟨q, hq⟩
  calc
    (S₁ + S₂ * p){L}[i] = (S₁ + p * S₂) / bexp (S₁ + S₂ * p) (i * ‖L‖) % L # 1         := by simp [ext, mul_comm S₂]
    _                   = (S₁ + bexp (S₁ + S₂ * p) (i * ‖L‖) * (L # 1 * q * S₂)) / bexp (S₁ + S₂ * p) (i * ‖L‖) % L # 1 := by simp [←mul_assoc, ←hq]
    _                   = (S₁ / bexp (S₁ + S₂ * p) (i * ‖L‖) + L # 1 * q * S₂) % L # 1 := by rw [div_add_mul_self' _ _ (bexp_pos lt_len)]
    _                   = S₁ / bexp (S₁ + S₂ * p) (i * ‖L‖) % L # 1                    := by simp [mul_assoc]
    _                   = S₁{L}[i]                                                     := ext_eq_of_ge le_self_add

lemma ext_add₁_bexp {L i j S₁ S₂ : M} (hi : i ≤ ‖I‖) (hij : j < i) :
    (S₁ + S₂ * bexp (I # L) (i * ‖L‖)){L}[j] = S₁{L}[j] :=
  ext_add₁_pow2 (bexp_pow2 $ mul_len_lt_len_hash hi)
    (by rw [len_bexp (mul_len_lt_len_hash hi), lt_succ_iff_le]; exact mul_le_mul_right (succ_le_iff_lt.mpr hij))

lemma ext_add₂_bexp {I i j S₁ S₂ : M} (hij : i + j ≤ ‖I‖) (hS₁ : ‖S₁‖ ≤ i * ‖L‖) :
    (S₁ + S₂ * bexp (I # L) (i * ‖L‖)){L}[i + j] = S₂{L}[j] := by
  have hie : Exp (i * ‖L‖) (bexp (I # L) (i * ‖L‖)) := exp_bexp_of_lt (mul_len_lt_len_hash $ le_trans le_self_add hij)
  calc  (S₁ + S₂ * bexp (I # L) (i * ‖L‖)){L}[i + j]
      = (S₁ + S₂ * bexp (I # L) (i * ‖L‖)) / bexp (I # L) ((i + j) * ‖L‖) % (L # 1)                    := by rw [ext_eq_hash_of_le hij]
    _ = (S₁ + S₂ * bexp (I # L) (i * ‖L‖)) / bexp (I # L) (i * ‖L‖) / bexp (I # L) (j * ‖L‖) % (L # 1) := by
      simp [←div_mul, add_mul]; congr 2; exact bexp_add (by simp [←add_mul, mul_len_lt_len_hash hij])
    _ = S₂ / bexp (I # L) (j * ‖L‖) % (L # 1)                                                          := by
      congr 2; rw [div_add_mul_self, div_eq_zero_of_lt] <;> simp [hie.lt_iff_len_le.mpr hS₁, hie.range_pos]
    _ = S₂{L}[j]                                                                                       := ext_eq_hash_of_le (le_trans le_add_self hij)

def append (I L S i X : M) : M := S % bexp (I # L) (i * ‖L‖) + X * bexp (I # L) (i * ‖L‖)

lemma append_nil (I L S i : M) : append I L S i 0 = S % bexp (I # L) (i * ‖L‖) := by simp [append]

lemma len_append (I L S : M) {i X} (hi : i ≤ ‖I‖) (hX : 0 < X) : ‖append I L S i X‖ = ‖X‖ + i * ‖L‖ := calc
  ‖append I L S i X‖ = ‖X * bexp (I # L) (i * ‖L‖) + S % bexp (I # L) (i * ‖L‖)‖ := by simp [append, add_comm]
  _                  = ‖X‖ + log (bexp (I # L) (i * ‖L‖))                        := length_mul_pow2_add_of_lt hX
                                                                                      (bexp_pow2 $ mul_len_lt_len_hash hi)
                                                                                      (mod_lt _ $ bexp_pos $ mul_len_lt_len_hash hi)
  _                  = ‖X‖ + i * ‖L‖                                             := by simp [log_bexp (mul_len_lt_len_hash hi)]

lemma append_lt_hash (I L S : M) {i X} (hi : i < ‖I‖) (hX : ‖X‖ ≤ ‖L‖) : append I L S i X < I # L := by
  rcases zero_le X with (rfl | pos)
  · simp [append_nil]
    exact lt_of_lt_of_le (mod_lt _ (bexp_pos $ mul_len_lt_len_hash $ le_of_lt hi)) (by simp)
  · simp [lt_hash_iff, len_append I L S (le_of_lt hi) pos]
    calc
      ‖X‖ + i * ‖L‖ ≤ (i + 1) * ‖L‖ := by simp [add_mul, add_comm (i * ‖L‖), hX]
      _             ≤ ‖I‖ * ‖L‖     := mul_le_mul_right (succ_le_iff_lt.mpr hi)

lemma append_lt_sq_hash (I L S : M) {i X} (hi : i ≤ ‖I‖) (hX : ‖X‖ ≤ ‖L‖) (Ipos : 0 < I) : append I L S i X < (I # L)^2 := by
  rcases hi with (rfl | hi)
  · calc
      append I L S ‖I‖ X = S % I # L + X * I # L := by simp [append, bexp_eq_hash]
      _                  < (X + 1) * I # L       := by simp [add_mul, add_comm]
      _                  ≤ L # 1 * I # L         := mul_le_mul_right (succ_le_iff_lt.mpr $ lt_hash_one_iff.mpr hX)
      _                  ≤ (I # L) ^ 2           := by simp [sq, hash_comm L 1]; exact hash_monotone (pos_iff_one_le.mp Ipos) (by rfl)
  · exact lt_of_lt_of_le (append_lt_hash I L S hi hX) (by simp)

lemma ext_append_last (I L S : M) {i X} (hi : i ≤ ‖I‖) (hX : ‖X‖ ≤ ‖L‖) : (append I L S i X){L}[i] = X := calc
  (append I L S i X){L}[i] = (S % bexp (I # L) (i * ‖L‖) + X * bexp (I # L) (i * ‖L‖)){L}[i + 0] := by simp [append]
  _                        =  X{L}[0]                                                            := ext_add₂_bexp (by simpa using hi)
                                                                                                      ((exp_bexp_of_lt (mul_len_lt_len_hash hi)).lt_iff_len_le.mp
                                                                                                        (mod_lt _ $ bexp_pos $ mul_len_lt_len_hash hi))
  _                        =  X                                                                  := ext_zero_eq_self_of_le hX

lemma ext_append_lt (I L S : M) {i j X} (hi : i ≤ ‖I‖) (hij : j < i) :
    (append I L S i X){L}[j] = S{L}[j] := calc
  (append I L S i X){L}[j] = (S % bexp (I # L) (i * ‖L‖) + X * bexp (I # L) (i * ‖L‖)){L}[j] := rfl
  _                        = (S % bexp (I # L) (i * ‖L‖)){L}[j]                              := ext_add₁_bexp hi hij
  _                        = (S % bexp (I # L) (i * ‖L‖) + (S / bexp (I # L) (i * ‖L‖)) * bexp (I # L) (i * ‖L‖)){L}[j] := Eq.symm <| ext_add₁_bexp hi hij
  _                        = S{L}[j]                                                         := by rw [add_comm, mul_comm, div_add_mod]

variable {L A : M}

def IsSegment (L A start intv S : M) : Prop := ∀ i < intv, S{L}[i + 1] = S{L}[i] + fbit A (start + i)

def Segment (U L A start intv nₛ nₑ : M) : Prop := ∃ S < U, IsSegment L A start intv S ∧ S{L}[0] = nₛ ∧ S{L}[intv] = nₑ

def IsSeries (U I L A iter T : M) : Prop := ∀ l < iter, Segment U L A (‖I‖ * l) ‖I‖ (T{L}[l]) (T{L}[l + 1])

def Series (U I L A iter n : M) : Prop := ∃ T < U, IsSeries U I L A iter T ∧ T{L}[0] = 0 ∧ T{L}[iter] = n

def SeriesSegment (U I L A k n : M) : Prop := ∃ nₖ ≤ n, Series U I L A (k / ‖I‖) nₖ ∧ Segment U L A (‖I‖ * (k / ‖I‖)) (k % ‖I‖) nₖ n

lemma SeriesSegment.series {U I L A k n : M} (H : SeriesSegment U I L A k n) :
    ∃ T S, IsSeries U I L A (k / ‖I‖) T ∧ IsSegment L A (‖I‖ * (k / ‖I‖)) (k % ‖I‖) S ∧ T{L}[0] = 0 ∧ T{L}[k / ‖I‖] = S{L}[0] ∧ S{L}[k % ‖I‖] = n := by
  rcases H with ⟨_, _, ⟨T, _, hT, hTₛ, hTₑ⟩, ⟨S, _, hS, rfl, rfl⟩⟩
  exact ⟨T, S, hT, hS, hTₛ, hTₑ, rfl⟩

lemma IsSegment.le_add {L A start intv S : M} (H : IsSegment L A start intv S) : ∀ i ≤ intv, S{L}[i] ≤ S{L}[0] + i := by
  intro i
  induction i using hierarchy_induction_sigma₀
  · definability
  case zero => simp
  case succ i IH =>
    intro h
    have IH : S{L}[i] ≤ S{L}[0] + i := IH (le_trans (by simp) h)
    calc
      S{L}[i + 1] = S{L}[i] + fbit A (start + i) := H i (succ_le_iff_lt.mp h)
      _           ≤ S{L}[i] + 1                  := by simp
      _           ≤ S{L}[0] + (i + 1)            := by simp [←add_assoc, IH]

-- lemma Segment.refl (U L A start n : M) (hU : n < U) (hn : ‖n‖ ≤ ‖L‖) : Segment U L A start 0 n n :=
--   ⟨n, hU, by intro; simp, ext_zero_eq_self_of_le hn, ext_zero_eq_self_of_le hn⟩

lemma Segment.refl (U L A start n : M) (hL : L # 1 ≤ U) (hn : ‖n‖ ≤ ‖L‖) : Segment U L A start 0 n n :=
  ⟨n, lt_of_lt_of_le (lt_hash_one_iff.mpr hn) hL, by intro; simp, ext_zero_eq_self_of_le hn, ext_zero_eq_self_of_le hn⟩

lemma Segment.le_add {U L A start intv nₛ nₑ : M} (H : Segment U L A start intv nₛ nₑ) : nₑ ≤ nₛ + intv := by
  rcases H with ⟨S, _, hS, rfl, rfl⟩; exact hS.le_add intv (by rfl)

lemma Segment.uniq {U L A start intv nₛ nₑ₁ nₑ₂ : M}
    (H₁ : Segment U L A start intv nₛ nₑ₁) (H₂ : Segment U L A start intv nₛ nₑ₂) : nₑ₁ = nₑ₂ := by
  rcases H₁ with ⟨S₁, _, HS₁, Hₛ, rfl⟩
  rcases H₂ with ⟨S₂, _, HS₂, rfl, rfl⟩
  suffices : ∀ i ≤ intv, S₁{L}[i] = S₂{L}[i]
  · exact this intv (by rfl)
  intro i; induction i using hierarchy_induction_sigma₀
  · definability
  case zero => intro _; exact Hₛ
  case succ i IH =>
    intro hi
    have h₁ : S₁{L}[i + 1] = S₁{L}[i] + fbit A (start + i) := HS₁ i (lt_iff_succ_le.mpr hi)
    have h₂ : S₂{L}[i + 1] = S₂{L}[i] + fbit A (start + i) := HS₂ i (lt_iff_succ_le.mpr hi)
    simp [IH (le_trans (by simp) hi), h₁, h₂]

lemma IsSeries.le_add {U I L A iter T : M} (H : IsSeries U I L A iter T) : ∀ l ≤ iter, T{L}[l] ≤ T{L}[0] + ‖I‖ * l := by
  intro l
  induction l using hierarchy_induction_sigma₀
  · definability
  case zero => simp
  case succ l IH =>
    intro h
    have IH : T{L}[l] ≤ T{L}[0] + ‖I‖ * l := IH (le_trans (by simp) h)
    calc
      T{L}[l + 1] ≤ T{L}[l] + ‖I‖           := (H l (succ_le_iff_lt.mp h)).le_add
      _           ≤ T{L}[0] + ‖I‖ * (l + 1) := by simpa [mul_add, ←add_assoc] using IH

lemma Series.le_add {U I L A iter n : M} (H : Series U I L A iter n) : n ≤ ‖I‖ * iter := by
  rcases H with ⟨T, _, hT, hzero, rfl⟩; simpa [hzero] using hT.le_add iter (by rfl)

lemma Series.uniq {U I L A iter n₁ n₂ : M} (H₁ : Series U I L A iter n₁) (H₂ : Series U I L A iter n₂) : n₁ = n₂ := by
  rcases H₁ with ⟨T₁, _, HT₁, Hₛ₁, rfl⟩
  rcases H₂ with ⟨T₂, _, HT₂, Hₛ₂, rfl⟩
  suffices : ∀ i ≤ iter, T₁{L}[i] = T₂{L}[i]
  · exact this iter (by rfl)
  intro i; induction i using hierarchy_induction_sigma₀
  · definability
  case zero => intro _; simp [Hₛ₁, Hₛ₂]
  case succ i IH =>
    intro hi
    have IH : T₁{L}[i] = T₂{L}[i] := IH (le_trans (by simp) hi)
    have h₁ : Segment U L A (‖I‖ * i) ‖I‖ (T₁{L}[i]) (T₁{L}[i + 1]) := HT₁ i (lt_iff_succ_le.mpr hi)
    have h₂ : Segment U L A (‖I‖ * i) ‖I‖ (T₁{L}[i]) (T₂{L}[i + 1]) := by simpa [IH] using HT₂ i (lt_iff_succ_le.mpr hi)
    exact h₁.uniq h₂

lemma SeriesSegment.le {U I L A k n : M} (H : SeriesSegment U I L A k n) :
    n ≤ k := by
  rcases H with ⟨nₖ, _, hT, hS⟩
  calc
    n ≤ nₖ + k % ‖I‖              := hS.le_add
    _ ≤ ‖I‖ * (k / ‖I‖) + k % ‖I‖ := by simpa [mul_comm] using hT.le_add
    _ = k                         := div_add_mod k ‖I‖

lemma SeriesSegment.zero {U I L A : M} (Upos : 0 < U) : SeriesSegment U I L A 0 0 :=
  ⟨0, by rfl, ⟨0, Upos, by simp [IsSeries]⟩, ⟨0, Upos, by simp [IsSegment]⟩⟩

lemma SeriesSegment.uniq {U I L A k n₁ n₂ : M} (H₁ : SeriesSegment U I L A k n₁) (H₂ : SeriesSegment U I L A k n₂) :
    n₁ = n₂ := by
  rcases H₁ with ⟨nₘ₁, _, hT₁, hS₁⟩
  rcases H₂ with ⟨nₘ₂, _, hT₂, hS₂⟩
  rcases show nₘ₁ = nₘ₂ from hT₁.uniq hT₂
  exact hS₁.uniq hS₂

section

variable {U I L A : M} (hU : (I # L)^2 ≤ U) (hIL : ‖‖I‖^2‖ ≤ ‖L‖) (Ipos : 0 < I)

lemma Segment.succ {start intv nₛ nₑ : M} (H : Segment U L A start intv nₛ nₑ) (hintv : intv < ‖I‖) (hnₛ : ‖nₛ + ‖I‖‖ ≤ ‖L‖) :
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
      lt_of_lt_of_le (append_lt_sq_hash I L S (succ_le_iff_lt.mpr hintv) le_len_L (by simpa using pos_of_gt hintv)) hU,
      H',
      ext_append_lt I L S (succ_le_iff_lt.mpr hintv) (by simp),
      ext_append_last I L S (succ_le_iff_lt.mpr hintv) le_len_L ⟩

lemma Series.succ {iter n n' : M} (HT : Series U I L A iter n) (HS : Segment U L A (‖I‖ * iter) ‖I‖ n n') (hiter : iter < ‖I‖) :
    Series U I L A (iter + 1) n' := by
  have Hn : n ≤ ‖I‖ * iter := HT.le_add
  rcases HT with ⟨T, _, HT, Tₛ, rfl⟩
  let T' := append I L T (iter + 1) n'
  have hn'L : ‖n'‖ ≤ ‖L‖ := calc
    ‖n'‖ ≤ ‖T{L}[iter] + ‖I‖‖ := length_monotone HS.le_add
    _    ≤ ‖(iter + 1) * ‖I‖‖ := length_monotone <| by simp [add_mul, mul_comm iter, Hn]
    _    ≤ ‖‖I‖^2‖            := length_monotone <| by simp [sq]; exact mul_le_mul_right (succ_le_iff_lt.mpr hiter)
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
    lt_of_lt_of_le (append_lt_sq_hash I L T (succ_le_iff_lt.mpr hiter) hn'L (by simpa using pos_of_gt hiter)) hU,
    HT',
    Eq.trans (ext_append_lt I L T (succ_le_iff_lt.mpr hiter) (by simp)) Tₛ,
    hTlast ⟩

lemma div_mod_succ (a b : M) : ((a + 1) / b = a / b + 1 ∧ (a + 1) % b = 0 ∧ a % b + 1 = b) ∨ ((a + 1) / b = a / b ∧ (a + 1) % b = a % b + 1) := by
  rcases zero_le b with (rfl | pos)
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

lemma SeriesSegment.succ {k n : M} (hk : k < ‖I‖^2) (H : SeriesSegment U I L A k n) :
    SeriesSegment U I L A (k + 1) (n + fbit A k) := by
  have hhk : (k + 1)/‖I‖ ≤ ‖I‖ := by simpa using div_monotone (succ_le_iff_lt.mpr hk) ‖I‖
  have hnk : n ≤ k := H.le
  have Ipos : 0 < I := by simpa using pos_of_gt hk
  rcases H with ⟨nₘ, hnₘn, HT, HS⟩
  have hnₘL : ‖nₘ + ‖I‖‖ ≤ ‖L‖ := by
    have : k / ‖I‖ < ‖I‖ := div_lt_of_lt_mul (by simpa [sq] using hk)
    calc
      ‖nₘ + ‖I‖‖ ≤ ‖‖I‖ * (k / ‖I‖ + 1)‖ := length_monotone <| by simp [mul_add, HT.le_add]
      _        ≤ ‖‖I‖^2‖                 := length_monotone <| by simp[sq]; exact mul_le_mul_left (lt_iff_succ_le.mp this)
      _        ≤ ‖L‖                     := hIL
  rcases div_mod_succ k ‖I‖ with (⟨hdiv, hmodsucc, hmod⟩ | ⟨hdiv, hmod⟩)
  · have : Segment U L A (‖I‖ * (k / ‖I‖)) ‖I‖ nₘ (n + fbit A k) := by
      simpa [div_add_mod, hmod] using HS.succ hU (mod_lt _ $ by simp [Ipos]) hnₘL
    have : Series U I L A ((k + 1) / ‖I‖) (n + fbit A k) := by
      simpa [hdiv] using HT.succ hU hIL this (lt_iff_succ_le.mpr $ by simpa [hdiv] using hhk)
    exact ⟨n + fbit A k, by rfl, this, by
      simp [hmodsucc]; apply Segment.refl U L A
      · calc
          L # 1 ≤ I # L     := by rw [hash_comm L 1]; apply hash_monotone (pos_iff_one_le.mp Ipos) (by rfl)
          _     ≤ (I # L)^2 := by simp
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

/-- Define $I$, $L$, $U$ to satisfy the following:
  1. $I$, $L$, $U$ are polynomial of $A$.
  2. $(I \# L)^2 \le U$
  3. $\| \| I \|^2 \| \le \|L\|$
  4. $\| A \| < \|I\|^2$
-/

def polyI (A : M) : M := bexp (2 * A) (√‖A‖)

def polyL (A : M) : M := ‖polyI A‖ ^ 2

lemma len_polyI {A : M} (pos : 0 < A) : ‖polyI A‖ = √‖A‖ + 1 :=
  len_bexp (show √‖A‖ < ‖2 * A‖ from by simp [length_two_mul_of_pos pos, lt_succ_iff_le])

lemma polyI_le {A : M} (pos : 0 < A) : ‖A‖ < ‖polyI A‖ ^ 2 := by simp [len_polyI pos]

lemma two_add_two_eq_four : 2 + 2 = (4 : M) := by simp [←three_add_one_eq_four, ←two_add_one_eq_three, ←one_add_one_eq_two, add_assoc]

lemma four_mul_eq_two_mul_two_mul (a : M) : 4 * a = 2 * (2 * a) := by simp [←two_add_two_eq_four, add_mul, two_mul]

@[simp] lemma two_mul_sqrt_le_self (a : M) : 2 * √a ≤ a + 1 := le_trans (two_mul_le_sq_add_one (√a)) (by simp)

lemma four_mul_hash_self (a : M) : (4 * a) # (4 * a) ≤ (a # a) ^ (4 * 4) := calc
  (4 * a) # (4 * a) ≤ ((4 * a) # (2 * a)) ^ 2 := by simp [four_mul_eq_two_mul_two_mul, hash_two_mul_le_sq_hash]
  _                 ≤ ((4 * a) # a) ^ 4       := by simp [pow_four_eq_sq_sq, hash_two_mul_le_sq_hash]
  _                 ≤ ((a # (2 * a)) ^ 2) ^ 4 := by rw [hash_comm (4 * a) a]
                                                    simp [four_mul_eq_two_mul_two_mul, pow_four_eq_sq_sq, hash_two_mul_le_sq_hash]
  _                 ≤ ((a # a) ^ 4) ^ 4       := by simp [pow_four_eq_sq_sq, hash_two_mul_le_sq_hash]
  _                 ≤ (a # a) ^ (4 * 4)       := by simp [←pow_mul]

@[simp] lemma pos_sq_iff {a : M} : 0 < √a ↔ 0 < a :=
  ⟨fun h ↦ lt_of_lt_of_le h (by simp),
    by intro h; by_contra A; simp at A;
       simp [show a = 0 from by simpa [A] using sqrt_lt_sq a] at h⟩

@[simp] lemma pow_four_le_pow_four {a b : M} : a ^ 4 ≤ b ^ 4 ↔ a ≤ b := by simp [pow_four_eq_sq_sq]

lemma polyI_hash_self_polybounded {A : M} (pos : 0 < A) : (polyI A) # (polyI A) ≤ (2 * A + 1) ^ 4 := calc
  (polyI A) # (polyI A) = bexp ((polyI A) # (polyI A)) ((√‖A‖ + 1) ^ 2) := Eq.symm <| by simpa [sq, len_polyI pos] using bexp_eq_hash (polyI A) (polyI A)
  _                     ≤ bexp ((2 * A) # (2 * A)) ((2 * √‖A‖) ^ 2)     :=
    (bexp_monotone_le
      (by simp [length_hash, lt_succ_iff_le, ←sq, len_polyI pos])
      (by simp [length_hash, lt_succ_iff_le, ←sq, len_polyI pos, length_two_mul_of_pos pos])).mpr
    (by simp [two_mul, ←pos_iff_one_le, pos])
  _                     ≤ bexp ((2 * A) # (2 * A)) (4 * (√‖A‖) ^ 2)     := by simp [mul_pow, two_pow_two_eq_four]
  _                     ≤ (bexp (A # 1) ((√‖A‖) ^ 2)) ^ 4               := by { sorry }
  _                     ≤ (bexp (A # 1) ‖A‖) ^ 4                        := by
    simp; exact (bexp_monotone_le (by simp [length_hash, lt_succ_iff_le]) (by simp [length_hash, lt_succ_iff_le])).mpr (by simp)
  _                     = (A # 1) ^ 4                                   := by congr 1; simpa using bexp_eq_hash A 1
  _                     ≤ (2 * A + 1) ^ 4                               := by simp

lemma polyU {A : M} (pos : 0 < A) : (polyI A) # (polyL A) ≤ (2 * A + 1) ^ (4 * 4 * 4) := calc
  (polyI A) # (polyL A) ≤ (polyI A) # (3 * polyI A)         := hash_monotone (by rfl) (by simp [polyL, sq_len_le_three_mul])
  _                     ≤ (4 * polyI A) # (4 * polyI A)     := hash_monotone (le_mul_of_pos_left $ by simp) (mul_le_mul_right $ by simp [←three_add_one_eq_four])
  _                     ≤ ((polyI A) # (polyI A)) ^ (4 * 4) := four_mul_hash_self _
  _                     ≤ ((2 * A + 1) ^ 4) ^ (4 * 4)       := by simp [pow_mul, polyI_hash_self_polybounded pos]
  _                     = (2 * A + 1) ^ (4 * 4 * 4)         := by simp [←pow_mul]

/--/
lemma SeriesSegment.exists {k : M} (hk : k < ‖I‖^2) : ∃ n, SeriesSegment U I L A k n := by
  suffices : ∃ n ≤ k, SeriesSegment U I L A k n
  · rcases this with ⟨n, _, h⟩; exact ⟨n, h⟩
  revert hk
  induction k using hierarchy_induction_sigma₀
  · sorry -- simp [SeriesSegment, Segment, Series, IsSegment, IsSeries]
  case zero =>
    intro _
    exact ⟨0, by rfl, SeriesSegment.zero $ lt_of_lt_of_le (by simp) hU⟩
  case succ k IH =>
    intro hk
    rcases IH (lt_of_le_of_lt (by simp) hk) with ⟨n, hn, Hn⟩
    exact ⟨n + fbit A k, add_le_add hn (by simp), Hn.succ hU hIL Ipos (lt_of_le_of_lt (by simp) hk)⟩

lemma SeriesSegment.le_len_self {k : M} (hk : k < ‖I‖^2) (H : SeriesSegment U I L A k n) : n ≤ ‖A‖ := by
  revert hk H n
  suffices : ∀ k, ∀ n ≤ k, SeriesSegment U I L A k n →


lemma nuonAux_exists_unique {k : M} (hk : k < ‖I‖^2) : ∃ n, SeriesSegment U I L A k n := by


end


end Nuon

end Model

end

end Arith

end LO.FirstOrder
