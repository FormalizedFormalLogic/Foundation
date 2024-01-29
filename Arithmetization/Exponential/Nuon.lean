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

def ext (I L S i : M) : M := S / bexp (I # L) (i * ‖L‖) % (L # 1)

local notation S "{" I ", " L "}[" i "]" => ext I L S i

-- lemma ext_graph (I L S i y : M) : y = S{I, L}[i] ↔ ((‖I‖ < i ∨ ‖S‖ ≤ i * ‖L‖) ∧ y = 0) ∨ (∃ b ≤ S, Exp (i * ‖L‖) b ∧ y = S / b % (L # 1)) := by
--   constructor
--   · rintro rfl

lemma ext_add_of_dvd_sq_right {I L i S₁ S₂ p : M} (hi : i ≤ ‖I‖)
    (pp : Pow2 p) (h : (i + 1) * ‖L‖ ≤ log p) : (S₁ + S₂ * p){I, L}[i] = S₁{I, L}[i] := by
  have : Exp ((i + 1) * ‖L‖) (bexp (I # L) (i * ‖L‖) * L # 1) := by
    simp [add_mul]
    exact Exp.add_mul
      (by simp [mul_len_lt_len_hash hi])
      (by simpa using exp_hash L 1)
  have : bexp (I # L) (i * ‖L‖) * L # 1 ∣ p :=
    Pow2.dvd_of_le (by simp; apply bexp_pow2; simp [mul_len_lt_len_hash hi]) pp (this.monotone_le (exp_of_pow2 pp) h)
  rcases this with ⟨p, rfl⟩
  simp [ext, mul_comm S₂, mul_assoc]
  have : 0 < bexp (I # L) (i * ‖L‖) := bexp_pos (by simp [mul_len_lt_len_hash hi])
  simp [div_add_mul_self', this]

def append (I L S i X : M) : M := S % bexp (I # L) (i * ‖L‖) + X * bexp (I # L) (i * ‖L‖)

lemma append_lt_hash (S : M) {i X I L} (hi : i ≤ ‖I‖) (hx : X ≤ L) : append I L S i X < (L + 1) * I # L := calc
  append I L S i X < (X + 1) * bexp (I # L) (i * ‖L‖)   := by simp [append, add_mul, add_comm]
                                                              exact mod_lt _ (bexp_pos $ mul_len_lt_len_hash hi)
  _                ≤ (L + 1) * bexp (I # L) (i * ‖L‖)   := mul_le_mul_right (by simp [hx])
  _                ≤ (L + 1) * bexp (I # L) (‖I‖ * ‖L‖) := mul_le_mul_left ((bexp_monotone_le (mul_len_lt_len_hash hi) (by simp [length_hash])).mpr (mul_le_mul_right hi))
  _                = (L + 1) * I # L                    := by congr 1; exact bexp_eq_of_exp (by simp [length_hash]) (exp_hash _ _)

lemma ext_append_last (S : M) {i X I L} (hi : i ≤ ‖I‖) (hx : X ≤ L) : (append I L S i X){I, L}[i] = X := by
  have he : Exp (i * ‖L‖) (bexp (I # L) (i * ‖L‖)) := by simp [mul_len_lt_len_hash hi]
  have : X < L # 1 := lt_of_le_of_lt hx (by simp)
  simp [ext, append, div_add_mul_self _ _ he.range_pos, this]

lemma ext_append_lt (S : M) {i j X I L} (hi : i ≤ ‖I‖) (hij : j < i) :
    (append I L S i X){I, L}[j] = S{I, L}[j] :=
  let Q := bexp (I # L) (i * ‖L‖)
  have pq : Pow2 Q := bexp_pow2 (by simp [mul_len_lt_len_hash hi])
  have hq : (j + 1) * ‖L‖ ≤ log Q := by simp [log_bexp (mul_len_lt_len_hash hi)]; exact mul_le_mul_right' (lt_iff_succ_le.mp hij) _
  calc
    (append I L S i X){I, L}[j] = (S % Q + X * Q){I, L}[j]       := rfl
    _                           = (S % Q){I, L}[j]               := ext_add_of_dvd_sq_right (le_trans (le_of_lt hij) hi) pq hq
    _                           = (S % Q + (S / Q) * Q){I, L}[j] := Eq.symm <| ext_add_of_dvd_sq_right (le_trans (le_of_lt hij) hi) pq hq
    _                           = S{I, L}[j]                     := by rw [mul_comm, add_comm, div_add_mod]

variable {L A : M}

def IsNuonIntvSeq (I L A start intv S : M) : Prop := ∀ i < intv, S{I, L}[i + 1] = S{I, L}[i] + fbit A (start + i)

def NuonIntv (U I L A start intv nₛ nₑ : M) : Prop := ∃ S < U, IsNuonIntvSeq I L A start intv S ∧ S{I, L}[0] = nₛ ∧ S{I, L}[intv] = nₑ

def IsNuonsSeq (U I L A cycle T : M) : Prop := ∀ l < cycle, NuonIntv U I L A (l * ‖I‖) ‖I‖ (T{I, L}[l]) (T{I, L}[l + 1])

def NuonCycle (U I L A cycle n : M) : Prop := ∃ T < U, IsNuonsSeq U I L A cycle T ∧ T{I, L}[0] = 0 ∧ T{I, L}[cycle] = n

def NuonPart (U I L A k n : M) : Prop := ∃ nₖ, NuonCycle U I L A (k / ‖I‖) nₖ ∧ NuonIntv U I L A (‖I‖ * k / ‖I‖) (k % ‖I‖) nₖ n

/--/
def Nuon₀ (K A n : M) : Prop := NuonIntv K A 0 ‖A‖ 0 n





def Nuon₁ (A n : M) : Prop := NuonIntv A A 0 ‖A‖ 0 n



end Nuon





namespace Nuon



end Nuon



end Model

end

end Arith

end LO.FirstOrder
