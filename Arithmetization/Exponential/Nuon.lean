import Arithmetization.Exponential.Omega

namespace LO.FirstOrder

namespace Arith

noncomputable section

namespace Model

variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [𝐏𝐀⁻.Mod M] [𝐈𝚺₀.Mod M] [𝛀₁.Mod M]

namespace Nuon

@[simp] lemma llen_lt_len_hash_len (a : M) : ‖‖a‖‖ < ‖a # ‖a‖‖ := by
  simp [length_hash, lt_succ_iff_le]
  rcases zero_le ‖a‖ with (ha | pos)
  · simp [←ha]
  · exact le_mul_of_pos_left pos

lemma mul_llen_lt_len_hash_len {i a : M} (hi : i ≤ ‖a‖) : i * ‖‖a‖‖ < ‖a # ‖a‖‖ := by
  simp [length_hash, lt_succ_iff_le]; exact mul_le_mul_right' hi ‖‖a‖‖

def ext (a s i : M) : M := s / bexp (a # ‖a‖) (i * ‖‖a‖‖) % (‖a‖ # 1)

lemma ext_add_of_dvd_sq_right {i s₁ s₂ p : M} (hi : i ≤ ‖a‖)
    (pp : Pow2 p) (h : (i + 1) * ‖‖a‖‖ ≤ log p) :
    ext a (s₁ + s₂ * p) i = ext a s₁ i := by
  have : Exp ((i + 1) * ‖‖a‖‖) (bexp (a # ‖a‖) (i * ‖‖a‖‖) * ‖a‖ # 1) := by
    simp [add_mul]
    exact Exp.add_mul
      (by simp [mul_llen_lt_len_hash_len hi])
      (by simpa using exp_hash ‖a‖ 1)
  have : bexp (a # ‖a‖) (i * ‖‖a‖‖) * ‖a‖ # 1 ∣ p :=
    Pow2.dvd_of_le (by simp; apply bexp_pow2; simp [mul_llen_lt_len_hash_len hi]) pp (this.monotone_le (exp_of_pow2 pp) h)
  rcases this with ⟨p, rfl⟩
  simp [ext, mul_comm s₂, mul_assoc]
  have : 0 < bexp (a # ‖a‖) (i * ‖‖a‖‖) := bexp_pos (by simp [mul_llen_lt_len_hash_len hi])
  simp [div_add_mul_self', this]

def append (a s i x : M) : M := s % bexp (a # ‖a‖) (i * ‖‖a‖‖) + x * bexp (a # ‖a‖) (i * ‖‖a‖‖)

lemma append_lt_hash (s : M) {i x a} (hi : i ≤ ‖a‖) (hx : x ≤ ‖a‖) : append a s i x < 1 # ‖a‖ * a # ‖a‖ := calc
  append a s i x < (x + 1) * bexp (a # ‖a‖) (i * ‖‖a‖‖)                := by simp [append, add_mul, add_comm]
                                                                             exact mod_lt _ (bexp_pos $ mul_llen_lt_len_hash_len hi)
  _              ≤ (‖a‖ + 1) * bexp (a # ‖a‖) (i * ‖‖a‖‖)              := mul_le_mul_right (by simp [hx])
  _              ≤ bexp (a # ‖a‖) ‖‖a‖‖ * bexp (a # ‖a‖) (i * ‖‖a‖‖)   := mul_le_mul_right (by simp [succ_le_iff_lt]; apply lt_bexp_len (by simp))
  _              ≤ bexp (a # ‖a‖) ‖‖a‖‖ * bexp (a # ‖a‖) (‖a‖ * ‖‖a‖‖) := mul_le_mul_left
                                                                            ((bexp_monotone_le (mul_llen_lt_len_hash_len hi)
                                                                              (mul_llen_lt_len_hash_len $ by rfl)).mpr (mul_le_mul_right hi))
  _              = 1 # ‖a‖ * a # ‖a‖                                   := by congr 1
                                                                             · exact bexp_eq_of_exp (by simp) (by simpa using exp_hash 1 ‖a‖)
                                                                             · exact bexp_eq_of_exp (mul_llen_lt_len_hash_len $ by rfl) (exp_hash _ _)

lemma ext_append_last (s : M) {i x a} (hi : i ≤ ‖a‖) (hx : x ≤ ‖a‖) : ext a (append a s i x) i = x := by
  have he : Exp (i * ‖‖a‖‖) (bexp (a # ‖a‖) (i * ‖‖a‖‖)) := by simp [mul_llen_lt_len_hash_len hi]
  have : x < ‖a‖ # 1 := lt_of_le_of_lt hx (by simp)
  simp [ext, append, div_add_mul_self _ _ he.range_pos, this]

lemma ext_append_last_lt (s : M) {i j x a} (hi : i ≤ ‖a‖) (hij : j < i) :
    ext a (append a s i x) j = ext a s j :=
  let q := bexp (a # ‖a‖) (i * ‖‖a‖‖)
  have pq : Pow2 q := bexp_pow2 (by simp [mul_llen_lt_len_hash_len hi])
  have hq : (j + 1) * ‖‖a‖‖ ≤ log q := by simp [log_bexp (mul_llen_lt_len_hash_len hi)]; exact mul_le_mul_right' (lt_iff_succ_le.mp hij) _
  calc
    ext a (append a s i x) j = ext a (s % q + x * q) j       := rfl
    _                        = ext a (s % q) j               := ext_add_of_dvd_sq_right (le_trans (le_of_lt hij) hi) pq hq
    _                        = ext a (s % q + (s / q) * q) j := Eq.symm <| ext_add_of_dvd_sq_right (le_trans (le_of_lt hij) hi) pq hq
    _                        = ext a s j                     := by rw [mul_comm, add_comm, div_add_mod]

def IsNuonSeq (a s : M) : Prop := ext a s 0 = 0 ∧ ∀ i < ‖a‖, ext a s (i + 1) = ext a s i + fbit a i

def nuon (a n : M) : Prop := ∃ s, IsNuonSeq a s ∧ ext a s ‖a‖ = n

end Nuon





namespace Nuon



end Nuon



end Model

end

end Arith

end LO.FirstOrder
