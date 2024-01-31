import Arithmetization.Exponential.Log

namespace LO.FirstOrder

namespace Arith

/-- ∀ x, ∃ y, 2^{|x|^2} = y-/
def omega₁ : Sentence ℒₒᵣ := “∀ ∃ ∃[#0 < #2 + 1] (!Model.binarylengthdef [#0, #2] ∧ !Model.Exp.def [#0*#0, #1])”

inductive Theory.Omega₁ : Theory ℒₒᵣ where
  | omega : Theory.Omega₁ omega₁

notation "𝛀₁" => Theory.Omega₁

@[simp] lemma Omega₁.mem_iff {σ} : σ ∈ 𝛀₁ ↔ σ = omega₁ :=
  ⟨by rintro ⟨⟩; rfl, by rintro rfl; exact Theory.Omega₁.omega⟩

noncomputable section

namespace Model

variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [𝐏𝐀⁻.Mod M]

lemma models_Omega₁_iff [𝐈𝚺₀.Mod M] : M ⊧ₘ omega₁ ↔ ∀ x : M, ∃ y, Exp (‖x‖^2) y := by
  simp [models_def, omega₁, length_defined.pval, Exp.defined.pval, sq, ←le_iff_lt_succ]
  constructor
  · intro h x
    rcases h x with ⟨y, _, _, rfl, h⟩; exact ⟨y, h⟩
  · intro h x
    rcases h x with ⟨y, h⟩
    exact ⟨y, ‖x‖, by simp, rfl, h⟩

lemma sigma₁_omega₁ [𝐈𝚺₁.Mod M] : M ⊧ₘ omega₁ := models_Omega₁_iff.mpr (fun x ↦ Exp.range_exists (‖x‖^2))

instance [𝐈𝚺₁.Mod M] : 𝛀₁.Mod M := ⟨by intro _; simp; rintro rfl; exact sigma₁_omega₁⟩

variable [𝐈𝚺₀.Mod M] [𝛀₁.Mod M]

lemma exists_exp_sq_length (x : M) : ∃ y, Exp (‖x‖^2) y :=
  models_Omega₁_iff.mp (Theory.Mod.models M Theory.Omega₁.omega) x

lemma exists_unique_exp_sq_length (x : M) : ∃! y, Exp (‖x‖^2) y := by
  rcases exists_exp_sq_length x with ⟨y, h⟩
  exact ExistsUnique.intro y h (fun y' h' ↦ h'.uniq h)

lemma hash_exists_unique (x y : M) : ∃! z, Exp (‖x‖ * ‖y‖) z := by
  wlog le : x ≤ y
  · simpa [mul_comm] using this y x (le_of_not_ge le)
  rcases exists_exp_sq_length y with ⟨z, h⟩
  have : ‖x‖ * ‖y‖ < ‖z‖ :=
    lt_of_le_of_lt (by simp [sq]; exact mul_le_mul_right (length_monotone le)) h.lt_length
  have : Exp (‖x‖ * ‖y‖) (bexp z (‖x‖ * ‖y‖)) := exp_bexp_of_lt (a := z) (x := ‖x‖ * ‖y‖) this
  exact ExistsUnique.intro (bexp z (‖x‖ * ‖y‖)) this (fun z' H' ↦ H'.uniq this)

instance : Hash M := ⟨fun a b ↦ Classical.choose! (hash_exists_unique a b)⟩

lemma exp_hash (a b : M) : Exp (‖a‖ * ‖b‖) (a # b) := Classical.choose!_spec (hash_exists_unique a b)

lemma exp_hash_one (a : M) : Exp ‖a‖ (a # 1) := by simpa using exp_hash a 1

def hashdef : Σᴬ[0] 3 :=
  ⟨“∃[#0 < #2 + 1] ∃[#0 < #4 + 1] (!binarylengthdef [#1, #3] ∧ !binarylengthdef [#0, #4] ∧ !Exp.def [#1 * #0, #2])”, by simp⟩

lemma hash_defined : Σᴬ[0]-Function₂ (Hash.hash : M → M → M) hashdef := by
  intro v; simp[hashdef, length_defined.pval, Exp.defined.pval, ←le_iff_lt_succ]
  constructor
  · intro h; exact ⟨‖v 1‖, by simp, ‖v 2‖, by simp, rfl, rfl, by rw [h]; exact exp_hash _ _⟩
  · rintro ⟨_, _, _, _, rfl, rfl, h⟩; exact h.uniq (exp_hash (v 1) (v 2))

instance : DefinableFunction₂ b s (Hash.hash : M → M → M) := defined_to_with_param₀ _ hash_defined

@[simp] lemma hash_pow2 (a b : M) : Pow2 (a # b) := (exp_hash a b).range_pow2

@[simp] lemma hash_pos (a b : M) : 0 < a # b := (exp_hash a b).range_pos

@[simp] lemma hash_lt (a b : M) : ‖a‖ * ‖b‖ < a # b := (exp_hash a b).dom_lt_range

lemma length_hash (a b : M) : ‖a # b‖ = ‖a‖ * ‖b‖ + 1 := (exp_hash a b).length_eq

@[simp] lemma hash_zero_left (a : M) : 0 # a = 1 := (exp_hash 0 a).uniq (by simp)

@[simp] lemma hash_zero_right (a : M) : a # 0 = 1 := (exp_hash a 0).uniq (by simp)

lemma hash_comm (a b : M) : a # b = b # a := (exp_hash a b).uniq (by simpa [mul_comm] using exp_hash b a)

@[simp] lemma lt_hash_one_right (a : M) : a < a # 1 := by
  have : Exp ‖a‖ (a # 1) := by simpa using (exp_hash a 1)
  exact lt_exp_length this

@[simp] lemma lt_hash_one_righs (a : M) : a # 1 ≤ 2 * a + 1 := by
  rcases zero_le a with (rfl | pos)
  · simp
  · exact (le_iff_lt_length_of_exp (exp_hash a 1)).mpr (by
      simp [mul_comm 2 a]
      have : ‖a * 2 + 1‖ = ‖a‖ + 1 := by
        simpa using length_mul_pow2_add_of_lt pos (show Pow2 2 from by simp) one_lt_two
      simp [this])

lemma lt_hash_iff {a b c : M} : a < b # c ↔ ‖a‖ ≤ ‖b‖ * ‖c‖ := (exp_hash b c).lt_iff_len_le

lemma hash_le_iff {a b c : M} : b # c ≤ a ↔ ‖b‖ * ‖c‖ < ‖a‖ :=
  not_iff_not.mp <| by simp [lt_hash_iff]

lemma lt_hash_one_iff {a b : M} : a < b # 1 ↔ ‖a‖ ≤ ‖b‖ := by simpa using lt_hash_iff (a := a) (b := b) (c := 1)

lemma hash_monotone {a₁ a₂ b₁ b₂ : M} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) : a₁ # a₂ ≤ b₁ # b₂ :=
  (exp_hash a₁ a₂).monotone_le (exp_hash b₁ b₂) (mul_le_mul (length_monotone h₁) (length_monotone h₂) (by simp) (by simp))

lemma bexp_eq_hash (a b : M) : bexp (a # b) (‖a‖ * ‖b‖) = a # b := bexp_eq_of_exp (by simp [length_hash]) (exp_hash a b)

lemma hash_two_mul (a : M) {b} (pos : 0 < b) : a # (2 * b) = (a # b) * (a # 1) := by
  have h₁ : Exp (‖a‖ * ‖b‖ + ‖a‖) (a # (2 * b)) := by
    simpa [length_two_mul_of_pos pos, mul_add] using exp_hash a (2 * b)
  have h₂ : Exp (‖a‖ * ‖b‖ + ‖a‖) (a # b * a # 1) := (exp_hash a b).add_mul (exp_hash_one a)
  exact h₁.uniq h₂

lemma hash_two_mul_le_sq_hash (a b : M) : a # (2 * b) ≤ (a # b) ^ 2 := by
  rcases zero_le b with (rfl | pos)
  · simp
  · simp [hash_two_mul a pos, sq]
    exact hash_monotone (by rfl) (pos_iff_one_le.mp pos)


end Model

end

end Arith

end LO.FirstOrder
