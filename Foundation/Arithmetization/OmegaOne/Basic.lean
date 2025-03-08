import Foundation.Arithmetization.ISigmaZero.Exponential.Log

namespace LO.Arith

open FirstOrder FirstOrder.Arith FirstOrder.Theory

/-- ∀ x, ∃ y, 2^{|x|^2} = y-/
def _root_.LO.FirstOrder.Theory.OmegaOneAxiom : SyntacticFormula ℒₒᵣ := “∀ x, ∃ y, ∃ l <⁺ x, !lengthDef l x ∧ !exponentialDef (l * l) y”

inductive _root_.LO.FirstOrder.Theory.OmegaOne : Theory ℒₒᵣ where
  | omega : OmegaOne OmegaOneAxiom

notation "𝛀₁" => Theory.OmegaOne

@[simp] lemma _root_.LO.FirstOrder.Theory.OmegaOne.mem_iff {σ} : σ ∈ 𝛀₁ ↔ σ = OmegaOneAxiom :=
  ⟨by rintro ⟨⟩; rfl, by rintro rfl; exact Theory.OmegaOne.omega⟩

noncomputable section

variable {V : Type*} [ORingStruc V]

lemma models_Omega₁_iff [V ⊧ₘ* 𝐈𝚺₀] : V ⊧ₘ OmegaOneAxiom ↔ ∀ x : V, ∃ y, Exponential (‖x‖^2) y := by
  simp [models_def, OmegaOneAxiom, length_defined.df.iff, Exponential.defined.df.iff, sq, ←le_iff_lt_succ]

lemma sigma₁_omega₁ [V ⊧ₘ* 𝐈𝚺₁] : V ⊧ₘ OmegaOneAxiom := models_Omega₁_iff.mpr (fun x ↦ Exponential.range_exists (‖x‖^2))

instance [V ⊧ₘ* 𝐈𝚺₁] : V ⊧ₘ* 𝐈𝚺₀ + 𝛀₁ :=
  ModelsTheory.add_iff.mpr ⟨inferInstance, ⟨by intro _; simp; rintro rfl; exact sigma₁_omega₁⟩⟩

variable [V ⊧ₘ* 𝐈𝚺₀ + 𝛀₁]

instance : V ⊧ₘ* 𝐈𝚺₀ := ModelsTheory.of_add_left V 𝐈𝚺₀ 𝛀₁

instance : V ⊧ₘ* 𝛀₁ := ModelsTheory.of_add_right V 𝐈𝚺₀ 𝛀₁

lemma exists_exponential_sq_length (x : V) : ∃ y, Exponential (‖x‖^2) y :=
  models_Omega₁_iff.mp (ModelsTheory.models V Theory.OmegaOne.omega) x

lemma exists_unique_exponential_sq_length (x : V) : ∃! y, Exponential (‖x‖^2) y := by
  rcases exists_exponential_sq_length x with ⟨y, h⟩
  exact ExistsUnique.intro y h (fun y' h' ↦ h'.uniq h)

lemma hash_exists_unique (x y : V) : ∃! z, Exponential (‖x‖ * ‖y‖) z := by
  wlog le : x ≤ y
  · simpa [mul_comm] using this y x (le_of_not_ge le)
  rcases exists_exponential_sq_length y with ⟨z, h⟩
  have : ‖x‖ * ‖y‖ < ‖z‖ :=
    lt_of_le_of_lt (by simp [sq]; exact mul_le_mul_right (length_monotone le)) h.lt_length
  have : Exponential (‖x‖ * ‖y‖) (bexp z (‖x‖ * ‖y‖)) := exp_bexp_of_lt (a := z) (x := ‖x‖ * ‖y‖) this
  exact ExistsUnique.intro (bexp z (‖x‖ * ‖y‖)) this (fun z' H' ↦ H'.uniq this)

instance : Hash V := ⟨fun a b ↦ Classical.choose! (hash_exists_unique a b)⟩

lemma exponential_hash (a b : V) : Exponential (‖a‖ * ‖b‖) (a # b) := Classical.choose!_spec (hash_exists_unique a b)

lemma exponential_hash_one (a : V) : Exponential ‖a‖ (a # 1) := by simpa using exponential_hash a 1

def hashDef : 𝚺₀.Semisentence 3 := .mkSigma
  “z x y. ∃ lx <⁺ x, ∃ ly <⁺ y, !lengthDef lx x ∧ !lengthDef ly y ∧ !exponentialDef (lx * ly) z” (by simp)

lemma hash_defined : 𝚺₀-Function₂ (Hash.hash : V → V → V) via hashDef := by
  intro v; simp [hashDef, length_defined.df.iff, Exponential.defined.df.iff, ←le_iff_lt_succ]
  constructor
  · intro h; simp [h, exponential_hash]
  · rintro h; exact h.uniq (exponential_hash (v 1) (v 2))

instance hash_definable : 𝚺₀-Function₂ (Hash.hash : V → V → V) := hash_defined.to_definable

@[simp] lemma hash_pow2 (a b : V) : Pow2 (a # b) := (exponential_hash a b).range_pow2

@[simp] lemma hash_pos (a b : V) : 0 < a # b := (exponential_hash a b).range_pos

@[simp] lemma hash_lt (a b : V) : ‖a‖ * ‖b‖ < a # b := (exponential_hash a b).lt

lemma length_hash (a b : V) : ‖a # b‖ = ‖a‖ * ‖b‖ + 1 := (exponential_hash a b).length_eq

@[simp] lemma hash_zero_left (a : V) : 0 # a = 1 := (exponential_hash 0 a).uniq (by simp)

@[simp] lemma hash_zero_right (a : V) : a # 0 = 1 := (exponential_hash a 0).uniq (by simp)

lemma hash_comm (a b : V) : a # b = b # a := (exponential_hash a b).uniq (by simpa [mul_comm] using exponential_hash b a)

@[simp] lemma lt_hash_one_right (a : V) : a < a # 1 := by
  have : Exponential ‖a‖ (a # 1) := by simpa using (exponential_hash a 1)
  exact lt_exponential_length this

@[simp] lemma lt_hash_one_righs (a : V) : a # 1 ≤ 2 * a + 1 := by
  rcases zero_le a with (rfl | pos)
  · simp
  · exact (le_iff_lt_length_of_exp (exponential_hash a 1)).mpr (by
      simp [mul_comm 2 a]
      have : ‖a * 2 + 1‖ = ‖a‖ + 1 := by
        simpa using length_mul_pow2_add_of_lt pos (show Pow2 2 from by simp) one_lt_two
      simp [this])

lemma lt_hash_iff {a b c : V} : a < b # c ↔ ‖a‖ ≤ ‖b‖ * ‖c‖ := (exponential_hash b c).lt_iff_len_le

lemma hash_le_iff {a b c : V} : b # c ≤ a ↔ ‖b‖ * ‖c‖ < ‖a‖ :=
  not_iff_not.mp <| by simp [lt_hash_iff]

lemma lt_hash_one_iff {a b : V} : a < b # 1 ↔ ‖a‖ ≤ ‖b‖ := by simpa using lt_hash_iff (a := a) (b := b) (c := 1)

lemma hash_monotone {a₁ a₂ b₁ b₂ : V} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) : a₁ # a₂ ≤ b₁ # b₂ :=
  (exponential_hash a₁ a₂).monotone_le (exponential_hash b₁ b₂) (mul_le_mul (length_monotone h₁) (length_monotone h₂) (by simp) (by simp))

lemma bexp_eq_hash (a b : V) : bexp (a # b) (‖a‖ * ‖b‖) = a # b := bexp_eq_of_exp (by simp [length_hash]) (exponential_hash a b)

lemma hash_two_mul (a : V) {b} (pos : 0 < b) : a # (2 * b) = (a # b) * (a # 1) := by
  have h₁ : Exponential (‖a‖ * ‖b‖ + ‖a‖) (a # (2 * b)) := by
    simpa [length_two_mul_of_pos pos, mul_add] using exponential_hash a (2 * b)
  have h₂ : Exponential (‖a‖ * ‖b‖ + ‖a‖) (a # b * a # 1) := (exponential_hash a b).add_mul (exponential_hash_one a)
  exact h₁.uniq h₂

lemma hash_two_mul_le_sq_hash (a b : V) : a # (2 * b) ≤ (a # b) ^ 2 := by
  rcases zero_le b with (rfl | pos)
  · simp
  · simp [hash_two_mul a pos, sq]
    exact hash_monotone (by rfl) (pos_iff_one_le.mp pos)

end

end LO.Arith

namespace LO.FirstOrder.Arith

instance : 𝐈𝚺₀ ⪯ 𝐈𝚺₀ + 𝛀₁ := inferInstance

instance : 𝐈𝚺₀ + 𝛀₁ ⪯ 𝐈𝚺₁ := oRing_weakerThan_of.{0} _ _ fun _ _ _ ↦ inferInstance

instance : ℕ ⊧ₘ* 𝐈𝚺₀ + 𝛀₁ := inferInstance

end LO.FirstOrder.Arith
