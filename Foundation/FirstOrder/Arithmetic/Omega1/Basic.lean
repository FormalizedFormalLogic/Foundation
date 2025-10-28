import Foundation.FirstOrder.Arithmetic.Exponential

/-!
# Theory $\mathsf{I}\Sigma_0 + \Omega_1$

-/

namespace LO.FirstOrder.Arithmetic

/-- ∀ x, ∃ y, 2^{|x|^2} = y-/
def _root_.LO.Omega1.omega1 : Sentence ℒₒᵣ := “∀ x, ∃ y, ∃ l <⁺ x, !lengthDef l x ∧ !exponentialDef (l * l) y”

inductive _root_.LO.Omega1 : Theory ℒₒᵣ where
  | omega : Omega1 Omega1.omega1

notation "𝝮₁" => Omega1

@[simp] lemma _root_.LO.FirstOrder.Theory.OmegaOne.mem_iff {σ} : σ ∈ 𝝮₁ ↔ σ = Omega1.omega1 :=
  ⟨by rintro ⟨⟩; rfl, by rintro rfl; exact Omega1.omega⟩

noncomputable section

variable {V : Type*} [ORingStructure V]

lemma models_Omega1_iff [V ⊧ₘ* 𝗜𝚺₀] : V ⊧ₘ Omega1.omega1 ↔ ∀ x : V, ∃ y, Exponential (‖x‖^2) y := by
  simp [models_iff, Omega1.omega1, sq]

lemma omega1_of_ISigma1 [V ⊧ₘ* 𝗜𝚺₁] : V ⊧ₘ Omega1.omega1 := models_Omega1_iff.mpr (fun x ↦ Exponential.range_exists (‖x‖^2))

instance [V ⊧ₘ* 𝗜𝚺₁] : V ⊧ₘ* 𝗜𝚺₀ + 𝝮₁ :=
  ModelsTheory.add_iff.mpr
    ⟨inferInstance, ⟨by intro _; simp only [Theory.OmegaOne.mem_iff]; rintro rfl; exact omega1_of_ISigma1⟩⟩

variable [V ⊧ₘ* 𝗜𝚺₀ + 𝝮₁]

instance : V ⊧ₘ* 𝗜𝚺₀ := ModelsTheory.of_add_left V 𝗜𝚺₀ 𝝮₁

instance : V ⊧ₘ* 𝝮₁ := ModelsTheory.of_add_right V 𝗜𝚺₀ 𝝮₁

lemma exists_exponential_sq_length (x : V) : ∃ y, Exponential (‖x‖^2) y :=
  models_Omega1_iff.mp (ModelsTheory.models V Omega1.omega) x

lemma exists_unique_exponential_sq_length (x : V) : ∃! y, Exponential (‖x‖^2) y := by
  rcases exists_exponential_sq_length x with ⟨y, h⟩
  exact ExistsUnique.intro y h (fun y' h' ↦ h'.uniq h)

lemma smash_exists_unique (x y : V) : ∃! z, Exponential (‖x‖ * ‖y‖) z := by
  wlog le : x ≤ y
  · simpa [mul_comm] using this y x (le_of_not_ge le)
  rcases exists_exponential_sq_length y with ⟨z, h⟩
  have : ‖x‖ * ‖y‖ < ‖z‖ :=
    lt_of_le_of_lt (by simpa [sq] using mul_le_mul_right (length_monotone le)) h.lt_length
  have : Exponential (‖x‖ * ‖y‖) (bexp z (‖x‖ * ‖y‖)) := exp_bexp_of_lt (a := z) (x := ‖x‖ * ‖y‖) this
  exact ExistsUnique.intro (bexp z (‖x‖ * ‖y‖)) this (fun z' H' ↦ H'.uniq this)

instance : Smash V := ⟨fun a b ↦ Classical.choose! (smash_exists_unique a b)⟩

lemma exponential_smash (a b : V) : Exponential (‖a‖ * ‖b‖) (a ⨳ b) := Classical.choose!_spec (smash_exists_unique a b)

lemma exponential_smash_one (a : V) : Exponential ‖a‖ (a ⨳ 1) := by simpa using exponential_smash a 1

def smashDef : 𝚺₀.Semisentence 3 := .mkSigma
  “z x y. ∃ lx <⁺ x, ∃ ly <⁺ y, !lengthDef lx x ∧ !lengthDef ly y ∧ !exponentialDef (lx * ly) z”

instance smash_defined : 𝚺₀-Function₂ (Smash.smash : V → V → V) via smashDef := .mk <| fun v ↦ by
  suffices Exponential (‖v 1‖ * ‖v 2‖) (v 0) ↔ v 0 = v 1 ⨳ v 2 by
    simpa [smashDef, ←le_iff_lt_succ]
  constructor
  · rintro h; exact h.uniq (exponential_smash (v 1) (v 2))
  · intro h; simp [h, exponential_smash]

instance smash_definable : 𝚺₀-Function₂ (Smash.smash : V → V → V) := smash_defined.to_definable

@[simp] lemma smash_pow2 (a b : V) : Pow2 (a ⨳ b) := (exponential_smash a b).range_pow2

@[simp] lemma smash_pos (a b : V) : 0 < a ⨳ b := (exponential_smash a b).range_pos

@[simp] lemma smash_lt (a b : V) : ‖a‖ * ‖b‖ < a ⨳ b := (exponential_smash a b).lt

lemma length_smash (a b : V) : ‖a ⨳ b‖ = ‖a‖ * ‖b‖ + 1 := (exponential_smash a b).length_eq

@[simp] lemma smash_zero_left (a : V) : 0 ⨳ a = 1 := (exponential_smash 0 a).uniq (by simp)

@[simp] lemma smash_zero_right (a : V) : a ⨳ 0 = 1 := (exponential_smash a 0).uniq (by simp)

lemma smash_comm (a b : V) : a ⨳ b = b ⨳ a := (exponential_smash a b).uniq (by simpa [mul_comm] using exponential_smash b a)

@[simp] lemma lt_smash_one_right (a : V) : a < a ⨳ 1 := by
  have : Exponential ‖a‖ (a ⨳ 1) := by simpa using (exponential_smash a 1)
  exact lt_exponential_length this

@[simp] lemma lt_smash_one_righs (a : V) : a ⨳ 1 ≤ 2 * a + 1 := by
  rcases zero_le a with (rfl | pos)
  · simp
  · exact (le_iff_lt_length_of_exp (exponential_smash a 1)).mpr (by
      suffices ‖a‖ < ‖a * 2 + 1‖ by simpa [mul_comm 2 a]
      have : ‖a * 2 + 1‖ = ‖a‖ + 1 := by
        simpa using length_mul_pow2_add_of_lt pos (show Pow2 2 from by simp) one_lt_two
      simp [this])

lemma lt_smash_iff {a b c : V} : a < b ⨳ c ↔ ‖a‖ ≤ ‖b‖ * ‖c‖ := (exponential_smash b c).lt_iff_len_le

lemma smash_le_iff {a b c : V} : b ⨳ c ≤ a ↔ ‖b‖ * ‖c‖ < ‖a‖ :=
  not_iff_not.mp <| by simp [lt_smash_iff]

lemma lt_smash_one_iff {a b : V} : a < b ⨳ 1 ↔ ‖a‖ ≤ ‖b‖ := by simpa using lt_smash_iff (a := a) (b := b) (c := 1)

lemma smash_monotone {a₁ a₂ b₁ b₂ : V} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) : a₁ ⨳ a₂ ≤ b₁ ⨳ b₂ :=
  (exponential_smash a₁ a₂).monotone_le (exponential_smash b₁ b₂) (mul_le_mul (length_monotone h₁) (length_monotone h₂) (by simp) (by simp))

lemma bexp_eq_smash (a b : V) : bexp (a ⨳ b) (‖a‖ * ‖b‖) = a ⨳ b := bexp_eq_of_exp (by simp [length_smash]) (exponential_smash a b)

lemma smash_two_mul (a : V) {b} (pos : 0 < b) : a ⨳ (2 * b) = (a ⨳ b) * (a ⨳ 1) := by
  have h₁ : Exponential (‖a‖ * ‖b‖ + ‖a‖) (a ⨳ (2 * b)) := by
    simpa [length_two_mul_of_pos pos, mul_add] using exponential_smash a (2 * b)
  have h₂ : Exponential (‖a‖ * ‖b‖ + ‖a‖) (a ⨳ b * a ⨳ 1) := (exponential_smash a b).add_mul (exponential_smash_one a)
  exact h₁.uniq h₂

lemma smash_two_mul_le_sq_smash (a b : V) : a ⨳ (2 * b) ≤ (a ⨳ b) ^ 2 := by
  rcases zero_le b with (rfl | pos)
  · simp
  · simpa [smash_two_mul a pos, sq]
    using smash_monotone (by rfl) (pos_iff_one_le.mp pos)

end

instance : 𝗜𝚺₀ ⪯ 𝗜𝚺₀ + 𝝮₁ := inferInstance

instance : 𝗜𝚺₀ + 𝝮₁ ⪯ 𝗜𝚺₁ := weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance

instance : ℕ ⊧ₘ* 𝗜𝚺₀ + 𝝮₁ := inferInstance

end LO.FirstOrder.Arithmetic
