module

public import Foundation.ProvabilityLogic.GL.Letterless

/-!
# The logics `GLβ`

## References

- [Art86]
- [Bek90]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Formula LetterlessFormula

/-- The formula `∼⋀_{n ∉ X} alpha n` for a cofinite `X`. -/
noncomputable def Formula.beta {α : Type*} (X : Set ℕ) (hX : Xᶜ.Finite) : Formula α :=
  ∼(⩕ n ∈ hX.toFinset, alpha n)

noncomputable abbrev Logic.GLBeta {α : Type*} (X : Set ℕ) (hX : Xᶜ.Finite) : Logic α :=
  𝐆𝐋 +ᴸ {beta X hX}

notation "𝐆𝐋β" => Logic.GLBeta

variable {α : Type*} {X : Set ℕ} {hX : Xᶜ.Finite}

namespace LetterlessFormula

@[simp, grind =] lemma lift_beta : lift (beta X hX) = (beta X hX : Formula α) := by
  simp [beta, lift_neg, lift_conj'];

@[simp]
lemma spectrum_beta : spectrum (beta X hX) = Xᶜ := by
  ext n;
  simp [beta];

@[simp]
lemma trace_beta : trace (beta X hX) = X := by
  simp [trace];

end LetterlessFormula

lemma Logic.GLBeta.eq_sumQuasiNormal_lift :
    (𝐆𝐋β X hX : Logic α) = (𝐆𝐋 +ᴸ LetterlessFormulaSet.lift {beta X hX}) := by
  simp;

end FFL.ProvabilityLogic

end
