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

/-- The letterless formula `∼⋀_{n ∉ X} TBB n` for a cofinite `X`. -/
noncomputable def LetterlessFormula.betaMinus (X : Set ℕ) (hX : Xᶜ.Finite) : LetterlessFormula :=
  ∼(⩕ n ∈ hX.toFinset, TBB n)

noncomputable abbrev Logic.GLBeta {α : Type*} (X : Set ℕ) (hX : Xᶜ.Finite) : Logic α :=
  𝐆𝐋 +ᴸ {(betaMinus X hX).lift}

notation "𝐆𝐋β" => Logic.GLBeta

variable {α : Type*} {X : Set ℕ} {hX : Xᶜ.Finite}

namespace LetterlessFormula

@[simp]
lemma spectrum_betaMinus : spectrum (betaMinus X hX) = Xᶜ := by
  ext n;
  simp [betaMinus];

@[simp]
lemma trace_betaMinus : trace (betaMinus X hX) = X := by
  simp [trace];

end LetterlessFormula

lemma Logic.GLBeta.eq_sumQuasiNormal_lift :
    (𝐆𝐋β X hX : Logic α) = (𝐆𝐋 +ᴸ LetterlessFormulaSet.lift {betaMinus X hX}) := by
  simp;

end FFL.ProvabilityLogic

end
