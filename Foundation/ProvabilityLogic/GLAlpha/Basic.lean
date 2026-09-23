module

public import Foundation.ProvabilityLogic.GL.Letterless

/-!
# The logics `GLα`

## References

- [Art86]
- [Bek90]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Formula LetterlessFormula

abbrev Logic.GLAlpha {α : Type*} (X : Set ℕ) : Logic α := 𝐆𝐋 +ᴸ TBB '' X

notation "𝐆𝐋α" => Logic.GLAlpha

namespace Logic.GLAlpha

variable {α : Type*} {X : Set ℕ}

lemma eq_sumQuasiNormal_lift :
    (𝐆𝐋α X : Logic α) = (𝐆𝐋 +ᴸ LetterlessFormulaSet.lift (TBB '' X)) := by
  simp [Set.image_image];

@[simp]
lemma spectrum_TBB_image : LetterlessFormulaSet.spectrum (TBB '' X) = Xᶜ := by
  ext n;
  suffices (∀ i ∈ X, n ≠ i) ↔ n ∉ X by simpa [LetterlessFormulaSet.spectrum];
  grind;

@[simp]
lemma trace_TBB_image : LetterlessFormulaSet.trace (TBB '' X) = X := by
  simp [LetterlessFormulaSet.trace];

end Logic.GLAlpha

end FFL.ProvabilityLogic

end
