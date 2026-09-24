module

public import Foundation.ProvabilityLogic.Kripke.Rank

/-!
# Finite line models
-/

@[expose] public section

namespace FFL.ProvabilityLogic.Kripke

open Model Model.World

/-- The descending chain `n ≻ n - 1 ≻ ⋯ ≻ 0` on `Fin (n + 1)`, with every atom false. -/
abbrev finiteLineModel (n : ℕ) (α : Type*) : Model (Fin (n + 1)) α where
  Rel' x y := y < x
  Val' _ _ := False

namespace finiteLineModel

variable {n : ℕ} {α : Type*}

instance : (finiteLineModel n α).IsFiniteGL where
  trans _ _ _ h₁ h₂ := lt_trans h₂ h₁
  irrefl _ := lt_irrefl _

@[simp]
lemma rank_eq (x : (finiteLineModel n α).World) : x.rank = x := by
  obtain ⟨k, hk⟩ := x;
  induction k using Nat.strong_induction_on with
  | h k ih =>
    apply le_antisymm;
    · apply cwfHeight_le;
      rintro ⟨l, hl⟩ (h : l < k);
      exact (ih l h hl).trans_lt h;
    · rcases k with _ | k;
      · simp;
      · have h : (finiteLineModel n α).Rel ⟨k + 1, hk⟩ ⟨k, by omega⟩ := Nat.lt_add_one k;
        have := rank_lt_of_rel h;
        rw [ih k (by omega) (by omega)] at this;
        exact this;

end finiteLineModel

end FFL.ProvabilityLogic.Kripke

end
