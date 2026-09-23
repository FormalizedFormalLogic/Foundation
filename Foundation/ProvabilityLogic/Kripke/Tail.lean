module

public import Foundation.ProvabilityLogic.Kripke.RootedModel
public import Mathlib.Data.ENat.Basic

/-!
# Tails

## References

- [Vis84]
-/

@[expose] public section

namespace FFL.ProvabilityLogic.Kripke

open Model Model.World

variable {κ α : Type*} [Nonempty κ]

namespace RootedModel

variable (M : RootedModel κ α)

/-- `M` below which a descending chain of copies of its root, indexed by `ℕ∞`, is attached;
the top `⊤` of the chain is the new root. -/
def toTail : RootedModel (κ ⊕ ℕ∞) α where
  Rel' x y := match x, y with
    | .inl x, .inl y => M.Rel x y
    | .inl _, .inr _ => False
    | .inr _, .inl _ => True
    | .inr i, .inr j => j < i
  Val' x a := match x with
    | .inl x => M.Val x a
    | .inr _ => M.Val M.root a
  root := .inr ⊤
  root_rel x hx := by
    rcases x with x | i;
    . trivial;
    . exact lt_top_iff_ne_top.mpr (by simpa using hx);

namespace toTail

variable {M} {x y : M.World} {i j : ℕ∞} {A : Formula α}

@[simp, grind =] lemma rel_inl_inl : M.toTail.Rel (.inl x) (.inl y) ↔ M.Rel x y := Iff.rfl

@[simp, grind .] lemma not_rel_inl_inr : ¬M.toTail.Rel (.inl x) (.inr i) := id

@[simp, grind .] lemma rel_inr_inl : M.toTail.Rel (.inr i) (.inl x) := trivial

@[simp, grind =] lemma rel_inr_inr : M.toTail.Rel (.inr i) (.inr j) ↔ j < i := Iff.rfl

instance [IsTrans _ M.Rel] : IsTrans _ M.toTail.Rel where
  trans x y z := by
    rcases x with x | i <;> rcases y with y | j <;> rcases z with z | k <;>
    simp only [rel_inl_inl, rel_inr_inr, rel_inr_inl, not_rel_inl_inr, IsEmpty.forall_iff,
      implies_true, forall_const];
    . exact IsTrans.trans _ _ _;
    . exact fun h₁ h₂ ↦ h₂.trans h₁;

instance [IsConverseWellFounded _ M.Rel] : IsConverseWellFounded _ M.toTail.Rel where
  cwf := by
    have hinl : ∀ x : M.World, Acc (flip M.toTail.Rel) (.inl x) := by
      intro x;
      induction x using WellFounded.induction IsConverseWellFounded.cwf (r := flip M.Rel) with
      | h x ih =>
        constructor;
        rintro (y | j) h;
        . exact ih y h;
        . exact absurd h not_rel_inl_inr;
    constructor;
    rintro (x | i);
    . exact hinl x;
    . induction i using WellFoundedLT.induction with
      | ind i ih =>
        constructor;
        rintro (y | j) h;
        . exact hinl y;
        . exact ih j h;

instance [M.IsGL] : M.toTail.IsGL where

lemma forces_inl : Sum.inl x ⊩[M.toTail.toModel] A ↔ x ⊩[M.toModel] A := by
  induction A generalizing x with
  | atom | falsum => rfl;
  | imp A B ihA ihB => exact imp_congr ihA ihB;
  | box A ih =>
    constructor;
    . intro h y Rxy;
      exact ih.mp (h (.inl y) Rxy);
    . rintro h (y | j) Rxy;
      . exact ih.mpr (h y Rxy);
      . exact absurd Rxy not_rel_inl_inr;

/-- If the root of `M` forces `□B 🡒 B` for all `□B ∈ Γ`, then it agrees with every finite point
of the chain on `Γ`. -/
lemma forces_inr_iff [DecidableEq α] {Γ : FormulaFinset α}
    (hΓ : ∀ B ∈ Γ, B.subfmls ⊆ Γ) (hroot : ∀ B, □B ∈ Γ → M.root ⊩[M.toModel] □B 🡒 B)
    (hA : A ∈ Γ) (n : ℕ) : Sum.inr (n : ℕ∞) ⊩[M.toTail.toModel] A ↔ M.root ⊩[M.toModel] A := by
  induction A generalizing n with
  | atom | falsum => rfl;
  | imp B C ihB ihC =>
    exact imp_congr (ihB (hΓ _ hA (by grind)) n) (ihC (hΓ _ hA (by grind)) n);
  | box B ih =>
    have hB : B ∈ Γ := hΓ _ hA (by grind);
    constructor;
    . intro h x Rrx;
      exact forces_inl.mp (h (.inl x) trivial);
    . rintro h (x | j) Rnx;
      . apply forces_inl.mpr;
        by_cases hx : x = M.root;
        . exact hx ▸ hroot B hA h;
        . exact h x (M.root_rel x hx);
      . obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt (rel_inr_inr.mp Rnx));
        exact (ih hB m).mpr (hroot B hA h);

lemma forces_inr_boxdotTranslate_iff (n : ℕ) :
    Sum.inr (n : ℕ∞) ⊩[M.toTail.toModel] Aᵇ ↔ M.root ⊩[M.toModel] Aᵇ := by
  induction A generalizing n with
  | atom | falsum => rfl;
  | imp B C ihB ihC => exact imp_congr (ihB n) (ihC n);
  | box B ih =>
    simp only [Formula.boxdotTranslate_box, forces_boxdot, ih n];
    apply and_congr_right;
    intro hB;
    constructor;
    . intro h x _;
      exact forces_inl.mp (h (.inl x) trivial);
    . rintro h (x | j) Rnx;
      . apply forces_inl.mpr;
        by_cases hx : x = M.root;
        . exact hx ▸ hB;
        . exact h x (M.root_rel x hx);
      . obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt (rel_inr_inr.mp Rnx));
        exact (ih m).mpr hB;

end toTail

end RootedModel

end FFL.ProvabilityLogic.Kripke

end
