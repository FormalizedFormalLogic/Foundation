module

public import Foundation.ProvabilityLogic.Kripke.RootedModel
public import Mathlib.Data.ENat.Basic

/-!
# Tails

## References

- [Vis84]
- [KKIM25]
-/

@[expose] public section

namespace FFL.ProvabilityLogic.Kripke

open Model Model.World

variable {κ α : Type*} [Nonempty κ]

namespace Model

variable (M : Model κ α)

/-- `M` below which a descending chain indexed by `ℕ∞` is attached, the point `i` of the chain
carrying the valuation `V i`; the top `⊤` of the chain is the root.

- [KKIM25]
-/
def toFreeTail (V : ℕ∞ → α → Prop) : RootedModel (κ ⊕ ℕ∞) α where
  Rel' x y := match x, y with
    | .inl x, .inl y => M.Rel x y
    | .inl _, .inr _ => False
    | .inr _, .inl _ => True
    | .inr i, .inr j => j < i
  Val' x a := match x with
    | .inl x => M.Val x a
    | .inr i => V i a
  root := .inr ⊤
  root_rel x hx := by
    rcases x with x | i;
    · trivial;
    · exact lt_top_iff_ne_top.mpr (by simpa using hx);

namespace toFreeTail

variable {M} {V : ℕ∞ → α → Prop} {x y : M.World} {i j : ℕ∞} {A : Formula α}

@[simp, grind =] lemma rel_inl_inl : (M.toFreeTail V).Rel (.inl x) (.inl y) ↔ M.Rel x y := Iff.rfl

@[simp, grind .] lemma not_rel_inl_inr : ¬(M.toFreeTail V).Rel (.inl x) (.inr i) := id

@[simp, grind .] lemma rel_inr_inl : (M.toFreeTail V).Rel (.inr i) (.inl x) := trivial

@[simp, grind =] lemma rel_inr_inr : (M.toFreeTail V).Rel (.inr i) (.inr j) ↔ j < i := Iff.rfl

instance [IsTrans _ M.Rel] : IsTrans _ (M.toFreeTail V).Rel where
  trans x y z := by
    rcases x with x | i <;> rcases y with y | j <;> rcases z with z | k <;>
    simp only [rel_inl_inl, rel_inr_inr, rel_inr_inl, not_rel_inl_inr, IsEmpty.forall_iff,
      implies_true, forall_const];
    · exact IsTrans.trans _ _ _;
    · exact fun h₁ h₂ ↦ h₂.trans h₁;

instance [IsConverseWellFounded _ M.Rel] : IsConverseWellFounded _ (M.toFreeTail V).Rel where
  cwf := by
    have hinl : ∀ x : M.World, Acc (flip (M.toFreeTail V).Rel) (.inl x) := by
      intro x;
      induction x using WellFounded.induction IsConverseWellFounded.cwf (r := flip M.Rel) with
      | h x ih =>
        constructor;
        rintro (y | j) h;
        · exact ih y h;
        · exact absurd h not_rel_inl_inr;
    constructor;
    rintro (x | i);
    · exact hinl x;
    · induction i using WellFoundedLT.induction with
      | ind i ih =>
        constructor;
        rintro (y | j) h;
        · exact hinl y;
        · exact ih j h;

instance [M.IsGL] : (M.toFreeTail V).IsGL where

lemma forces_inl : Sum.inl x ⊩[(M.toFreeTail V).toModel] A ↔ x ⊩[M] A := by
  induction A generalizing x with
  | atom | falsum => rfl;
  | imp A B ihA ihB => exact imp_congr ihA ihB;
  | box A ih =>
    constructor;
    · intro h y Rxy;
      exact ih.mp (h (.inl y) Rxy);
    · rintro h (y | j) Rxy;
      · exact ih.mpr (h y Rxy);
      · exact absurd Rxy not_rel_inl_inr;

lemma not_rel_root {x : (M.toFreeTail V).World} : ¬(M.toFreeTail V).Rel x (.inr ⊤) := by
  rcases x with x | i;
  · exact not_rel_inl_inr;
  · exact not_top_lt;

/-- Every point of the chain sees everything below the root from some point on. -/
lemma eventually_rel {y : (M.toFreeTail V).World} (h : (M.toFreeTail V).Rel (.inr ⊤) y) :
    ∃ k : ℕ, ∀ n ≥ k, (M.toFreeTail V).Rel (.inr n) y := by
  rcases y with y | j;
  · exact ⟨0, fun _ _ ↦ trivial⟩;
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt (rel_inr_inr.mp h));
    exact ⟨m + 1, fun n hn ↦ rel_inr_inr.mpr (by exact_mod_cast Nat.lt_of_succ_le hn)⟩;

lemma forces_box_of_root (h : Sum.inr ⊤ ⊩[(M.toFreeTail V).toModel] □A)
    (x : (M.toFreeTail V).World) : x ⊩[(M.toFreeTail V).toModel] □A :=
  fun y Rxy ↦ h y ((M.toFreeTail V).root_rel y fun hy ↦ by subst hy; exact not_rel_root Rxy)

/-- If the finite points of the chain carry the valuation of the root of `M`, and the root of
`M` forces `□B 🡒 B` for all `□B ∈ X`, then they agree with the root of `M` on `X`. -/
lemma forces_inr_iff [DecidableEq α] {M : RootedModel κ α} {V : ℕ∞ → α → Prop}
    (hV : ∀ n : ℕ, V n = M.Val M.root) {X : FormulaFinset α}
    (hX : ∀ B ∈ X, B.subfmls ⊆ X) (hroot : ∀ B, □B ∈ X → M.root ⊩[M.toModel] □B 🡒 B)
    (hA : A ∈ X) (n : ℕ) :
    Sum.inr (n : ℕ∞) ⊩[(M.toModel.toFreeTail V).toModel] A ↔ M.root ⊩[M.toModel] A := by
  induction A generalizing n with
  | atom a => exact iff_of_eq (congrFun (hV n) a);
  | falsum => rfl;
  | imp B C ihB ihC =>
    exact imp_congr (ihB (hX _ hA (by grind)) n) (ihC (hX _ hA (by grind)) n);
  | box B ih =>
    have hB : B ∈ X := hX _ hA (by grind);
    constructor;
    · intro h x Rrx;
      exact forces_inl.mp (h (.inl x) trivial);
    · rintro h (x | j) Rnx;
      · apply forces_inl.mpr;
        by_cases hx : x = M.root;
        · exact hx ▸ hroot B hA h;
        · exact h x (M.root_rel x hx);
      · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt (rel_inr_inr.mp Rnx));
        exact (ih hB m).mpr (hroot B hA h);

end toFreeTail

end Model

namespace RootedModel

variable (M : RootedModel κ α)

/-- The chain carries the valuation of the root of `M`.

- [Vis84]
-/
abbrev toTail := M.toModel.toFreeTail fun _ ↦ M.Val M.root

/-- The finite points of the chain carry the valuation of the root of `M`, and the root `o`.

- [KKIM25]
-/
abbrev toPseudoTail (o : α → Prop) :=
  M.toModel.toFreeTail fun i ↦ if i = ⊤ then o else M.Val M.root

namespace toTail

open Model.toFreeTail

variable {M} {A : Formula α}

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
    · intro h x _;
      exact forces_inl.mp (h (.inl x) trivial);
    · rintro h (x | j) Rnx;
      · apply forces_inl.mpr;
        by_cases hx : x = M.root;
        · exact hx ▸ hB;
        · exact h x (M.root_rel x hx);
      · obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt (rel_inr_inr.mp Rnx));
        exact (ih m).mpr hB;

end toTail

end RootedModel

end FFL.ProvabilityLogic.Kripke

end
