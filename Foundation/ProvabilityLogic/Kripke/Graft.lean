module

public import Foundation.ProvabilityLogic.Kripke.Rank
public import Mathlib.Basic.Finite.Sum

/-!
# Grafting a chain below a point

## References

- [AB05, Lemma 12]
- [Bek90, Lemma 5]
-/

@[expose] public section

namespace FFL.ProvabilityLogic.Kripke

open Model Model.World

variable {κ α : Type*} [Nonempty κ]

namespace RootedModel

/-- `M` with a descending chain `ι` inserted between the root and `a`: the root sees the chain,
every point of the chain sees `a` and the cone above it, and carries the valuation of `a`.

- [AB05, Lemma 12]
- [Bek90, Lemma 5]
-/
def graft (M : RootedModel κ α) (a : M.NonRoot) (ι : Type*) [LT ι] : RootedModel (κ ⊕ ι) α where
  Rel' x y := match x, y with
    | .inl x, .inl y => M.Rel x y
    | .inl x, .inr _ => x = M.root
    | .inr _, .inl y => y = a.1 ∨ M.Rel a.1 y
    | .inr i, .inr j => j < i
  Val' x p := match x with
    | .inl x => M.Val x p
    | .inr _ => M.Val a.1 p
  root := .inl M.root
  root_rel x hx := by
    rcases x with x | i;
    . exact M.root_rel x (by simpa using hx);
    . rfl;

namespace graft

variable {M : RootedModel κ α} {a : M.NonRoot} {ι : Type*} [LT ι] {x y : M.World} {i j : ι}

@[simp, grind =] lemma rel_inl_inl : (M.graft a ι).Rel (.inl x) (.inl y) ↔ M.Rel x y := Iff.rfl

@[simp, grind =] lemma rel_inl_inr : (M.graft a ι).Rel (.inl x) (.inr i) ↔ x = M.root := Iff.rfl

@[simp, grind =]
lemma rel_inr_inl : (M.graft a ι).Rel (.inr i) (.inl y) ↔ y = a.1 ∨ M.Rel a.1 y := Iff.rfl

@[simp, grind =] lemma rel_inr_inr : (M.graft a ι).Rel (.inr i) (.inr j) ↔ j < i := Iff.rfl

@[simp] lemma root_eq : (M.graft a ι).root = .inl M.root := rfl

section

variable {ι : Type*} [Preorder ι]

instance [IsTrans _ M.Rel] [Std.Irrefl M.Rel] : IsTrans _ (M.graft a ι).Rel where
  trans x y z := by
    have := M.root_rel a.1 a.2;
    have := a.2;
    have : ∀ x y z : M.World, x ≺ y → y ≺ z → x ≺ z := fun _ _ _ ↦ IsTrans.trans _ _ _;
    rcases x with x | i <;> rcases y with y | j <;> rcases z with z | k <;>
    simp only [rel_inl_inl, rel_inl_inr, rel_inr_inl, rel_inr_inr] <;> grind;

instance [Std.Irrefl M.Rel] : Std.Irrefl (M.graft a ι).Rel where
  irrefl x := by
    rcases x with x | i;
    . exact Std.Irrefl.irrefl (r := M.Rel) x;
    . exact lt_irrefl i;

instance [M.IsGL] [WellFoundedLT ι] : IsConverseWellFounded _ (M.graft a ι).Rel where
  cwf := by
    have hinl : ∀ x : M.World, x ≠ M.root → Acc (flip (M.graft a ι).Rel) (.inl x) := by
      intro x;
      induction x using WellFounded.induction IsConverseWellFounded.cwf (r := flip M.Rel) with
      | h x ih =>
        intro hx;
        constructor;
        rintro (y | j) h;
        . exact ih y h (by rintro rfl; exact not_rel_root h);
        . exact absurd h hx;
    have hinr : ∀ i : ι, Acc (flip (M.graft a ι).Rel) (.inr i) := by
      intro i;
      induction i using WellFoundedLT.induction with
      | ind i ih =>
        constructor;
        rintro (y | j) h;
        . apply hinl y;
          rintro rfl;
          rcases h with h | h;
          . exact a.2 h.symm;
          . exact not_rel_root h;
        . exact ih j h;
    constructor;
    rintro (x | i);
    . by_cases hx : x = M.root;
      . subst hx;
        constructor;
        rintro (y | j) h;
        . exact hinl y (by rintro rfl; exact not_rel_root h);
        . exact hinr j;
      . exact hinl x hx;
    . exact hinr i;

instance [M.IsGL] [WellFoundedLT ι] : (M.graft a ι).IsGL where

instance [M.IsFiniteGL] [Finite ι] : (M.graft a ι).IsFiniteGL where
  finite := inferInstanceAs (Finite (M.World ⊕ ι))

end

/-- The points of `M` keep their forcing, and the points of the chain behave as `a`, on a
subformula-closed set on whose boxes `a` is reflexive.

- [AB05, Lemma 12]
- [Bek90, Lemma 5]
-/
lemma forces_iff [DecidableEq α] {Φ : FormulaFinset α} (hΦ : ∀ B ∈ Φ, B.subfmls ⊆ Φ)
    (ha : ∀ B, □B ∈ Φ → a.1 ⊩[M.toModel] □B 🡒 B) {A : Formula α} (hA : A ∈ Φ) :
    (∀ x, Sum.inl x ⊩[(M.graft a ι).toModel] A ↔ x ⊩[M.toModel] A) ∧
    (∀ i, Sum.inr i ⊩[(M.graft a ι).toModel] A ↔ a.1 ⊩[M.toModel] A) := by
  induction A with
  | atom | falsum => exact ⟨fun _ ↦ Iff.rfl, fun _ ↦ Iff.rfl⟩;
  | imp B C ihB ihC =>
    obtain ⟨hB₁, hB₂⟩ := ihB (hΦ _ hA (by grind));
    obtain ⟨hC₁, hC₂⟩ := ihC (hΦ _ hA (by grind));
    exact ⟨fun x ↦ imp_congr (hB₁ x) (hC₁ x), fun i ↦ imp_congr (hB₂ i) (hC₂ i)⟩;
  | box B ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (hΦ _ hA (by grind));
    and_intros;
    . intro x;
      constructor;
      . exact fun h y Rxy ↦ (ih₁ y).mp (h (.inl y) Rxy);
      . rintro h (y | i) Rxy;
        . exact (ih₁ y).mpr (h y Rxy);
        . exact (ih₂ i).mpr (h a.1 (Rxy ▸ M.root_rel a.1 a.2));
    . intro i;
      constructor;
      . exact fun h y Ray ↦ (ih₁ y).mp (h (.inl y) (.inr Ray));
      . rintro h (y | j) Riy;
        . rcases Riy with rfl | Ray;
          . exact (ih₁ _).mpr (ha B hA h);
          . exact (ih₁ y).mpr (h y Ray);
        . exact (ih₂ j).mpr (ha B hA h);

lemma not_forces_boxItr_bot (n : ℕ) : (M.graft a ℕ).root ⊮[(M.graft a ℕ).toModel] □^[n]⊥ := by
  have h : ∀ m : ℕ, (M.graft a ℕ).RelItr m (.inr m) (.inr 0) := by
    intro m;
    induction m with
    | zero => rfl;
    | succ m ih => exact ⟨.inr m, by simp, ih⟩;
  rcases n with _ | n;
  . exact id;
  . exact fun hr ↦ forces_boxItr.mp hr (.inr 0) ⟨.inr n, rfl, h n⟩;

section Rank

variable [Fintype M.World] [M.IsGL] {k : ℕ}

instance : Fintype (M.graft a (Fin k)).World := inferInstanceAs (Fintype (M.World ⊕ Fin k))

lemma rank_inl (hx : x ≠ M.root) :
    Model.World.rank (M := (M.graft a (Fin k)).toModel) (.inl x) = x.rank := by
  induction x using WellFounded.induction IsConverseWellFounded.cwf (r := flip M.Rel) with
  | h x ih =>
    apply le_antisymm;
    . apply cwfHeight_le;
      rintro (y | i) R;
      . have hy : y ≠ M.root := by rintro rfl; exact not_rel_root R;
        have := ih y R hy;
        have := rank_lt_of_rel (M := M.toModel) R;
        simp_all [World.rank];
      . exact absurd R hx;
    . apply cwfHeight_le;
      intro y R;
      have hy : y ≠ M.root := by rintro rfl; exact not_rel_root R;
      have := ih y R hy;
      have := rank_lt_of_rel (M := (M.graft a (Fin k)).toModel) (x := .inl x) (y := .inl y) R;
      simp_all [World.rank];

lemma rank_inr (i : Fin k) :
    Model.World.rank (M := (M.graft a (Fin k)).toModel) (.inr i) = i + 1 + a.1.rank := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have ha := rank_inl (a := a) (k := k) a.2;
    apply le_antisymm;
    . apply cwfHeight_le;
      rintro (y | j) R;
      . have hy : y ≠ M.root := by
          rcases R with rfl | R;
          exacts [a.2, fun h ↦ not_rel_root (h ▸ R)];
        have := rank_inl (a := a) (k := k) hy;
        have : World.rank (M := M.toModel) y ≤ a.1.rank := by
          rcases R with rfl | R;
          exacts [le_rfl, (rank_lt_of_rel R).le];
        simp only [World.rank] at *;
        omega;
      . have := ih j R;
        have : j.1 < i.1 := R;
        simp only [World.rank] at *;
        omega;
    . obtain ⟨_ | m, hm⟩ := i;
      . have := rank_lt_of_rel (M := (M.graft a (Fin k)).toModel)
          (x := .inr ⟨0, hm⟩) (y := .inl a.1) (.inl rfl);
        simp only [World.rank] at *;
        omega;
      . have := ih ⟨m, by omega⟩ (show m < m + 1 by omega);
        have := rank_lt_of_rel (M := (M.graft a (Fin k)).toModel)
          (x := .inr ⟨m + 1, hm⟩) (y := .inr ⟨m, by omega⟩) (show m < m + 1 by omega);
        simp only [World.rank] at *;
        omega;

lemma height_eq : (M.graft a (Fin k)).height = max M.height (a.1.rank + k + 1) := by
  have hne : ∀ {y}, M.root ≺ y → y ≠ M.root := fun R h ↦ Std.Irrefl.irrefl (r := M.Rel) _ (h ▸ R);
  apply le_antisymm;
  . apply cwfHeight_le;
    rintro (y | i) R;
    . replace R : M.root ≺ y := R;
      have := rank_inl (a := a) (k := k) (hne R);
      have := rank_lt_height R;
      simp only [World.rank, height] at *;
      omega;
    . have := rank_inr (a := a) i;
      have := i.2;
      simp only [World.rank, height, root_eq] at *;
      omega;
  . apply max_le;
    . apply cwfHeight_le;
      intro y R;
      have := rank_inl (a := a) (k := k) (hne R);
      have := rank_lt_of_rel (M := (M.graft a (Fin k)).toModel)
        (x := .inl M.root) (y := .inl y) R;
      simp only [World.rank, height, root_eq] at *;
      omega;
    . rcases k with _ | k;
      . have := rank_inl (a := a) (k := 0) a.2;
        have := rank_lt_of_rel (M := (M.graft a (Fin 0)).toModel)
          (x := .inl M.root) (y := .inl a.1) (M.root_rel a.1 a.2);
        simp only [World.rank, height, root_eq] at *;
        omega;
      . have := rank_inr (a := a) (⟨k, by omega⟩ : Fin (k + 1));
        have := rank_lt_of_rel (M := (M.graft a (Fin (k + 1))).toModel)
          (x := .inl M.root) (y := .inr ⟨k, by omega⟩) rfl;
        simp only [World.rank, height, root_eq] at *;
        omega;

end Rank

end graft

end RootedModel

end FFL.ProvabilityLogic.Kripke

end
