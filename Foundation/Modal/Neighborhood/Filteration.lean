import Mathlib.Data.Set.Finite.Powerset
import Foundation.Modal.Neighborhood.AxiomGeach

namespace LO.Modal

namespace Neighborhood

open FormulaSet.IsSubformulaClosed
open Formula (atom)
open Formula.Neighborhood

variable {M : Model} {T : FormulaSet ℕ} [T.IsSubformulaClosed] {x y : M.World} {φ ψ : Formula ℕ}

def filterEquiv (M : Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] (x y : M.World) := ∀ φ, (_ : φ ∈ T) → x ⊧ φ ↔ y ⊧ φ

lemma filterEquiv.equivalence (M : Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] : Equivalence (filterEquiv M T) where
  refl := by intro x φ _; rfl;
  symm := by intro x y h φ hp; exact h _ hp |>.symm;
  trans := by
    intro x y z exy eyz;
    intro φ hp;
    exact Iff.trans (exy φ hp) (eyz φ hp)

def FilterEqvSetoid (M : Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] : Setoid (M.World) := ⟨filterEquiv M T, filterEquiv.equivalence M T⟩

abbrev FilterEqvQuotient (M : Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] := Quotient (FilterEqvSetoid M T)

namespace FilterEqvQuotient

@[grind]
lemma iff_eq : (⟦x⟧ : FilterEqvQuotient M T) = ⟦y⟧ ↔ (∀ φ ∈ T, x ⊧ φ ↔ y ⊧ φ) := by
  simp [FilterEqvSetoid, filterEquiv];

lemma finite (T_finite : T.Finite) : Finite (FilterEqvQuotient M T) := by
  have : Finite (𝒫 T) := Set.Finite.powerset T_finite
  let f : FilterEqvQuotient M T → 𝒫 T :=
    λ (X : FilterEqvQuotient M T) => Quotient.lift (λ x => ⟨{ φ ∈ T | x ⊧ φ }, (by simp_all)⟩) (by
      intro x y hxy;
      suffices {φ | φ ∈ T ∧ Satisfies M x φ} = {φ | φ ∈ T ∧ Satisfies M y φ} by simpa;
      apply Set.eq_of_subset_of_subset;
      . rintro φ ⟨hp, hx⟩; exact ⟨hp, (hxy φ hp).mp hx⟩;
      . rintro φ ⟨hp, hy⟩; exact ⟨hp, (hxy φ hp).mpr hy⟩;
      ) X
  have hf : Function.Injective f := by
    intro X Y h;
    obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
    obtain ⟨y, rfl⟩ := Quotient.exists_rep Y;
    simp [f] at h;
    apply Quotient.eq''.mpr;
    intro φ hp;
    constructor;
    . intro hpx;
      have : ∀ a ∈ T, x ⊧ a → a ∈ T ∧ y ⊧ a := by simpa using h.subset;
      exact this φ hp hpx |>.2;
    . intro hpy;
      have := h.symm.subset;
      simp only [Set.setOf_subset_setOf, and_imp] at this;
      exact this φ hp hpy |>.2;
  exact Finite.of_injective f hf

instance : Nonempty (FilterEqvQuotient M T) := ⟨⟦M.toFrame.world_nonempty.some⟧⟩

end FilterEqvQuotient


def toFilterEquivSet (X : Set M.World) : Set (FilterEqvQuotient M T) := { ⟦x⟧ | x ∈ X }
local notation "【" X "】" => toFilterEquivSet X

@[simp, grind] lemma toFilterEquivSet_empty : (【∅】 : Set (FilterEqvQuotient M T)) = ∅ := by simp [toFilterEquivSet];


@[grind]
lemma toFilterEquivSet_union : (【X ∪ Y】 : Set (FilterEqvQuotient M T)) = (【X】 ∪ 【Y】 : Set (FilterEqvQuotient M T)) := by
  ext Z;
  constructor;
  . rintro ⟨x, (hx | hx), rfl⟩;
    . left; use x;
    . right; use x;
  . rintro (h | h) <;>
    . obtain ⟨x, hx, rfl⟩ := h;
      use x;
      grind;

@[grind]
lemma toFilterEquivSet_compl_truthset (hφ : φ ∈ T) : (【(M φ)ᶜ】 : Set (FilterEqvQuotient M T)) = 【M φ】ᶜ := by
  ext X;
  suffices (∃ x ∉ M.truthset φ, ⟦x⟧ = X) ↔ ∀ x ∈ M.truthset φ, ¬⟦x⟧ = X by simpa [toFilterEquivSet, Model.truthset];
  constructor;
  . rintro ⟨x, hx, rfl⟩ y hy;
    apply FilterEqvQuotient.iff_eq.not.mpr;
    push_neg;
    use φ;
    constructor;
    . assumption;
    . left; tauto;
  . rintro h;
    obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
    use x;
    constructor;
    . tauto;
    . rfl;

structure Filtration (M : Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] where
  B : Set (FilterEqvQuotient M T) → Set (FilterEqvQuotient M T)
  B_def : ∀ φ, (□φ ∈ T) → B 【M φ】 = 【M.box (M φ)】
  V : ℕ → Set (FilterEqvQuotient M T)
  V_def : ∀ a, V a = 【M (.atom a)】

attribute [simp] Filtration.B_def Filtration.V_def

def Filtration.toModel {M : Model} {T : FormulaSet ℕ} [T.IsSubformulaClosed] (Fi : Filtration M T) : Model where
  toFrame := Frame.mk_ℬ (FilterEqvQuotient M T) Fi.B
  Val := Fi.V

attribute [grind]
  FormulaSet.IsSubformulaClosed.of_mem_imp₁
  FormulaSet.IsSubformulaClosed.of_mem_imp₂
  FormulaSet.IsSubformulaClosed.of_mem_box

theorem filtration (Fi : Filtration M T) (φ : Formula ℕ) (hφ : φ ∈ T) : (Fi.toModel φ) = 【M φ】 := by
  induction φ with
  | hatom a => apply Fi.V_def;
  | hfalsum => simp;
  | himp φ ψ ihφ ihψ =>
    replace ihφ := ihφ (by grind);
    replace ihψ := ihψ (by grind);
    simp_all [toFilterEquivSet_union, toFilterEquivSet_compl_truthset (show φ ∈ T by grind)];
  | hbox φ ihφ =>
    replace ihφ := ihφ (by grind);
    apply ihφ ▸ Fi.B_def φ (by grind);

lemma Filtration.truthlemma (Fi : Filtration M T) {φ ψ} (hφ : φ ∈ T) (hψ : ψ ∈ T) :
  (Fi.toModel φ) = (Fi.toModel ψ) ↔ (【M φ】 : Set (FilterEqvQuotient M T)) = (【M ψ】) := by
  rw [filtration Fi φ hφ, filtration Fi ψ hψ];

lemma toFilterEquivSet.subset_original_truthset_of_subset (hψ : ψ ∈ T) (h : (【M φ】 : Set (FilterEqvQuotient M T)) ⊆ 【M ψ】) : M φ ⊆ M ψ := by
  intro x hx;
  replace h : ∀ y ∈ M φ, ∃ z ∈ M ψ, (filterEquiv M T) z y := by simpa [toFilterEquivSet] using h;
  obtain ⟨y, hy₁, hy₂⟩ := h x hx;
  apply hy₂ ψ hψ |>.mp hy₁;

lemma Filtration.box_in_out (Fi : Filtration M T) (hφ : □φ ∈ T) : Fi.toModel.box 【M.truthset φ】 = 【M.box $ M φ】 := calc
  _ = Fi.toModel.box (Fi.toModel φ) := by rw [filtration Fi φ (by grind)];
  _ = (Fi.toModel (□φ)) := by simp;
  _ = 【M (□φ)】 := filtration Fi _ hφ
  _ = 【M.box (M φ)】 := by simp;

lemma toFilterEquivSet.eq_box (hφ : φ ∈ T) (hψ : ψ ∈ T) (h : (【M φ】 : Set (FilterEqvQuotient M T)) = 【M ψ】) : M φ = M ψ := by
  apply Set.Subset.antisymm;
  . apply toFilterEquivSet.subset_original_truthset_of_subset hψ; tauto_set;
  . apply toFilterEquivSet.subset_original_truthset_of_subset hφ; tauto_set;

lemma toFilterEquivSet.iff_box (hφ : φ ∈ T) (hψ : ψ ∈ T) : (【M φ】 : Set (FilterEqvQuotient M T)) = 【M ψ】 ↔ M φ = M ψ := by
  constructor;
  . apply toFilterEquivSet.eq_box hφ hψ;
  . tauto;

open Classical in
abbrev minimalFiltration (M : Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] : Filtration M T where
  B X := if h : ∃ φ, □φ ∈ T ∧ X = 【M φ】 then 【M.box (M h.choose)】 else ∅
  B_def := by
    intro φ hφ;
    split_ifs with hψ;
    . suffices M φ = M hψ.choose by simp [←this];
      have := hψ.choose_spec;
      apply toFilterEquivSet.eq_box (by grind) (by grind) this.2;
    . push_neg at hψ;
      have := hψ _ hφ;
      contradiction;
  V := λ a => 【M (.atom a)】
  V_def := by intro a; rfl

lemma transitive_lemma (hφ : φ ∈ T) (hψ : □ψ ∈ T) (Fi : Filtration M T) (h : 【M φ】 = Fi.toModel.box 【M ψ】) : (【M (□φ)】 : Set (FilterEqvQuotient M T)) = 【M (□□ψ)】 := by
  have : M φ = M (□ψ) := toFilterEquivSet.iff_box (T := T) hφ hψ |>.mp $ (show 【M φ】 = 【M (□ψ)】 by exact Fi.box_in_out hψ ▸ h);
  have : M.box (M φ) = M.box (M (□ψ)) := by rw [this];
  have : M (□φ) = M (□□ψ) := by tauto;
  tauto;

lemma toFilterEquivSet.trans [M.IsTransitive] : (【M (□φ)】 : Set (FilterEqvQuotient M T)) ⊆ 【M (□□φ)】 := by
  intro X;
  suffices ∀ (x : M.World), x ∈ M (□φ) → ⟦x⟧ = X → ∃ x, M.box^[2] (M φ) x ∧ ⟦x⟧ = X by
    simpa [toFilterEquivSet, Set.mem_setOf_eq];
  rintro x hx rfl;
  use x;
  constructor;
  . apply M.trans;
    simpa;
  . rfl;

open Classical in
abbrev transitiveFiltration (M : Model) [M.IsTransitive] (T : FormulaSet ℕ) [T.IsSubformulaClosed] : Filtration M T where
  B X := ((minimalFiltration M T).toModel.box X) ∪ (if ∃ Y, X = (minimalFiltration M T).toModel.box Y then X else ∅)
  B_def := by
    intro φ hφ;
    ext X;
    constructor;
    . rintro (hX | hX);
      . simpa [Filtration.box_in_out (minimalFiltration M T) (φ := φ) (by grind)] using hX;
      . split_ifs at hX with hY;
        . obtain ⟨Y, hY⟩ : ∃ Y, 【M φ】 = if h : ∃ φ, □φ ∈ T ∧ Y = 【M φ】 then 【(M (□h.choose))】 else ∅ := hY;
          split_ifs at hY with hZ;
          . apply transitive_lemma (Fi := minimalFiltration M T) (φ := φ) (ψ := hZ.choose) ?_ ?_ ?_ ▸ (toFilterEquivSet.trans (hY ▸ hX));
            . grind;
            . exact hZ.choose_spec.1;
            . exact (Filtration.box_in_out (Fi := minimalFiltration M T) (hφ := hZ.choose_spec.1)) ▸ hY;
          . tauto_set;
        . contradiction;
    . intro hX;
      left;
      suffices X ∈ if h : ∃ ψ, □ψ ∈ T ∧ 【M.truthset φ】 = 【M.truthset ψ】 then 【M.box (M h.choose)】 else ∅ by
        simpa [Filtration.toModel, Frame.mk_ℬ, Model.truthset.eq_atom, Set.mem_setOf_eq];
      split_ifs with h;
      . have := h.choose_spec;
        rwa [←(toFilterEquivSet.eq_box (by grind) (by grind) this.2)];
      . push_neg at h;
        have := h _ hφ;
        contradiction;
  V := λ a => 【M (.atom a)】
  V_def := by intro a; rfl

end Neighborhood

end LO.Modal
