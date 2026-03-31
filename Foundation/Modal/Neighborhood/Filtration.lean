module

public import Foundation.Modal.Neighborhood.IntersectionClosure

@[expose] public section

/-
  Filtration of neighborhood semantics.

  References:
  - K. Kopnev, "The Finite Model Property of Some Non-normal Modal Logics with the Transitivity Axiom", https://arxiv.org/abs/2305.08605
-/

namespace LO.Modal

namespace Neighborhood

open FormulaSet.IsSubformulaClosed
open Formula (atom)
open Formula.Neighborhood

attribute [grind]
  FormulaSet.IsSubformulaClosed.of_mem_imp₁
  FormulaSet.IsSubformulaClosed.of_mem_imp₂
  FormulaSet.IsSubformulaClosed.of_mem_box

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

@[grind =>]
lemma iff_eq : (⟦x⟧ : FilterEqvQuotient M T) = ⟦y⟧ ↔ (∀ φ ∈ T, x ⊧ φ ↔ y ⊧ φ) := by
  simp [FilterEqvSetoid, Quotient.eq, filterEquiv];

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

namespace toFilterEquivSet

variable {X Y : Set M.World}

@[grind ⇒]
lemma mem_of_mem {x : M.World} (hx : x ∈ X) : ⟦x⟧ ∈ (【X】 : Set (FilterEqvQuotient M T)) := by use x;

@[grind ⇒]
lemma iff_mem_truthset (hφ : φ ∈ T) : x ∈ M.truthset φ ↔ ⟦x⟧ ∈ (【M.truthset φ】 : Set (FilterEqvQuotient M T)) := by
  constructor;
  . grind;
  . rintro ⟨y, hy₁, hy₂⟩;
    exact FilterEqvQuotient.iff_eq.mp hy₂ φ hφ |>.mp hy₁;


@[simp, grind =] lemma empty : (【∅】 : Set (FilterEqvQuotient M T)) = ∅ := by simp [toFilterEquivSet];

@[grind =]
lemma union : (【X ∪ Y】 : Set (FilterEqvQuotient M T)) = (【X】 ∪ 【Y】 : Set (FilterEqvQuotient M T)) := by
  ext Z;
  constructor;
  . rintro ⟨x, (hx | hx), rfl⟩;
    . left; use x;
    . right; use x;
  . rintro (h | h) <;>
    . obtain ⟨x, hx, rfl⟩ := h;
      use x;
      grind;

@[grind ⇒]
lemma of_inter : (【X ∩ Y】 : Set (FilterEqvQuotient M T)) ⊆ (【X】 ∩ 【Y】 : Set (FilterEqvQuotient M T)) := by
  rintro _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩;
  constructor <;> use x;

@[grind =]
lemma compl_truthset (hφ : φ ∈ T) : (【(M φ)ᶜ】 : Set (FilterEqvQuotient M T)) = 【M φ】ᶜ := by
  ext X;
  suffices (∃ x ∉ M.truthset φ, ⟦x⟧ = X) ↔ ∀ x ∈ M.truthset φ, ¬⟦x⟧ = X by simpa [toFilterEquivSet, Model.truthset];
  constructor;
  . rintro ⟨x, hx, rfl⟩ y hy;
    apply FilterEqvQuotient.iff_eq.not.mpr;
    push Not;
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

lemma subset_original_truthset_of_subset (hψ : ψ ∈ T) (h : (【M φ】 : Set (FilterEqvQuotient M T)) ⊆ 【M ψ】) : M φ ⊆ M ψ := by
  intro x hx;
  replace h : ∀ y ∈ M φ, ∃ z ∈ M ψ, (filterEquiv M T) z y := by
    simpa [toFilterEquivSet, FilterEqvSetoid, Quotient.eq] using h;
  obtain ⟨y, hy₁, hy₂⟩ := h x hx;
  apply hy₂ ψ hψ |>.mp hy₁;

lemma eq_original_truthset_of_eq (hφ : φ ∈ T) (hψ : ψ ∈ T) (h : (【M φ】 : Set (FilterEqvQuotient M T)) = 【M ψ】) : M φ = M ψ := by
  apply Set.Subset.antisymm;
  . apply toFilterEquivSet.subset_original_truthset_of_subset hψ; tauto_set;
  . apply toFilterEquivSet.subset_original_truthset_of_subset hφ; tauto_set;

@[simp, grind =]
lemma eq_univ : (【Set.univ】  : Set (FilterEqvQuotient M T)) = Set.univ := by
  ext X;
  obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
  suffices ∃ y, (FilterEqvSetoid M T) y x by simpa [toFilterEquivSet];
  use x;

@[simp, grind =]
lemma contains_unit [M.ContainsUnit] : (【M (□⊤)】  : Set (FilterEqvQuotient M T)) = Set.univ := by
  suffices M (□⊤) = Set.univ by rw [this, eq_univ];
  simp [M.contains_unit];

lemma trans_truthset [M.IsTransitive] : (【M (□φ)】 : Set (FilterEqvQuotient M T)) ⊆ 【M (□□φ)】 := by
  intro X;
  suffices ∀ (x : M.World), x ∈ M (□φ) → ⟦x⟧ = X → ∃ x, M.box^[2] (M φ) x ∧ ⟦x⟧ = X by
    simpa [toFilterEquivSet, Set.mem_setOf_eq];
  rintro x hx rfl;
  use x;
  constructor;
  . apply M.trans;
    simpa;
  . rfl;

lemma refl_truthset [M.IsReflexive] : (【M (□φ)】 : Set (FilterEqvQuotient M T)) ⊆ 【M φ】 := by
  intro X;
  suffices ∀ (x : M.World), x ∈ M (□φ) → ⟦x⟧ = X → ∃ x, (M φ) x ∧ ⟦x⟧ = X by
    simpa [toFilterEquivSet, Set.mem_setOf_eq];
  rintro x hx rfl;
  use x;
  constructor;
  . apply M.refl; simpa;
  . rfl;

lemma mono'_truthset [M.IsMonotonic] (hψ : ψ ∈ T) (h : (【M φ】 : Set (FilterEqvQuotient M T)) ⊆ 【M ψ】) : (【M (□φ)】 : Set (FilterEqvQuotient M T)) ⊆ 【M (□ψ)】 := by
  intro X;
  suffices ∀ (x : M.World), x ∈ M.truthset (□φ) → ⟦x⟧ = X → ∃ x, x ∈ M.truthset (□ψ) ∧ ⟦x⟧ = X by
    simpa [toFilterEquivSet, Set.mem_setOf_eq];
  rintro x hx rfl;
  use x;
  constructor;
  . exact M.mono' (subset_original_truthset_of_subset hψ h) hx;
  . rfl;

end toFilterEquivSet


structure Filtration (M : Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] where
  B : Set (FilterEqvQuotient M T) → Set (FilterEqvQuotient M T)
  B_def : ∀ φ, (□φ ∈ T) → B 【M φ】 = 【M.box (M φ)】
  V : ℕ → Set (FilterEqvQuotient M T)
  V_def : ∀ a, V a = 【M (.atom a)】

namespace Filtration

attribute [simp] Filtration.B_def Filtration.V_def

variable {Fi : Filtration M T}

def toModel {M : Model} {T : FormulaSet ℕ} [T.IsSubformulaClosed] (Fi : Filtration M T) : Model where
  toFrame := Frame.mk_ℬ (FilterEqvQuotient M T) Fi.B
  Val := Fi.V

@[simp, grind =_]
lemma toModel_def : Fi.toModel.box X = Fi.B X := by simp [Filtration.toModel, Frame.mk_ℬ, Frame.box]

theorem filtration (Fi : Filtration M T) (φ) (hφ : φ ∈ T) : (Fi.toModel φ) = 【M φ】 := by
  induction φ with
  | hatom a => apply Fi.V_def;
  | hfalsum => simp;
  | himp φ ψ ihφ ihψ =>
    replace ihφ := ihφ (by grind);
    replace ihψ := ihψ (by grind);
    simp_all [toFilterEquivSet.union, toFilterEquivSet.compl_truthset (show φ ∈ T by grind)];
  | hbox φ ihφ =>
    replace ihφ := ihφ (by grind);
    apply ihφ ▸ Fi.B_def φ (by grind);

lemma filtration_satisfies (Fi : Filtration M T) (φ) (hφ : φ ∈ T) {x : M} : Satisfies Fi.toModel ⟦x⟧ φ ↔ x ⊧ φ := by
  simp only [Satisfies, (filtration Fi _ hφ)];
  constructor;
  . rintro ⟨y, hy, Ryx⟩;
    simp only [FilterEqvSetoid, Quotient.eq, filterEquiv] at Ryx;
    apply Ryx φ hφ |>.mp hy;
  . tauto;

lemma truthlemma (Fi : Filtration M T) {φ ψ} (hφ : φ ∈ T) (hψ : ψ ∈ T) :
  (Fi.toModel φ) = (Fi.toModel ψ) ↔ (【M φ】 : Set (FilterEqvQuotient M T)) = (【M ψ】) := by
  rw [filtration Fi φ hφ, filtration Fi ψ hψ];

@[grind .]
lemma iff_mem_toModel_box_mem_B {Fi : Filtration M T} : W ∈ Fi.toModel.box Y ↔ W ∈ Fi.B Y := by
  simp [Filtration.toModel, Frame.mk_ℬ, Frame.box];

@[grind =>]
lemma box_in_out {Fi : Filtration M T} (hφ : □φ ∈ T) : Fi.B 【M φ】 = 【M (□φ)】 := calc
  _ = Fi.toModel.box 【M.truthset φ】 := by simp [Filtration.toModel, Frame.mk_ℬ, Frame.box];
  _ = Fi.toModel.box (Fi.toModel φ) := by rw [filtration Fi φ (by grind)];
  _ = (Fi.toModel (□φ)) := by simp;
  _ = 【M (□φ)】 := filtration Fi _ hφ

@[grind =>]
lemma mem_box_in_out (hψ : □φ ∈ T) : X ∈ Fi.B 【M φ】 ↔ X ∈ 【M (□φ)】 := by grind;

lemma transitive_lemma (hφ : φ ∈ T) (hψ : □ψ ∈ T) (Fi : Filtration M T) (h : 【M φ】 = Fi.B 【M ψ】) : (【M (□φ)】 : Set (FilterEqvQuotient M T)) = 【M (□□ψ)】 := by
  have : M φ = M (□ψ) := toFilterEquivSet.eq_original_truthset_of_eq (T := T) hφ hψ $ (show 【M φ】 = 【M (□ψ)】 by exact Fi.box_in_out hψ ▸ h);
  have : M.box (M φ) = M.box (M (□ψ)) := by rw [this];
  have : M (□φ) = M (□□ψ) := by tauto;
  tauto;

end Filtration

open Classical in
def minimalFiltration (M : Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] : Filtration M T where
  B X := if h : ∃ φ, □φ ∈ T ∧ X = 【M φ】 then 【M.box (M h.choose)】 else ∅
  B_def := by
    intro φ hφ;
    split_ifs with hψ;
    . suffices M φ = M hψ.choose by simp [←this];
      have := hψ.choose_spec;
      apply toFilterEquivSet.eq_original_truthset_of_eq (by grind) (by grind) this.2;
    . push Not at hψ;
      have := hψ _ hφ;
      contradiction;
  V := λ a => 【M (.atom a)】
  V_def := by intro a; rfl

lemma minimalFiltration.iff_mem_B : W ∈ (minimalFiltration M T).B X ↔ ∃ φ, □φ ∈ T ∧ X = 【M.truthset φ】 ∧ W ∈ 【M.truthset (□φ)】 := by
  constructor;
  . intro h;
    dsimp [minimalFiltration, Filtration.toModel, Frame.mk_ℬ, Frame.box] at h;
    split_ifs at h with hY;
    . use hY.choose;
      refine ⟨?_, ?_, ?_⟩
      . exact hY.choose_spec.1;
      . exact hY.choose_spec.2;
      . simpa;
    . contradiction;
  . rintro ⟨φ, hφ, rfl, hW⟩;
    dsimp [minimalFiltration, Filtration.toModel, Frame.mk_ℬ, Frame.box];
    split_ifs with h;
    . suffices W ∈ 【M.truthset (□h.choose)】 by exact this;
      exact (minimalFiltration M T).mem_box_in_out h.choose_spec.1 |>.mp $ h.choose_spec.2 ▸ (minimalFiltration M T).mem_box_in_out hφ |>.mpr hW;
    . push Not at h;
      have := h φ hφ;
      contradiction;


open Classical in
def transitiveFiltration (M : Model) [M.IsTransitive] (T : FormulaSet ℕ) [T.IsSubformulaClosed] : Filtration M T where
  B X := ((minimalFiltration M T).B X) ∪ (if ∃ Y, X = (minimalFiltration M T).B Y then X else ∅)
  B_def := by
    intro φ hφ;
    ext X;
    constructor;
    . rintro (hX | hX);
      . exact (minimalFiltration M T).box_in_out hφ ▸ hX;
      . split_ifs at hX with hY;
        . obtain ⟨Y, hY⟩ : ∃ Y, 【M φ】 = if h : ∃ φ, □φ ∈ T ∧ Y = 【M φ】 then 【(M (□h.choose))】 else ∅ := hY;
          split_ifs at hY with hZ;
          . apply (minimalFiltration M T).transitive_lemma (φ := φ) (ψ := hZ.choose) ?_ ?_ ?_ ▸ (toFilterEquivSet.trans_truthset (hY ▸ hX));
            . grind;
            . exact hZ.choose_spec.1;
            . exact minimalFiltration M T|>.box_in_out hZ.choose_spec.1 ▸ hY;
          . tauto_set;
        . contradiction;
    . intro hX;
      left;
      suffices X ∈ if h : ∃ ψ, □ψ ∈ T ∧ 【M.truthset φ】 = 【M.truthset ψ】 then 【M.box (M h.choose)】 else ∅ by
        simpa [Filtration.toModel, Frame.mk_ℬ, Model.truthset.eq_atom, Set.mem_setOf_eq];
      split_ifs with h;
      . have := h.choose_spec;
        rwa [←(toFilterEquivSet.eq_original_truthset_of_eq (by grind) (by grind) this.2)];
      . push Not at h;
        have := h _ hφ;
        contradiction;
  V := λ a => 【M (.atom a)】
  V_def := by intro a; rfl


namespace transitiveFiltration

variable [M.IsTransitive]

lemma iff_mem_B :
  (W ∈ (transitiveFiltration M T).B X) ↔
  (((∃ φ, □φ ∈ T ∧ X = 【M.truthset φ】 ∧ W ∈ 【M.truthset (□φ)】) ∨
  (∃ φ, □φ ∈ T ∧ X = 【M.truthset (□φ)】 ∧ W ∈ 【M.truthset (□φ)】))) := by
  constructor;
  . rintro (h | h);
    . left; exact minimalFiltration.iff_mem_B.mp h;
    . split_ifs at h with hY;
      . right;
        obtain ⟨Y, rfl⟩ := hY;
        obtain ⟨φ, hφ₁, rfl, hφ₃⟩ := minimalFiltration.iff_mem_B.mp h;
        use φ;
        refine ⟨hφ₁, ?_, ?_⟩;
        . grind;
        . assumption;
      . contradiction;
  . rintro (⟨φ, hφ₁, rfl, hφ₃⟩ | ⟨φ, hφ, rfl, _⟩);
    . left;
      apply minimalFiltration.iff_mem_B.mpr;
      use φ;
    . right;
      suffices (∃ Y, 【M (□φ)】 = (minimalFiltration M T).B Y) ∧ W ∈ 【M (□φ)】 by simpa;
      constructor;
      . use (【M.truthset φ】);
        rw [Filtration.box_in_out hφ]
      . tauto;

protected instance isTransitive : (transitiveFiltration M T).toModel.IsTransitive := by
  constructor;
  intro X;
  by_cases h : (minimalFiltration M T).B X = ∅;
  . simp_all [transitiveFiltration, Filtration.toModel, Frame.mk_ℬ, Frame.box];
  . suffices (minimalFiltration M T).B X = (transitiveFiltration M T).B X by calc
      _ = (transitiveFiltration M T).B X := by simp;
      _ ⊆ (minimalFiltration M T).B X ∪ (minimalFiltration M T).B^[2] X := by tauto_set
      _ ⊆ (transitiveFiltration M T).B ((minimalFiltration M T).B X) := by
        rintro W (hW | hW);
        . right;
          split_ifs;
          . assumption;
          . grind;
        . left; assumption;
      _ = (transitiveFiltration M T).toModel.box^[2] X := by simp [this]
    ext W;
    constructor;
    . tauto;
    . rintro (hW | hW);
      . assumption;
      . split_ifs at hW with hif₁;
        . obtain ⟨Y, hY⟩ := hif₁;
          dsimp [minimalFiltration, Filtration.toModel, Frame.mk_ℬ, Frame.box] at hY;
          split_ifs at hY with hif₂;
          . generalize eψ : hif₂.choose = ψ at hif₂ hY;
            have hψ : □ψ ∈ T := eψ ▸ hif₂.choose_spec.1;
            replace hY : X = 【M (□ψ)】 := hY;
            subst hY;
            replace hW := toFilterEquivSet.trans_truthset hW;
            obtain ⟨φ, hφ₁, hφ₂, _⟩ := by simpa [minimalFiltration, Filtration.toModel, Frame.mk_ℬ, Frame.box] using h;
            have : (【M (□φ)】 : Set (FilterEqvQuotient M T)) = 【M (□□ψ)】 := (minimalFiltration M T).transitive_lemma (by grind) (by grind) $ by
              rw [(minimalFiltration M T).box_in_out hψ];
              exact hφ₂.symm;
            rwa [←this, ←(Filtration.box_in_out (Fi := minimalFiltration M T) hφ₁), ←hφ₂] at hW;
          . grind;
        . grind;

protected instance isReflexive [M.IsReflexive] : (transitiveFiltration M T).toModel.IsReflexive := by
  constructor;
  rintro X W hW;
  rcases transitiveFiltration.iff_mem_B.mp hW with (⟨φ, hφ, rfl, _⟩ | ⟨φ, hφ, rfl, _⟩);
  . apply toFilterEquivSet.refl_truthset;
    assumption;
  . assumption;

protected instance containsUnit [M.ContainsUnit] (hT : □⊤ ∈ T) : (transitiveFiltration M T).toModel.ContainsUnit := by
  constructor;
  ext X;
  suffices X ∈ (transitiveFiltration M T).B Set.univ by simpa;
  apply iff_mem_B.mpr;
  left;
  use ⊤;
  refine ⟨hT, ?_, ?_⟩;
  . simp;
  . grind;

end transitiveFiltration


open Classical in
def supplementedTransitiveFiltration (M : Model) [M.IsMonotonic] [M.IsTransitive] (T : FormulaSet ℕ) [T.IsSubformulaClosed] : Filtration M T where
  B := (transitiveFiltration M T).toModel.supplementation.box
  B_def := by
    intro φ hφ;
    suffices ⋃₀ {x | ∃ Y ⊆ 【M.truthset φ】, (transitiveFiltration M T).B Y = x} = 【M (□φ)】 by
      simpa [Frame.supplementation.box_aux]
    ext W;
    constructor;
    . rintro ⟨Y, ⟨Z, hZ₁, rfl⟩, hZ₂⟩;
      rcases transitiveFiltration.iff_mem_B.mp hZ₂ with ⟨ψ, ψ_sub, rfl, hψ⟩ | ⟨ψ, ψ_sub, rfl, hψ⟩;
      . exact toFilterEquivSet.mono'_truthset (by grind) (by assumption) hψ;
      . apply toFilterEquivSet.mono'_truthset (by grind) (by assumption) $ toFilterEquivSet.trans_truthset hψ;
    . intro hW;
      use (transitiveFiltration M T).B 【M.truthset φ】;
      constructor;
      . use 【M.truthset φ】;
      . exact (transitiveFiltration M T).mem_box_in_out hφ |>.mpr hW;
  V := (transitiveFiltration M T).V
  V_def := by simp;

namespace supplementedTransitiveFiltration

variable [M.IsMonotonic] [M.IsTransitive]

protected instance isMonotonic: (supplementedTransitiveFiltration M T).toModel.IsMonotonic := ⟨
  Frame.supplementation.isMonotonic (F := (transitiveFiltration M T).toModel.toFrame).mono
⟩

protected instance isTransitive : (supplementedTransitiveFiltration M T).toModel.IsTransitive := ⟨
  Frame.supplementation.isTransitive (F := (transitiveFiltration M T).toModel.toFrame).trans
⟩

protected instance isReflexive [M.IsReflexive] : (supplementedTransitiveFiltration M T).toModel.IsReflexive := ⟨
  Frame.supplementation.isReflexive (F := (transitiveFiltration M T).toModel.toFrame).refl
⟩

protected instance containsUnit [M.ContainsUnit] (hT : □⊤ ∈ T) : (supplementedTransitiveFiltration M T).toModel.ContainsUnit := by
  constructor;
  ext X;
  suffices X ∈ (supplementedTransitiveFiltration M T).B Set.univ by simpa;
  have : (transitiveFiltration M T).toModel.ContainsUnit := transitiveFiltration.containsUnit hT;
  simp [supplementedTransitiveFiltration, (transitiveFiltration M T).toModel.supplementation.contains_unit]

end supplementedTransitiveFiltration


open Classical in
def quasiFilteringTransitiveFiltration (M : Model) [M.IsMonotonic] [M.IsTransitive] [M.IsRegular] (T : FormulaSet ℕ) [T.IsSubformulaClosed] (hT : T.Finite) : Filtration M T where
  V := (transitiveFiltration M T).V
  V_def := by simp;
  B := (transitiveFiltration M T).toModel.quasiFiltering.box
  B_def := by
    intro φ hφ;
    ext W;
    constructor;
    . rintro ⟨Y, hY, ⟨Ys, hYs₁, hYs₂, hYs₃⟩⟩;
      let Vs := { Vi ∈ Ys | ∃ ψ, □ψ ∈ T ∧ Vi = 【M ψ】 ∧ W ∈ 【M (□ψ)】 };
      let Us := { Ui ∈ Ys | ∃ ψ, □ψ ∈ T ∧ Ui = 【M (□ψ)】 ∧ W ∈ 【M (□ψ)】 };
      have eYVU : Ys = Vs ∪ Us := by
        ext Yi;
        simp only [Finset.mem_union, Finset.mem_filter, Vs, Us];
        constructor;
        . intro hYi;
          rcases transitiveFiltration.iff_mem_B.mp $ hYs₃ Yi hYi with (hV | hU);
          . left; tauto;
          . right; tauto;
        . tauto_set;

      let Ψ := {ψ // □ψ ∈ T ∧ (∃ Vi ∈ Ys, Vi = 【M ψ】) ∧ W ∈ 【M (□ψ)】};
      have : Fintype Ψ := by
        apply Fintype.subtype (s := { ψ ∈ □⁻¹'hT.toFinset | (∃ Vi ∈ Ys, Vi = 【M ψ】) ∧ W ∈ 【M (□ψ)】 });
        simp [Finset.LO.preboxItr];
      let Ξ := {ξ // □ξ ∈ T ∧ (∃ Ui ∈ Ys, Ui = 【M (□ξ)】) ∧ W ∈ 【M (□ξ)】};
      have : Fintype Ξ := by
        apply Fintype.subtype (s := { ξ ∈ □⁻¹'hT.toFinset | (∃ Ui ∈ Ys, Ui = 【M (□ξ)】) ∧ W ∈ 【M (□ξ)】 });
        simp [Finset.LO.preboxItr];
      have H : (⋂ ψ : Ψ, 【M ψ】) ∩ (⋂ ξ : Ξ, 【M (□ξ)】) ⊆ (【M φ】 : Set (FilterEqvQuotient M T)) := by calc
        _ = (⋂ ψ : Ψ, 【M ψ】) ∩ (⋂ Ui ∈ Us, Ui) := by
          suffices (⋂ ψ : Ξ, 【M (□ψ)】) = (⋂ Ui ∈ Us, Ui) by congr;
          ext A;
          suffices
            (∀ ξ, □ξ ∈ T → 【M (□ξ)】 ∈ Ys → W ∈ 【M (□ξ)】 → A ∈ 【M (□ξ)】) ↔
            (∀ ξ, □ξ ∈ T → ∀ Yi ∈ Ys, Yi = 【M (□ξ)】 → W ∈ 【M (□ξ)】 → A ∈ Yi) by
            simp [Ξ, Us];
            tauto;
          constructor;
          . rintro h _ _ _ _ rfl;
            apply h <;> assumption;
          . rintro h _ _ _ _;
            apply h <;> tauto;
        _ = (⋂ Vi ∈ Vs, Vi) ∩ (⋂ Ui ∈ Us, Ui) := by
          suffices (⋂ ψ : Ψ, 【M ψ】) = (⋂ Vi ∈ Vs, Vi) by congr;
          ext A;
          suffices
            (∀ ψ, □ψ ∈ T → 【M ψ】 ∈ Ys → W ∈ 【M (□ψ)】 → A ∈ 【M ψ】) ↔
            (∀ ψ, □ψ ∈ T → ∀ Yi ∈ Ys, Yi = 【M ψ】 → W ∈ 【M (□ψ)】 → A ∈ Yi) by
            simp [Ψ, Vs];
            tauto;
          constructor;
          . rintro h _ _ _ _ rfl;
            apply h <;> assumption;
          . rintro h _ _ _ _;
            apply h <;> tauto;
        _ = ⋂ Xi ∈ Ys, Xi := by
          ext A;
          simp only [Set.mem_inter_iff, Set.mem_iInter, eYVU, Finset.mem_union];
          constructor;
          . rintro ⟨hV, hU⟩ i (hi | hi);
            . exact hV i hi;
            . exact hU i hi;
          . rintro h;
            constructor;
            . intro i hi;
              apply h;
              left;
              assumption;
            . intro i hi;
              apply h;
              right;
              assumption;
        _ = Y             := by grind;
        _ ⊆ 【M φ】         := by assumption;
      obtain ⟨w, rfl⟩ := Quotient.exists_rep W;
      by_cases hΨ : Nonempty Ψ <;> by_cases hΞ : Nonempty Ξ;
      . suffices w ∈ M.box ((⋂ ψ : Ψ, M ψ) ∩ (⋂ ξ : Ξ, M (□ξ))) by
          apply toFilterEquivSet.mem_of_mem;
          replace H : M.box ((⋂ ψ : Ψ, M ψ) ∩ (⋂ ξ : Ξ, M (□ξ))) ⊆ M.box (M φ) := M.mono' $ by
            rintro a ⟨haψ, haξ⟩;
            apply toFilterEquivSet.iff_mem_truthset (T := T) (by grind) |>.mpr;
            apply H;
            constructor;
            . apply Set.mem_iInter.mpr;
              intro ψ;
              apply toFilterEquivSet.iff_mem_truthset (by grind) |>.mp;
              apply haψ;
              simp;
            . apply Set.mem_iInter.mpr;
              intro ξ;
              apply toFilterEquivSet.iff_mem_truthset (by grind) |>.mp;
              apply haξ;
              simp;
          apply H this;
        apply M.regular;
        constructor;
        . suffices ∀ ψ : Ψ, w ∈ M (□ψ) by apply M.regular_finite_iUnion; simpa;
          rintro ⟨ψ, _, ⟨Vi, hVi, rfl⟩, ⟨v, hv₁, hv₂⟩⟩;
          grind;
        . suffices ∀ ξ : Ξ, w ∈ M (□^[2]ξ) by apply M.regular_finite_iUnion (ι := Ξ); simpa;
          rintro ⟨ξ, _, ⟨Ui, hUi, rfl⟩, ⟨v, hv₁, hv₂⟩⟩;
          replace hv₁ : v ∈ M.box^[2] (M ξ) := M.trans hv₁;
          grind only [= Set.subset_def, = Finset.mem_union, = Set.setOf_true, of_mem_box,
            Satisfies.def_box', = Finset.mem_filter, Model.truthset.eq_box,
            FilterEqvQuotient.iff_eq, toFilterEquivSet.mem_of_mem, Satisfies.def_box,
            usr Set.mem_setOf_eq, = Set.setOf_false, !Frame.trans,
            !toFilterEquivSet.iff_mem_truthset]
      . suffices ∀ ψ : Ψ, w ∈ M (□ψ) by
          apply toFilterEquivSet.mem_of_mem;
          replace H : M.box (⋂ ψ : Ψ, M ψ) ⊆ M.box (M φ) := M.mono' $ by
            rintro a haψ;
            apply toFilterEquivSet.iff_mem_truthset (T := T) (by grind) |>.mpr;
            apply H;
            constructor;
            . apply Set.mem_iInter.mpr;
              intro ψ;
              apply toFilterEquivSet.iff_mem_truthset (by grind) |>.mp;
              apply haψ;
              simp;
            . have : ⋂ ξ : Ξ, (【M.truthset (□ξ)】 : Set (FilterEqvQuotient M T)) = Set.univ := by
                ext A;
                simp [@IsEmpty.forall_iff (α := Ξ) (by simpa using hΞ)];
              rw [this];
              simp;
          apply H;
          apply M.regular_finite_iUnion;
          simpa;
        rintro ⟨ψ, _, ⟨Vi, hVi, rfl⟩, ⟨v, hv₁, hv₂⟩⟩;
        grind;
      . suffices ∀ ξ : Ξ, w ∈ M (□^[2]ξ) by
          apply toFilterEquivSet.mem_of_mem;
          replace H : M.box (⋂ ξ : Ξ, M (□ξ)) ⊆ M.box (M φ) := M.mono' $ by
            rintro a haξ;
            apply toFilterEquivSet.iff_mem_truthset (T := T) (by grind) |>.mpr;
            apply H;
            constructor;
            . have : ⋂ ψ : Ψ, (【M.truthset ψ】 : Set (FilterEqvQuotient M T)) = Set.univ := by
                ext A;
                simp [@IsEmpty.forall_iff (α := Ψ) (by simpa using hΨ)];
              rw [this];
              simp;
            . apply Set.mem_iInter.mpr;
              intro ξ;
              apply toFilterEquivSet.iff_mem_truthset (by grind) |>.mp;
              apply haξ;
              simp;
          apply H;
          apply M.regular_finite_iUnion;
          simpa;
        rintro ⟨ξ, _, ⟨Ui, hUi, rfl⟩, ⟨v, hv₁, hv₂⟩⟩;
        replace hv₁ : v ∈ M.box^[2] (M ξ) := M.trans hv₁;
        grind only [= Set.subset_def, = Finset.mem_union, = Set.setOf_true, of_mem_box,
          Satisfies.def_box', = Finset.mem_filter, Model.truthset.eq_box, FilterEqvQuotient.iff_eq,
          toFilterEquivSet.mem_of_mem, usr Set.mem_setOf_eq, = Set.setOf_false, !Frame.trans,
          !toFilterEquivSet.iff_mem_truthset]
      . exfalso;
        apply hYs₁;
        suffices (Vs = ∅ ∧ Us = ∅) by simp [eYVU, this.1, this.2];
        constructor;
        . suffices ∀ Yi ∈ Ys, ∀ ψ, □ψ ∈ T → Yi = 【M ψ】 → ⟦w⟧ ∉ 【M (□ψ)】 by simpa [Vs];
          rintro _ _ ψ hψ rfl;
          apply (show ∀ ψ, □ψ ∈ T → 【M ψ】 ∈ Ys → ⟦w⟧ ∉ 【M (□ψ)】 by simpa [Ψ] using hΨ) <;> assumption;
        . suffices ∀ Yi ∈ Ys, ∀ ξ, □ξ ∈ T → Yi = 【M (□ξ)】 → ⟦w⟧ ∉ 【M (□ξ)】 by simpa [Us];
          rintro _ _ ξ hξ rfl;
          apply (show ∀ ξ, □ξ ∈ T → 【M (□ξ)】 ∈ Ys → ⟦w⟧ ∉ 【M (□ξ)】 by simpa [Ξ] using hΞ) <;> assumption;
    . intro h;
      apply Frame.quasiFiltering.mem_box_of_mem_original_box;
      apply transitiveFiltration.iff_mem_B.mpr;
      left;
      use φ;
      tauto;

namespace quasiFilteringTransitiveFiltration

variable {T_finite : Set.Finite T} [M.IsMonotonic] [M.IsTransitive] [M.IsRegular]

protected instance isRegular : (quasiFilteringTransitiveFiltration M T T_finite).toModel.IsRegular := ⟨
  Frame.quasiFiltering.isRegular (F := (transitiveFiltration M T).toModel.toFrame).regular
⟩

protected instance isMonotonic: (quasiFilteringTransitiveFiltration M T T_finite).toModel.IsMonotonic := ⟨
  Frame.quasiFiltering.isMonotonic (F := (transitiveFiltration M T).toModel.toFrame).mono
⟩

protected instance isTransitive : (quasiFilteringTransitiveFiltration M T T_finite).toModel.IsTransitive := ⟨
  Frame.quasiFiltering.isTransitive (F := (transitiveFiltration M T).toModel.toFrame).trans
⟩

protected instance containsUnit [M.ContainsUnit] (hT : □⊤ ∈ T) : (quasiFilteringTransitiveFiltration M T T_finite).toModel.ContainsUnit := by
  constructor;
  ext X;
  suffices X ∈ (quasiFilteringTransitiveFiltration M T T_finite).B Set.univ by simpa;
  have : (transitiveFiltration M T).toModel.ContainsUnit := transitiveFiltration.containsUnit hT;
  simp [quasiFilteringTransitiveFiltration, (transitiveFiltration M T).toModel.quasiFiltering.contains_unit];

end quasiFilteringTransitiveFiltration

end Neighborhood

end LO.Modal
end
