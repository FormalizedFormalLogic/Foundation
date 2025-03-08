import Mathlib.Data.Set.Finite.Powerset
import Foundation.Propositional.Kripke.Basic

universe u v

namespace LO.Propositional

namespace Kripke

open Formula (atom)
open Formula.Kripke

def filterEquiv (M : Kripke.Model) (T : FormulaSet ℕ) [T.SubformulaClosed] (x y : M.World) := ∀ φ, (_ : φ ∈ T := by trivial) → x ⊧ φ ↔ y ⊧ φ

variable (M : Kripke.Model) (T : FormulaSet ℕ) [T.SubformulaClosed]

lemma filterEquiv.equivalence : Equivalence (filterEquiv M T) where
  refl := by intro x φ _; rfl;
  symm := by intro x y h φ hp; exact h _ hp |>.symm;
  trans := by
    intro x y z exy eyz;
    intro φ hp;
    exact Iff.trans (exy φ hp) (eyz φ hp)

def FilterEqvSetoid : Setoid (M.World) := ⟨filterEquiv M T, filterEquiv.equivalence M T⟩

abbrev FilterEqvQuotient := Quotient (FilterEqvSetoid M T)

lemma FilterEqvQuotient.finite (T_finite : T.Finite) : Finite (FilterEqvQuotient M T) := by
  have : Finite (𝒫 T) := Set.Finite.powerset T_finite
  let f : FilterEqvQuotient M T → 𝒫 T :=
    λ (Qx : FilterEqvQuotient M T) => Quotient.lift (λ x => ⟨{ φ ∈ T | x ⊧ φ }, (by simp_all)⟩) (by
      intro x y hxy;
      suffices {φ | φ ∈ T ∧ Satisfies M x φ} = {φ | φ ∈ T ∧ Satisfies M y φ} by simpa;
      apply Set.eq_of_subset_of_subset;
      . rintro φ ⟨hp, hx⟩; exact ⟨hp, (hxy φ hp).mp hx⟩;
      . rintro φ ⟨hp, hy⟩; exact ⟨hp, (hxy φ hp).mpr hy⟩;
    ) Qx
  have hf : Function.Injective f := by
    intro Qx Qy h;
    obtain ⟨x, rfl⟩ := Quotient.exists_rep Qx;
    obtain ⟨y, rfl⟩ := Quotient.exists_rep Qy;
    simp [f] at h;
    apply Quotient.eq''.mpr;
    intro φ hp;
    constructor;
    . intro hpx;
      have : ∀ a ∈ T, x ⊧ a → a ∈ T ∧ y ⊧ a := by simpa using h.subset;
      exact this φ hp hpx |>.2;
    . intro hpy;
      have := h.symm.subset;
      simp only [Set.setOf_subset_setOf, and_imp, f] at this;
      exact this φ hp hpy |>.2;
  exact Finite.of_injective f hf

instance : Nonempty (FilterEqvQuotient M T) := ⟨⟦M.toFrame.world_nonempty.some⟧⟩

class FilterOf (FM : Model) (M : Model) (T : FormulaSet ℕ) [T.SubformulaClosed] : Prop where
  def_world : FM.World = FilterEqvQuotient M T := by rfl
  def_rel_forth : ∀ {x y : M.World}, x ≺ y → (cast def_world.symm ⟦x⟧) ≺ (cast def_world.symm ⟦y⟧)
  def_rel_back : ∀ {Qx Qy : FM.World}, Qx ≺ Qy → Quotient.lift₂ (λ x y => ∀ φ ∈ T, (x ⊧ φ → y ⊧ φ)) (by
    intro x₁ y₁ x₂ y₂ hx hy;
    apply eq_iff_iff.mpr;
    constructor;
    . intro h φ hφ hφ_x₂;
      apply hy φ |>.mp;
      apply h;
      . exact hφ
      . apply hx φ |>.mpr hφ_x₂;
    . intro h φ hφ hφ_y₁;
      apply hy φ |>.mpr;
      apply h;
      . exact hφ
      . apply hx φ |>.mp hφ_y₁;
  ) (cast def_world Qx) (cast def_world Qy)
  def_valuation Qx a : (ha : (atom a) ∈ T := by trivial) →
    FM Qx a ↔ Quotient.lift (λ x => M x a) (by
      intro x y h;
      apply eq_iff_iff.mpr;
      constructor;
      . intro hx; exact h (.atom a) ha |>.mp hx;
      . intro hy; exact h (.atom a) ha |>.mpr hy;
    ) (cast def_world Qx)

attribute [simp] FilterOf.def_world


section

variable {M T}

lemma reflexive_filterOf_of_reflexive (h_filter : FilterOf FM M T) (hRefl : Reflexive M.toFrame) : Reflexive FM.Rel := by
  intro Qx;
  obtain ⟨x, hx⟩ := Quotient.exists_rep (cast (h_filter.def_world) Qx);
  convert h_filter.def_rel_forth $ hRefl x <;> simp_all;

lemma serial_filterOf_of_serial (h_filter : FilterOf FM M T) (hSerial : Serial M.toFrame) : Serial FM.Rel := by
  intro Qx;
  obtain ⟨x, hx⟩ := Quotient.exists_rep (cast (h_filter.def_world) Qx);
  obtain ⟨y, Rxy⟩ := hSerial x;
  use (cast (h_filter.def_world.symm) ⟦y⟧);
  convert h_filter.def_rel_forth $ Rxy;
  simp_all;

end



section

variable {M : Model} {T : FormulaSet ℕ} [T.SubformulaClosed]
         (FM : Model) (filterOf : FilterOf FM M T)

theorem filteration {x : M.World} {φ : Formula ℕ} (hs : φ ∈ T := by subformula) : x ⊧ φ ↔ (cast (filterOf.def_world.symm) ⟦x⟧) ⊧ φ := by
  induction φ using Formula.rec' generalizing x with
  | hatom a =>
    have := filterOf.def_valuation (cast filterOf.def_world.symm ⟦x⟧) a;
    simp_all [Satisfies];
  | hand φ ψ ihφ ihψ =>
    constructor;
    . rintro ⟨hφ, hψ⟩;
      constructor;
      . refine ihφ (by subformula) |>.mp hφ;
      . refine ihψ (by subformula) |>.mp hψ;
    . rintro ⟨hφ, hψ⟩;
      constructor;
      . refine ihφ (by subformula) |>.mpr hφ;
      . refine ihψ (by subformula) |>.mpr hψ;
  | hor φ ψ ihφ ihψ =>
    constructor;
    . rintro (hφ | hψ);
      . left; exact ihφ (by subformula) |>.mp hφ;
      . right; exact ihψ (by subformula) |>.mp hψ;
    . rintro (hφ | hψ);
      . left; exact ihφ (by subformula) |>.mpr hφ;
      . right; exact ihψ (by subformula) |>.mpr hψ;
  | himp φ ψ ihφ ihψ =>
    constructor;
    . rintro hφψ Qy RQxQy hφ;
      obtain ⟨y, ey⟩ := Quotient.exists_rep (cast (filterOf.def_world) Qy);
      apply (show Satisfies M y ψ → Satisfies FM Qy ψ by simpa [ey] using ihψ (x := y) (by subformula) |>.mp)
      have : ∀ φ ∈ T, Satisfies M x φ → Satisfies M y φ := by simpa [←ey] using filterOf.def_rel_back RQxQy;
      apply this (φ ➝ ψ) hs hφψ;
      . simp;
      . apply ihφ (by subformula) |>.mpr;
        convert hφ;
        simp_all;
    . rintro h y Rxy hφ;
      apply ihψ (by subformula) |>.mpr;
      apply h (filterOf.def_rel_forth Rxy);
      apply ihφ (by subformula) |>.mp hφ;
  | _ => trivial

end

abbrev standardFilterationValuation (Qx : FilterEqvQuotient M T) (a : ℕ) := (ha : (atom a) ∈ T) → Quotient.lift (λ x => M.Val x a) (by
  intro x y h;
  apply eq_iff_iff.mpr;
  constructor;
  . intro hx; exact h (.atom a) ha |>.mp hx;
  . intro hy; exact h (.atom a) ha |>.mpr hy;
) Qx


abbrev coarsestFilterationFrame (M : Model) (T : FormulaSet ℕ) [T.SubformulaClosed] : Kripke.Frame where
  World := FilterEqvQuotient M T
  Rel Qx Qy :=
    Quotient.lift₂ (λ x y => ∀ φ ∈ T, (x ⊧ φ → y ⊧ φ)) (by
      intro x₁ y₁ x₂ y₂ hx hy;
      apply eq_iff_iff.mpr;
      constructor;
      . intro h φ hφ hφ_x₂;
        apply hy φ |>.mp;
        apply h;
        . exact hφ
        . apply hx φ |>.mpr hφ_x₂;
      . intro h φ hφ hφ_y₁;
        apply hy φ |>.mpr;
        apply h;
        . exact hφ
        . apply hx φ |>.mp hφ_y₁;
    ) Qx Qy
  rel_refl := by
    intro Qx;
    obtain ⟨x, rfl⟩ := Quotient.exists_rep Qx;
    simp;
  rel_trans := by
    intro Qx Qy Qz RQxQy RQyQz;
    obtain ⟨x, rfl⟩ := Quotient.exists_rep Qx;
    obtain ⟨y, rfl⟩ := Quotient.exists_rep Qy;
    obtain ⟨z, rfl⟩ := Quotient.exists_rep Qz;
    simp_all;
  rel_antisymm := by
    intro Qx Qy RQxQy RQyQx;
    obtain ⟨x, rfl⟩ := Quotient.exists_rep Qx;
    obtain ⟨y, rfl⟩ := Quotient.exists_rep Qy;
    simp only [Quotient.eq];
    intro φ hφ₁;
    constructor;
    . intro hφ₂; exact RQxQy φ hφ₁ hφ₂;
    . intro hφ₂; exact RQyQx φ hφ₁ hφ₂;

abbrev coarsestFilterationModel (M : Model) (T : FormulaSet ℕ) [T.SubformulaClosed] : Kripke.Model where
  toFrame := coarsestFilterationFrame M T
  Val := ⟨
    standardFilterationValuation M T,
    by
      intro Qx Qy RQxQy a hQx ha;
      obtain ⟨x, rfl⟩ := Quotient.exists_rep Qx;
      obtain ⟨y, rfl⟩ := Quotient.exists_rep Qy;
      apply RQxQy (.atom a) ha;
      tauto;
  ⟩

instance coarsestFilterationModel.filterOf {M} {T : FormulaSet ℕ} [T.SubformulaClosed] : FilterOf (coarsestFilterationModel M T) M T where
  def_valuation := by tauto
  def_rel_forth := by
    intro x y Rxy;
    intro φ hφ;
    apply Formula.Kripke.Satisfies.formula_hereditary Rxy;
  def_rel_back := by tauto;


-- TODO: might be wrong, because finest filteration is not transitive?
/-
abbrev finestFilterationFrame (M : Model) (T : FormulaSet ℕ) [T.SubformulaClosed] : Kripke.Frame where
  World := FilterEqvQuotient M T
  Rel Qx Qy := ∃ x y, Qx = ⟦x⟧ ∧ Qy = ⟦y⟧ ∧ x ≺ y
  rel_refl := by
    intro Qx;
    obtain ⟨x, rfl⟩ := Quotient.exists_rep Qx;
    use x, x;
    simp;
  rel_trans := by
    rintro Qx Qy Qz ⟨x, y, ⟨rfl, rfl, Rxy⟩⟩ ⟨w, z, ⟨hyw, rfl, Ryz⟩⟩;
    use x, z;
    refine ⟨by tauto, by tauto, ?_⟩;
    sorry;

abbrev finestFilterationModel (M : Model) (T : FormulaSet ℕ) [T.SubformulaClosed] : Kripke.Model where
  toFrame := coarsestFilterationFrame M T
  Val := ⟨
    standardFilterationValuation M T,
    by
      intro Qx Qy RQxQy a hQx ha;
      obtain ⟨x, rfl⟩ := Quotient.exists_rep Qx;
      obtain ⟨y, rfl⟩ := Quotient.exists_rep Qy;
      apply RQxQy (.atom a) ha;
      tauto;
  ⟩

instance finestFilterationModel.filterOf {M} {T : FormulaSet ℕ} [T.SubformulaClosed] : FilterOf (finestFilterationModel M T) M T where
  def_valuation := by tauto
  def_rel_back := by tauto;
  def_rel_forth := by
    intro x y Rxy;
    intro φ hφ;
    apply Formula.Kripke.Satisfies.formula_hereditary Rxy;
-/

end Kripke

end LO.Propositional
