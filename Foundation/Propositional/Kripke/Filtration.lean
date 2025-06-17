import Mathlib.Data.Set.Finite.Powerset
import Foundation.Propositional.Kripke.Preservation

universe u v

namespace LO.Propositional

namespace Kripke

open Formula (atom)
open Formula.Kripke

def filterEquiv (M : Kripke.Model) (T : FormulaSet ℕ) [T.SubformulaClosed] (x y : M.World) := ∀ φ, (_ : φ ∈ T := by subformula) → x ⊧ φ ↔ y ⊧ φ

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

namespace FilterEqvQuotient

variable {M T} {x y : M.World}

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
      simp only [Set.setOf_subset_setOf, and_imp, f] at this;
      exact this φ hp hpy |>.2;
  exact Finite.of_injective f hf

instance : Nonempty (FilterEqvQuotient M T) := ⟨⟦M.toFrame.world_nonempty.some⟧⟩

lemma iff_of_eq (h : (⟦x⟧ : FilterEqvQuotient M T) = ⟦y⟧) : ∀ φ ∈ T, x ⊧ φ ↔ y ⊧ φ := by
  simp [FilterEqvSetoid, filterEquiv] at h;
  tauto;

end FilterEqvQuotient


class FilterOf (FM : Model) (M : Model) (T : FormulaSet ℕ) [T.SubformulaClosed] : Prop where
  def_world : FM.World = FilterEqvQuotient M T := by rfl
  def_rel_forth : ∀ {x y : M.World}, x ≺ y → (cast def_world.symm ⟦x⟧) ≺ (cast def_world.symm ⟦y⟧)
  def_rel_back : ∀ {x y : M.World}, (cast def_world.symm ⟦x⟧) ≺ (cast def_world.symm ⟦y⟧) → ∀ φ ∈ T, (x ⊧ φ → y ⊧ φ)
  def_valuation X a : (ha : (atom a) ∈ T := by subformula) →
    FM X a ↔ Quotient.lift (λ x => M x a) (by
      intro x y h;
      apply eq_iff_iff.mpr;
      constructor;
      . intro hx; exact h (.atom a) ha |>.mp hx;
      . intro hy; exact h (.atom a) ha |>.mpr hy;
    ) (cast def_world X)

attribute [simp] FilterOf.def_world


section

variable {M T}

lemma reflexive_filterOf_of_reflexive (h_filter : FilterOf FM M T) (hRefl : Reflexive M.toFrame) : Reflexive FM.Rel := by
  intro X;
  obtain ⟨x, hx⟩ := Quotient.exists_rep (cast (h_filter.def_world) X);
  convert h_filter.def_rel_forth $ hRefl x <;> simp_all;

lemma serial_filterOf_of_serial (h_filter : FilterOf FM M T) (hSerial : Serial M.toFrame) : Serial FM.Rel := by
  intro X;
  obtain ⟨x, hx⟩ := Quotient.exists_rep (cast (h_filter.def_world) X);
  obtain ⟨y, Rxy⟩ := hSerial x;
  use (cast (h_filter.def_world.symm) ⟦y⟧);
  convert h_filter.def_rel_forth $ Rxy;
  simp_all;

end



section

variable {M : Model} {T : FormulaSet ℕ} [T.SubformulaClosed]
         (FM : Model) (filterOf : FilterOf FM M T)

theorem filtration {x : M.World} {φ : Formula ℕ} (hs : φ ∈ T := by subformula) : x ⊧ φ ↔ (cast (filterOf.def_world.symm) ⟦x⟧) ⊧ φ := by
  induction φ generalizing x with
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
    . rintro hφψ Y RXY hφ;
      obtain ⟨y, ey⟩ := Quotient.exists_rep (cast (filterOf.def_world) Y);
      have : y ⊧ ψ → Y ⊧ ψ := by simpa [ey] using ihψ (x := y) |>.mp;
      apply this;
      apply filterOf.def_rel_back ?_ (φ := φ ➝ ψ) hs hφψ;
      . apply _root_.refl;
      . apply ihφ (by subformula) |>.mpr;
        simpa [ey] using hφ;
      . simpa [ey] using RXY;
    . rintro hφψ y Rxy hφ;
      apply ihψ (by subformula) |>.mpr;
      apply hφψ;
      . apply filterOf.def_rel_forth Rxy;
      . apply ihφ (by subformula) |>.mp hφ;
  | _ => tauto

end

abbrev standardFiltrationValuation (X : FilterEqvQuotient M T) (a : ℕ) := (ha : (atom a) ∈ T) → Quotient.lift (λ x => M.Val x a) (by
  intro x y h;
  apply eq_iff_iff.mpr;
  constructor;
  . intro hx; exact h (.atom a) ha |>.mp hx;
  . intro hy; exact h (.atom a) ha |>.mpr hy;
) X


abbrev coarsestFiltrationFrame (M : Model) (T : FormulaSet ℕ) [T.SubformulaClosed] : Kripke.Frame where
  World := FilterEqvQuotient M T
  Rel := Quotient.lift₂ (λ x y => ∀ φ ∈ T, (x ⊧ φ → y ⊧ φ)) (by
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
  )
  rel_partial_order := {
    refl := by
      rintro X;
      obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
      simp;
    trans := by
      rintro X Y Z RXY RYZ;
      obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
      obtain ⟨y, rfl⟩ := Quotient.exists_rep Y;
      obtain ⟨z, rfl⟩ := Quotient.exists_rep Z;
      simp_all;
    antisymm := by
      rintro X Y RXY RYX;
      obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
      obtain ⟨y, rfl⟩ := Quotient.exists_rep Y;
      simp only [Quotient.eq];
      intro φ hφ₁;
      constructor;
      . intro hφ₂;
        exact RXY φ hφ₁ hφ₂;
      . intro hφ₂;
        exact RYX φ hφ₁ hφ₂;
  }

abbrev coarsestFiltrationModel (M : Model) (T : FormulaSet ℕ) [T.SubformulaClosed] : Kripke.Model where
  toFrame := coarsestFiltrationFrame M T
  Val := ⟨
    standardFiltrationValuation M T,
    by
      intro X Y RXY a hX ha;
      obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
      obtain ⟨y, rfl⟩ := Quotient.exists_rep Y;
      apply RXY (.atom a) ha;
      tauto;
  ⟩

instance coarsestFiltrationModel.filterOf {M} {T : FormulaSet ℕ} [T.SubformulaClosed] : FilterOf (coarsestFiltrationModel M T) M T where
  def_valuation := by tauto
  def_rel_forth := by
    intro x y Rxy;
    intro φ hφ;
    apply Formula.Kripke.Satisfies.formula_hereditary Rxy;
  def_rel_back := by tauto;


section

open Relation
open Formula.Kripke.Satisfies (formula_hereditary)

variable {M T} [T.SubformulaClosed]

abbrev finestFiltrationTransitiveClosureFrame (M : Model) (T : FormulaSet ℕ) [T.SubformulaClosed] : Kripke.Frame where
  World := FilterEqvQuotient M T
  Rel := TransGen (λ X Y => ∃ x y, X = ⟦x⟧ ∧ Y = ⟦y⟧ ∧ x ≺ y)
  rel_partial_order := {
    refl := by
      rintro X;
      obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
      apply TransGen.single;
      use x, x;
      exact ⟨rfl, rfl, M.refl⟩
    trans := by apply TransGen.trans;
    antisymm := by
      rintro x y Rxy Ryx;
      obtain ⟨x, rfl⟩ := Quotient.exists_rep x;
      obtain ⟨y, rfl⟩ := Quotient.exists_rep y;
      simp only [Quotient.eq, FilterEqvSetoid, filterEquiv];
      intro φ hφ;
      constructor;
      . obtain ⟨n, hn⟩ := TransGen.exists_iterate'.mp Rxy;
        clear Rxy Ryx;
        induction n using PNat.recOn generalizing x with
        | one =>
          simp [FilterEqvSetoid, filterEquiv] at hn;
          obtain ⟨u, Rxu, v, Ryv, Ruv⟩ := hn;
          intro hx;
          have : u ⊧ φ := Rxu φ hφ |>.mp hx;
          have : v ⊧ φ := formula_hereditary Ruv this;
          exact Ryv φ hφ |>.mpr this;
        | succ n ih =>
          obtain ⟨⟨u⟩, ⟨x', u', exx', euu', Rx'u'⟩, RUY⟩ := hn;
          intro hx;
          have : x' ⊧ φ := FilterEqvQuotient.iff_of_eq exx' φ hφ |>.mp hx;
          have : u' ⊧ φ := formula_hereditary Rx'u' this;
          have : u ⊧ φ := FilterEqvQuotient.iff_of_eq euu' φ hφ |>.mpr this;
          exact ih u RUY this;
      . obtain ⟨n, hn⟩ := TransGen.exists_iterate'.mp Ryx;
        clear Rxy Ryx;
        induction n using PNat.recOn generalizing y with
        | one =>
          simp [FilterEqvSetoid, filterEquiv] at hn;
          obtain ⟨u, Rxu, v, Ryv, Ruv⟩ := hn;
          intro hy;
          have : u ⊧ φ := Rxu φ hφ |>.mp hy;
          have : v ⊧ φ := formula_hereditary Ruv this;
          exact Ryv φ hφ |>.mpr this;
        | succ n ih =>
          obtain ⟨⟨u⟩, ⟨y', u', eyy', euu', Ry'u'⟩, RUY⟩ := hn;
          intro hy;
          have : y' ⊧ φ := FilterEqvQuotient.iff_of_eq eyy' φ hφ |>.mp hy;
          have : u' ⊧ φ := formula_hereditary Ry'u' this;
          have : u ⊧ φ := FilterEqvQuotient.iff_of_eq euu' φ hφ |>.mpr this;
          exact ih u RUY this;
  }

abbrev finestFiltrationTransitiveClosureModel (M : Model) (T : FormulaSet ℕ) [T.SubformulaClosed] : Kripke.Model where
  toFrame := (finestFiltrationTransitiveClosureFrame M T)
  Val := ⟨
    standardFiltrationValuation M T,
    by
      intro X Y RXY a hX ha;
      obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
      obtain ⟨y, rfl⟩ := Quotient.exists_rep Y;
      obtain ⟨n, hn⟩ := TransGen.exists_iterate'.mp RXY;
      clear RXY;
      induction n using PNat.recOn generalizing x with
      | one =>
        obtain ⟨u, v, exu, eyv, Ruv⟩ : ∃ u v : M.World, (⟦x⟧ : FilterEqvQuotient M T) = ⟦u⟧ ∧ (⟦y⟧ : FilterEqvQuotient M T) = ⟦v⟧ ∧ u ≺ v := by simpa using hn;
        have := FilterEqvQuotient.iff_of_eq (h := exu) (.atom a) ha |>.mp $ hX ha;
        have := formula_hereditary Ruv this;
        exact FilterEqvQuotient.iff_of_eq eyv (.atom a) ha |>.mpr this;
      | succ n ih =>
        obtain ⟨_, ⟨x', u', exx', rfl, Rx'u'⟩, RUY⟩ := hn;
        refine ih u' ?_ RUY;
        intro ha;
        apply M.Val.hereditary Rx'u';
        apply FilterEqvQuotient.iff_of_eq exx' _ ha |>.mp;
        tauto;
  ⟩


instance finestFiltrationTransitiveClosureModel.filterOf : FilterOf (finestFiltrationTransitiveClosureModel M T) M T where
  def_valuation := by tauto
  def_rel_forth := by
    intro x y Rxy;
    apply TransGen.single;
    use x, y;
    tauto;
  def_rel_back := by
    rintro x y RXY;
    obtain ⟨n, hn⟩ := TransGen.exists_iterate'.mp RXY;
    clear RXY;
    induction n using PNat.recOn generalizing x with
    | one =>
      obtain ⟨u, v, exu, eyv, Ruv⟩ : ∃ u v : M.World, (⟦x⟧ : FilterEqvQuotient M T) = ⟦u⟧ ∧ (⟦y⟧ : FilterEqvQuotient M T) = ⟦v⟧ ∧ u ≺ v := by simpa using hn;
      intro φ hφ hx;
      have : u ⊧ φ := FilterEqvQuotient.iff_of_eq exu _ hφ |>.mp hx;
      have : v ⊧ φ := formula_hereditary Ruv this;
      exact FilterEqvQuotient.iff_of_eq eyv _ hφ |>.mpr this;
    | succ n ih =>
      obtain ⟨U, ⟨v, w, exv, euw, Rvw⟩, RUY⟩ := hn;
      obtain ⟨u, rfl⟩ := Quotient.exists_rep U;
      intro φ hφ hx;
      refine @ih u ?_ φ hφ ?_;
      . simpa using RUY;
      . have : v ⊧ φ := FilterEqvQuotient.iff_of_eq exv _ hφ |>.mp hx;
        have : w ⊧ φ := formula_hereditary Rvw this;
        exact FilterEqvQuotient.iff_of_eq euw _ hφ |>.mpr this;

end

end Kripke

end LO.Propositional
