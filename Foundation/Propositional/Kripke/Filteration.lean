import Mathlib.Data.Set.Finite.Powerset
import Foundation.Vorspiel.Relation.Iterate
import Foundation.Propositional.Kripke.Preservation

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

namespace FilterEqvQuotient

variable {M T} {x y : M.World}

lemma finite (T_finite : T.Finite) : Finite (FilterEqvQuotient M T) := by
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

lemma iff_of_eq (h : (⟦x⟧ : FilterEqvQuotient M T) = ⟦y⟧) : ∀ φ ∈ T, x ⊧ φ ↔ y ⊧ φ := by
  simp [FilterEqvSetoid, filterEquiv] at h;
  tauto;

end FilterEqvQuotient


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

theorem filteration {x : M.World} {φ : Formula ℕ} (hs : φ ∈ T) : x ⊧ φ ↔ (cast (filterOf.def_world.symm) ⟦x⟧) ⊧ φ := by
  induction φ using Formula.rec' generalizing x with
  | hatom a =>
    have := filterOf.def_valuation (cast filterOf.def_world.symm ⟦x⟧) a;
    simp_all [Satisfies];
  | hand φ ψ ihφ ihψ =>
    constructor;
    . rintro ⟨hφ, hψ⟩;
      constructor;
      . refine ihφ (FormulaSet.SubformulaClosed.mem_and₁ hs) |>.mp hφ;
      . refine ihψ (FormulaSet.SubformulaClosed.mem_and₂ hs) |>.mp hψ;
    . rintro ⟨hφ, hψ⟩;
      constructor;
      . refine ihφ (FormulaSet.SubformulaClosed.mem_and₁ hs) |>.mpr hφ;
      . refine ihψ (FormulaSet.SubformulaClosed.mem_and₂ hs) |>.mpr hψ;
  | hor φ ψ ihφ ihψ =>
    constructor;
    . rintro (hφ | hψ);
      . left; exact ihφ (FormulaSet.SubformulaClosed.mem_or₁ hs) |>.mp hφ;
      . right; exact ihψ (FormulaSet.SubformulaClosed.mem_or₂ hs) |>.mp hψ;
    . rintro (hφ | hψ);
      . left; exact ihφ (FormulaSet.SubformulaClosed.mem_or₁ hs) |>.mpr hφ;
      . right; exact ihψ (FormulaSet.SubformulaClosed.mem_or₂ hs) |>.mpr hψ;
  | himp φ ψ ihφ ihψ =>
    constructor;
    . rintro hφψ Qy RQxQy hφ;
      obtain ⟨y, ey⟩ := Quotient.exists_rep (cast (filterOf.def_world) Qy);
      apply (show Satisfies M y ψ → Satisfies FM Qy ψ by simpa [ey] using @ihψ y (FormulaSet.SubformulaClosed.mem_imp₂ hs) |>.mp)
      have : ∀ φ ∈ T, Satisfies M x φ → Satisfies M y φ := by simpa [←ey] using filterOf.def_rel_back RQxQy;
      apply this (φ ➝ ψ) hs hφψ;
      . apply M.refl;
      . apply ihφ (FormulaSet.SubformulaClosed.mem_imp₁ hs) |>.mpr;
        convert hφ;
        simp_all;
    . rintro h y Rxy hφ;
      apply ihψ (FormulaSet.SubformulaClosed.mem_imp₂ hs) |>.mpr;
      apply h (filterOf.def_rel_forth Rxy);
      apply ihφ (FormulaSet.SubformulaClosed.mem_imp₁ hs) |>.mp hφ;
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
  rel_partial_order := {
    refl := by
      intro Qx;
      obtain ⟨x, rfl⟩ := Quotient.exists_rep Qx;
      simp;
    trans := by
      intro Qx Qy Qz RQxQy RQyQz;
      obtain ⟨x, rfl⟩ := Quotient.exists_rep Qx;
      obtain ⟨y, rfl⟩ := Quotient.exists_rep Qy;
      obtain ⟨z, rfl⟩ := Quotient.exists_rep Qz;
      simp_all;
    antisymm := by
      intro Qx Qy RQxQy RQyQx;
      obtain ⟨x, rfl⟩ := Quotient.exists_rep Qx;
      obtain ⟨y, rfl⟩ := Quotient.exists_rep Qy;
      simp only [Quotient.eq];
      intro φ hφ₁;
      constructor;
      . intro hφ₂; exact RQxQy φ hφ₁ hφ₂;
      . intro hφ₂; exact RQyQx φ hφ₁ hφ₂;
  }

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


section

open Relation
open Formula.Kripke.Satisfies (formula_hereditary)

variable {M T} [T.SubformulaClosed]

abbrev finestFilterationTransitiveClosureFrame (M : Model) (T : FormulaSet ℕ) [T.SubformulaClosed] : Kripke.Frame where
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

abbrev finestFilterationTransitiveClosureModel (M : Model) (T : FormulaSet ℕ) [T.SubformulaClosed] : Kripke.Model where
  toFrame := (finestFilterationTransitiveClosureFrame M T)
  Val := ⟨
    standardFilterationValuation M T,
    by
      intro X Y RXY a hX;
      obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
      obtain ⟨y, rfl⟩ := Quotient.exists_rep Y;
      obtain ⟨n, hn⟩ := TransGen.exists_iterate'.mp RXY;
      clear RXY;
      induction n using PNat.recOn generalizing x with
      | one =>
        simp [FilterEqvSetoid, filterEquiv] at hn;
        obtain ⟨u, Rxu, v, Ryv, Ruv⟩ := hn;
        intro ha;
        apply Ryv _ ha |>.mpr;
        apply M.Val.hereditary Ruv;
        apply Rxu _ ha |>.mp;
        tauto;
      | succ n ih =>
        obtain ⟨_, ⟨x', u', exx', rfl, Rx'u'⟩, RUY⟩ := hn;
        refine ih u' ?_ RUY;
        intro ha;
        apply M.Val.hereditary Rx'u';
        apply FilterEqvQuotient.iff_of_eq exx' _ ha |>.mp;
        tauto;
  ⟩

instance finestFilterationTransitiveClosureModel.filterOf : FilterOf (finestFilterationTransitiveClosureModel M T) M T where
  def_valuation := by tauto
  def_rel_forth := by
    intro x y Rxy;
    apply TransGen.single;
    use x, y;
    tauto;
  def_rel_back := by
    rintro X Y RXY;
    obtain ⟨n, hn⟩ := TransGen.exists_iterate'.mp RXY;
    clear RXY;
    induction n using PNat.recOn generalizing X with
    | one =>
      obtain ⟨U, ⟨x, y, rfl, rfl, Rxy⟩, rfl⟩ := hn;
      intro φ hφ hx;
      exact formula_hereditary Rxy hx;
    | succ n ih =>
      obtain ⟨_, ⟨x, u, rfl, rfl, Rxu⟩, RUY⟩ := hn;
      obtain ⟨y, rfl⟩ := Quotient.exists_rep Y;
      intro φ hφ hx;
      apply @ih ⟦u⟧ RUY;
      . exact hφ;
      . apply formula_hereditary Rxu hx;

end

end Kripke

end LO.Propositional
