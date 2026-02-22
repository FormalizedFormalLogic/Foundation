module

public import Foundation.Modal.Kripke.Root

@[expose] public section

universe u v

namespace LO.Modal

namespace Kripke

open FormulaSet.IsSubformulaClosed
open Formula (atom)
open Formula.Kripke

def filterEquiv (M : Kripke.Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] (x y : M.World) := ∀ φ, (_ : φ ∈ T) → x ⊧ φ ↔ y ⊧ φ

variable (M : Kripke.Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed]

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

lemma iff_of_eq (h : (⟦x⟧ : FilterEqvQuotient M T) = ⟦y⟧) (hφ : φ ∈ T) : x ⊧ φ ↔ y ⊧ φ := by
  apply @Quotient.eq_iff_equiv.mp h;
  assumption;

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


class FilterOf (FM : Model) (M : outParam Kripke.Model) (T : outParam (FormulaSet ℕ)) [T.IsSubformulaClosed] : Prop where
  def_world : FM.World = FilterEqvQuotient M T := by rfl
  def_rel_forth : ∀ {x y : M}, x ≺ y → (cast def_world.symm ⟦x⟧) ≺ (cast def_world.symm ⟦y⟧)
  def_rel_back : ∀ {x y : M}, (cast def_world.symm ⟦x⟧) ≺ (cast def_world.symm ⟦y⟧) → ∀ φ, □φ ∈ T → (x ⊧ □φ → y ⊧ φ)
  def_valuation X a : (ha : (atom a) ∈ T) →
    FM a X ↔ Quotient.lift (λ x => M a x) (by
      intro x y h;
      apply eq_iff_iff.mpr;
      constructor;
      . intro hx; exact h a ha |>.mp hx;
      . intro hy; exact h a ha |>.mpr hy;
    ) (cast def_world X) := by tauto

attribute [simp] FilterOf.def_world



theorem filtration
  {M : Model} (FM : Kripke.Model)
  {T : outParam (FormulaSet ℕ)} [T.IsSubformulaClosed]
  (filterOf : FilterOf FM M T)
  {x : M.World} {φ : Formula ℕ} (hs : φ ∈ T)
  : x ⊧ φ ↔ (cast (filterOf.def_world.symm) ⟦x⟧) ⊧ φ := by
  induction φ generalizing x with
  | hatom a =>
    have := filterOf.def_valuation (cast filterOf.def_world.symm ⟦x⟧) a;
    simp_all [Satisfies];
  | hbox φ ihφ =>
    constructor;
    . rintro h Y RXY;
      obtain ⟨y, ey⟩ := Quotient.exists_rep (cast (filterOf.def_world) Y);
      suffices Satisfies FM (cast filterOf.def_world.symm ⟦y⟧) φ by simp_all;
      apply ihφ (of_mem_box hs) |>.mp;
      apply @filterOf.def_rel_back x y (by simp_all) <;>
      . assumption;
    . intro h y rxy;
      apply ihφ (of_mem_box hs) |>.mpr;
      apply h;
      apply filterOf.def_rel_forth rxy;
  | himp φ ψ ihp ihq =>
    constructor;
    . rintro hxy hp;
      exact ihq (of_mem_imp₂ hs) |>.mp $ hxy (ihp (of_mem_imp₁ hs) |>.mpr hp);
    . rintro hxy hp;
      exact ihq (of_mem_imp₂ hs) |>.mpr $ hxy (ihp (of_mem_imp₁ hs) |>.mp hp);
  | _ => trivial



namespace FilterOf

variable {FM : Model} {M : outParam _} {T : outParam (FormulaSet ℕ)} [T.IsSubformulaClosed]

lemma isReflexive (filterOf : FilterOf FM M T) [M.IsReflexive] : FM.IsReflexive where
  refl := by
    intro X;
    obtain ⟨x, hx⟩ := Quotient.exists_rep (cast (filterOf.def_world) X);
    convert filterOf.def_rel_forth $ Std.Refl.refl x <;> simp_all;

lemma isSerial (filterOf : FilterOf FM M T) [M.IsSerial] : FM.IsSerial where
  serial := by
    intro X;
    obtain ⟨x, hx⟩ := Quotient.exists_rep (cast (filterOf.def_world) X);
    obtain ⟨y, Rxy⟩ : ∃ y, x ≺ y := IsSerial.serial x;
    use (cast (filterOf.def_world.symm) ⟦y⟧);
    simpa [hx] using filterOf.def_rel_forth Rxy;


end FilterOf


abbrev standardFiltrationValuation (a : ℕ) (X : FilterEqvQuotient M T) := (ha : (atom a) ∈ T) → Quotient.lift (λ x => M a x) (by
  intro x y h;
  apply eq_iff_iff.mpr;
  constructor;
  . intro hx; exact h a ha |>.mp hx;
  . intro hy; exact h a ha |>.mpr hy;
) X


variable
  {M FM : Model}
  {T : FormulaSet ℕ} [T.IsSubformulaClosed]


abbrev coarsestFiltrationFrame (M : Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] : Kripke.Frame where
  World := FilterEqvQuotient M T
  Rel := Quotient.lift₂ (λ x y => ∀ φ, □φ ∈ T → (x ⊧ □φ → y ⊧ φ)) (by
    intro x₁ y₁ x₂ y₂ hx hy;
    apply eq_iff_iff.mpr;
    constructor;
    . intro h φ hp sp₂; exact hy φ (of_mem_box hp) |>.mp $ h φ hp $ hx (□φ) hp |>.mpr sp₂;
    . intro h φ hp sp₁; exact hy φ (of_mem_box hp) |>.mpr $ h φ hp $ hx (□φ) hp |>.mp sp₁;
  )

abbrev coarsestFiltrationModel (M : Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] : Kripke.Model where
  toFrame := coarsestFiltrationFrame M T
  Val := standardFiltrationValuation M T

namespace coarsestFiltrationModel

instance filterOf : FilterOf (coarsestFiltrationModel M T) M T where
  def_rel_forth := by tauto
  def_rel_back := by tauto
  def_valuation := by tauto

lemma isFinite (T_finite : T.Finite) : (coarsestFiltrationModel M T).IsFinite where world_finite := FilterEqvQuotient.finite T_finite
instance [M.IsReflexive] : (coarsestFiltrationModel M T).IsReflexive := coarsestFiltrationModel.filterOf.isReflexive
instance [M.IsSerial] : (coarsestFiltrationModel M T).IsSerial := coarsestFiltrationModel.filterOf.isSerial

end coarsestFiltrationModel



abbrev finestFiltrationFrame (M : Model) (T : outParam (FormulaSet ℕ)) [T.IsSubformulaClosed] : Kripke.Frame where
  World := FilterEqvQuotient M T
  Rel X Y := ∃ x y, X = ⟦x⟧ ∧ Y = ⟦y⟧ ∧ x ≺ y

abbrev finestFiltrationModel (M : Model) (T : outParam (FormulaSet ℕ)) [T.IsSubformulaClosed] : Kripke.Model where
  toFrame := finestFiltrationFrame M T
  Val := standardFiltrationValuation M T


namespace finestFiltrationModel

instance filterOf : FilterOf (finestFiltrationModel M T) M T where
  def_rel_forth := by tauto;
  def_rel_back := by
    simp only [cast_eq];
    rintro x y ⟨x', y', hx, hy, Rx'y'⟩ φ hφ hφx;
    have : x' ⊧ □φ := FilterEqvQuotient.iff_of_eq hx hφ |>.mp hφx;
    have : y' ⊧ φ := this _ Rx'y';
    exact FilterEqvQuotient.iff_of_eq hy (of_mem_box hφ) |>.mpr this;

lemma isFinite (T_finite : T.Finite) : (finestFiltrationModel M T).IsFinite where
  world_finite := FilterEqvQuotient.finite T_finite
instance isReflexive [M.IsReflexive] : (finestFiltrationFrame M T).IsReflexive := finestFiltrationModel.filterOf.isReflexive
instance isSerial [M.IsSerial] : (finestFiltrationFrame M T).IsSerial := finestFiltrationModel.filterOf.isSerial
instance isSymmetric [M.IsSymmetric] : (finestFiltrationModel M T).IsSymmetric where
  symm := by
    rintro _ _ ⟨x, y, rfl, rfl, Rxy⟩;
    use y, x;
    refine ⟨by trivial, by trivial, Std.Symm.symm _ _ Rxy⟩;

end finestFiltrationModel


abbrev finestFiltrationTransitiveClosureModel (M : Model) (T : outParam (FormulaSet ℕ)) [T.IsSubformulaClosed] : Kripke.Model where
  toFrame := (finestFiltrationFrame M T)^+
  Val := standardFiltrationValuation M T

namespace finestFiltrationTransitiveClosureModel

open Relation in
instance filterOf [trans : M.IsTransitive] : FilterOf (finestFiltrationTransitiveClosureModel M T) M T where
  def_rel_forth := by
    intro x y hxy;
    apply Relation.TransGen.single;
    dsimp [finestFiltrationTransitiveClosureModel, finestFiltrationFrame];
    tauto;
  def_rel_back := by
    rintro x y RXY φ hφ hx;
    simp only [cast_eq] at RXY;
    replace ⟨n, RXY⟩ := Rel.TransGen.exists_iterate.mp RXY;
    induction n using PNat.recOn generalizing x with
    | one =>
      simp only [PNat.val_ofNat, Rel.Iterate.iff_succ, Rel.Iterate.iff_zero, exists_eq_right] at RXY;
      obtain ⟨u, v, exu, eyv, Ruv⟩ := RXY;
      have : u ⊧ □φ := FilterEqvQuotient.iff_of_eq exu hφ |>.mp hx;
      have : v ⊧ φ := this _ Ruv;
      exact FilterEqvQuotient.iff_of_eq eyv (of_mem_box hφ) |>.mpr this;
    | succ n ih =>
      obtain ⟨U, RXU, RUY⟩ := RXY;
      obtain ⟨u, rfl⟩ := Quotient.exists_rep U;
      apply @ih u ?_ RUY;
      obtain ⟨w, v, exw, euv, Rwv⟩ := RXU;
      apply FilterEqvQuotient.iff_of_eq euv (by assumption) |>.mpr;
      intro z Rvz;
      apply FilterEqvQuotient.iff_of_eq exw (by assumption) |>.mp hx;
      exact M.trans Rwv Rvz;

lemma isFinite (T_finite : T.Finite) : (finestFiltrationTransitiveClosureModel M T).IsFinite where
  world_finite := FilterEqvQuotient.finite T_finite

instance isTransitive : (finestFiltrationTransitiveClosureModel M T).IsTransitive := by simp
instance isSerial [trans : M.IsTransitive] [serial : M.IsSerial] : (finestFiltrationTransitiveClosureModel M T).IsSerial := finestFiltrationTransitiveClosureModel.filterOf.isSerial
instance isSymmetric [symm : M.IsSymmetric] : (finestFiltrationTransitiveClosureModel M T).IsSymmetric := by simp
instance isReflexive [preorder : M.IsPreorder] : (finestFiltrationTransitiveClosureModel M T).IsReflexive := by simp
instance isPreorder [preorder : M.IsPreorder] : (finestFiltrationTransitiveClosureModel M T).IsPreorder where
instance isEquiv [equiv : M.IsEquivalence] : (finestFiltrationTransitiveClosureModel M T).IsEquivalence where

instance rooted_isPiecewiseStronglyConvergent (r) [preorder : M.IsPreorder] [ps_convergent : M.IsPiecewiseStronglyConvergent] : (finestFiltrationTransitiveClosureModel (M↾r) T).IsPiecewiseStronglyConvergent where
  ps_convergent := by
    rintro X ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ RXY RXZ;
    . simp only [and_self];
      use ⟦⟨z, by tauto⟩⟧;
      apply Relation.TransGen.single;
      suffices z ≺ z by tauto;
      apply M.refl;
    . use ⟦⟨z, by tauto⟩⟧;
      constructor;
      . apply Relation.TransGen.single;
        tauto;
      . apply Relation.TransGen.single;
        suffices z ≺ z by tauto;
        apply Std.Refl.refl ;
    . use ⟦⟨y, by tauto⟩⟧;
      constructor;
      . apply Relation.TransGen.single;
        suffices y ≺ y by tauto;
        apply Std.Refl.refl;
      . apply Relation.TransGen.single;
        tauto;
    . obtain ⟨u, Ruy, Ruz⟩ := M.ps_convergent Rry Rrz;
      use ⟦⟨u, by grind⟩⟧;
      constructor;
      . exact Relation.TransGen.single $ by tauto;
      . exact Relation.TransGen.single $ by tauto;

instance rooted_isPiecewiseStronglyConnected (r) [preorder : M.IsPreorder] [ps_connected : M.IsPiecewiseStronglyConnected] : (finestFiltrationTransitiveClosureModel (M↾r) T).IsPiecewiseStronglyConnected where
  ps_connected := by
    rintro X ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ RXY RXZ;
    . simp only [or_self];
      apply Relation.TransGen.single;
      suffices z ≺ z by tauto;
      apply Std.Refl.refl;
    . left;
      apply Relation.TransGen.single;
      suffices y ≺ z by tauto;
      grind;
    . right;
      apply Relation.TransGen.single;
      suffices z ≺ y by tauto;
      grind;
    . rcases M.ps_connected Rry Rrz with (Ryz | Rrw);
      . left;
        apply Relation.TransGen.single;
        tauto;
      . right;
        apply Relation.TransGen.single;
        tauto;



end finestFiltrationTransitiveClosureModel


end Kripke

end LO.Modal
end
