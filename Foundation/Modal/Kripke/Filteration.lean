import Mathlib.Data.Set.Finite.Powerset
import Foundation.Modal.Kripke.Closure

universe u v

namespace LO.Modal

namespace Kripke

open FormulaSet.IsSubformulaClosed
open Formula (atom)
open Formula.Kripke

section

def filterEquiv (M : Kripke.Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] (x y : M.World) := ∀ φ, (_ : φ ∈ T := by subformula) → x ⊧ φ ↔ y ⊧ φ

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

class FilterOf (FM : Model) (M : Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] : Prop where
  def_world : FM.World = FilterEqvQuotient M T := by rfl
  def_rel₁ : ∀ {x y : M.toFrame}, x ≺ y → Frame.Rel' (cast def_world.symm ⟦x⟧) (cast def_world.symm ⟦y⟧)
  def_box : ∀ {Qx Qy : FM.World}, Qx ≺ Qy → Quotient.lift₂ (λ x y => ∀ φ, □φ ∈ T → (x ⊧ □φ → y ⊧ φ)) (by
    intro x₁ y₁ x₂ y₂ hx hy;
    apply eq_iff_iff.mpr;
    constructor;
    . intro h φ hφ hφ₂;
      apply hy φ (of_mem_box hφ) |>.mp;
      apply h _ hφ;
      apply hx _ hφ |>.mpr;
      assumption;
    . intro h φ hφ hx₁;
      apply hy φ (of_mem_box hφ) |>.mpr;
      apply h φ hφ;
      apply hx (□φ) hφ |>.mp;
      assumption;
  ) (cast def_world Qx) (cast def_world Qy)
  def_valuation Qx a : (ha : (atom a) ∈ T) →
    FM Qx a ↔ Quotient.lift (λ x => M x a) (by
      intro x y h;
      apply eq_iff_iff.mpr;
      constructor;
      . intro hx; exact h a ha |>.mp hx;
      . intro hy; exact h a ha |>.mpr hy;
    ) (cast def_world Qx) := by tauto

attribute [simp] FilterOf.def_world


section

variable {M : Model} {T : FormulaSet ℕ} [T.IsSubformulaClosed] (FM : Model) (filterOf : FilterOf FM M T)

theorem filteration {x : M.World} {φ : Formula ℕ} (hs : φ ∈ T) : x ⊧ φ ↔ (cast (filterOf.def_world.symm) ⟦x⟧) ⊧ φ := by
  induction φ generalizing x with
  | hatom a =>
    have := filterOf.def_valuation (cast filterOf.def_world.symm ⟦x⟧) a;
    simp_all [Satisfies];
  | hbox φ ihp =>
    constructor;
    . intro h Qy rQxQy;
      obtain ⟨y, ey⟩ := Quotient.exists_rep (cast (filterOf.def_world) Qy);
      have this := filterOf.def_box rQxQy; simp [←ey] at this;
      simpa [ey] using ihp (of_mem_box hs) |>.mp $ @this φ hs h;
    . intro h y rxy;
      have rQxQy := filterOf.def_rel₁ rxy;
      exact ihp (of_mem_box hs) |>.mpr $ h _ rQxQy;
  | himp φ ψ ihp ihq =>
    constructor;
    . rintro hxy hp;
      exact ihq (of_mem_imp₂ hs) |>.mp $ hxy (ihp (of_mem_imp₁ hs) |>.mpr hp);
    . rintro hxy hp;
      exact ihq (of_mem_imp₂ hs) |>.mpr $ hxy (ihp (of_mem_imp₁ hs) |>.mp hp);
  | _ => trivial

end


section

variable {M FM : Model} {T}

lemma isRefl_of_filterOf (h_filter : FilterOf FM M T) [IsRefl _ M.Rel] : IsRefl _ FM.Rel := ⟨by
  intro Qx;
  obtain ⟨x, hx⟩ := Quotient.exists_rep (cast (h_filter.def_world) Qx);
  convert h_filter.def_rel₁ $ IsRefl.refl x <;> simp_all;
⟩

lemma isSerial_of_filterOf (h_filter : FilterOf FM M T) [IsSerial _ M.Rel] : IsSerial _ FM.Rel := ⟨by
  intro Qx;
  obtain ⟨x, hx⟩ := Quotient.exists_rep (cast (h_filter.def_world) Qx);
  obtain ⟨y, Rxy⟩ : ∃ y, x ≺ y := IsSerial.serial x;
  use (cast (h_filter.def_world.symm) ⟦y⟧);
  convert h_filter.def_rel₁ $ Rxy;
  simp_all;
⟩

end


abbrev standardFilterationValuation (Qx : FilterEqvQuotient M T) (a : ℕ) := (ha : (atom a) ∈ T) → Quotient.lift (λ x => M x a) (by
  intro x y h;
  apply eq_iff_iff.mpr;
  constructor;
  . intro hx; exact h a ha |>.mp hx;
  . intro hy; exact h a ha |>.mpr hy;
) Qx


section Coarsest

variable {M FM : Model} {T} [T.IsSubformulaClosed]

abbrev coarsestFilterationFrame (M : Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] : Kripke.Frame where
  World := FilterEqvQuotient M T
  Rel Qx Qy :=
    Quotient.lift₂ (λ x y => ∀ φ, □φ ∈ T → (x ⊧ □φ → y ⊧ φ)) (by
      intro x₁ y₁ x₂ y₂ hx hy;
      apply eq_iff_iff.mpr;
      constructor;
      . intro h φ hp sp₂; exact hy φ (of_mem_box hp) |>.mp $ h φ hp $ hx (□φ) hp |>.mpr sp₂;
      . intro h φ hp sp₁; exact hy φ (of_mem_box hp) |>.mpr $ h φ hp $ hx (□φ) hp |>.mp sp₁;
    ) Qx Qy

abbrev coarsestFilterationModel (M : Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] : Kripke.Model where
  toFrame := coarsestFilterationFrame M T
  Val := standardFilterationValuation M T

instance coarsestFilterationModel.filterOf : FilterOf (coarsestFilterationModel M T) M T where
  def_box := by tauto
  def_rel₁ := by tauto
  def_valuation := by tauto

instance [IsRefl _ M.Rel] : IsRefl _ (coarsestFilterationModel M T).Rel := isRefl_of_filterOf $ coarsestFilterationModel.filterOf
instance [IsSerial _ M.Rel] : IsSerial _ (coarsestFilterationModel M T).Rel := isSerial_of_filterOf $ coarsestFilterationModel.filterOf

end Coarsest



section Finest

variable {M FM : Model} {T}

abbrev finestFilterationFrame (M : Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] : Kripke.Frame where
  World := FilterEqvQuotient M T
  Rel Qx Qy := ∃ x y, Qx = ⟦x⟧ ∧ Qy = ⟦y⟧ ∧ x ≺ y

abbrev finestFilterationModel (M : Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] : Kripke.Model where
  toFrame := finestFilterationFrame M T
  Val := standardFilterationValuation M T


namespace finestFilterationModel

instance filterOf : FilterOf (finestFilterationModel M T) M T where
  def_box := by
    rintro _ _ ⟨x, y, rfl, rfl, Rxy⟩;
    simp_all [Satisfies];
  def_rel₁ := by tauto;

instance isSymm [IsSymm _ M.Rel] : IsSymm _ (finestFilterationModel M T).Rel := ⟨by
  rintro _ _ ⟨x, y, rfl, rfl, Rxy⟩;
  use y, x;
  refine ⟨by trivial, by trivial, IsSymm.symm _ _ Rxy⟩;
⟩

instance isRefl [IsRefl _ M.Rel] : IsRefl _ (finestFilterationFrame M T).Rel := isRefl_of_filterOf finestFilterationModel.filterOf

instance isSerial [IsSerial _ M.Rel] : IsSerial _ (finestFilterationFrame M T).Rel := isSerial_of_filterOf finestFilterationModel.filterOf

end finestFilterationModel


abbrev finestFilterationTransitiveClosureModel (M : Model) (T : FormulaSet ℕ) [T.IsSubformulaClosed] : Kripke.Model where
  toFrame := (finestFilterationFrame M T)^+
  Val := standardFilterationValuation M T

namespace finestFilterationTransitiveClosureModel

instance filterOf [trans : IsTrans _ M.Rel] : FilterOf (finestFilterationTransitiveClosureModel M T) M T where
  def_rel₁ := by
    intro x y hxy;
    apply Relation.TransGen.single;
    dsimp [finestFilterationTransitiveClosureModel, finestFilterationFrame];
    tauto;
  def_box := by
    intro Qx Qy RQxQy;
    induction RQxQy using Relation.TransGen.head_induction_on with
    | base rxy =>
      obtain ⟨x, y, rfl, rfl, rxy⟩ := rxy;
      intro φ _ hpx;
      exact hpx _ rxy;
    | ih ha hxy hyz =>
      obtain ⟨x, y, rfl, rfl, rxy⟩ := ha;
      obtain ⟨w, z, _, rfl, _⟩ := hxy;
      . intro φ hp hpx;
        apply hyz φ hp;
        intro v ryv;
        exact hpx _ (IsTrans.trans _ _ _ rxy ryv);
      . rename_i h;
        obtain ⟨w, z, rfl, rfl, _⟩ := h;
        intro φ hp hpx;
        apply hyz φ hp;
        intro v ryv;
        exact hpx _ (IsTrans.trans _ _ _ rxy ryv);

instance : IsTrans _ (finestFilterationTransitiveClosureModel M T).Rel := by
  dsimp [finestFilterationTransitiveClosureModel]
  infer_instance;

instance [IsPreorder _ M.Rel] : IsRefl _ (finestFilterationTransitiveClosureModel M T).Rel := isRefl_of_filterOf filterOf

instance isPreorder [preorder : IsPreorder _ M.Rel] : IsPreorder _ (finestFilterationTransitiveClosureModel M T).Rel where

instance [IsSerial _ M.Rel] [IsTrans _ M.Rel] : IsSerial _ (finestFilterationTransitiveClosureModel M T).Rel := isSerial_of_filterOf filterOf

instance [IsSymm _ M.Rel] : IsSymm _ (finestFilterationTransitiveClosureModel M T).Rel := by
  apply Frame.mkTransClosure.isSymm

instance isEquiv [IsEquiv _ M.Rel] : IsEquiv _ (finestFilterationTransitiveClosureModel M T).Rel where

end finestFilterationTransitiveClosureModel

end Finest

end


end Kripke

end LO.Modal
