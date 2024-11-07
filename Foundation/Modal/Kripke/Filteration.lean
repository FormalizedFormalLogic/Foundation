import Foundation.Logic.Kripke.Closure
import Foundation.Modal.Kripke.Completeness
import Foundation.Modal.Kripke.Geach

universe u v

namespace LO.Modal

variable {α : Type u} -- [DecidableEq α] [Inhabited α]

namespace Kripke

open LO.Kripke
open Formula (atom)
open Formula.Kripke

section

def filterEquiv (M : Kripke.Model α) (T : Theory α) [T.SubformulaClosed] (x y : M.World) := ∀ φ, (_ : φ ∈ T := by trivial) → x ⊧ φ ↔ y ⊧ φ

variable (M : Kripke.Model α) (T : Theory α) [T.SubformulaClosed]

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
      intro x y hxy; simp;
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
      have := h.subset; simp at this;
      exact this φ hp hpx |>.2;
    . intro hpy;
      have := h.symm.subset; simp at this;
      exact this φ hp hpy |>.2;
  exact Finite.of_injective f hf

instance : Nonempty (FilterEqvQuotient M T) := ⟨⟦﹫⟧⟩

class FilterOf (FM : Model α) (M : Model α) (T : Theory α) [T.SubformulaClosed] where
  def_world : FM.World = FilterEqvQuotient M T := by rfl
  def_rel₁ : ∀ {x y : M.Frame}, x ≺ y → Frame.Rel' (cast def_world.symm ⟦x⟧) (cast def_world.symm ⟦y⟧) := by tauto;
  def_box : ∀ {Qx Qy : FM.World}, Qx ≺ Qy → Quotient.lift₂ (λ x y => ∀ φ, □φ ∈ T → (x ⊧ □φ → y ⊧ φ)) (by
    intro x₁ y₁ x₂ y₂ hx hy;
    simp;
    constructor;
    . intro h φ hp sp₂; exact hy φ |>.mp $ h φ hp $ hx (□φ) hp |>.mpr sp₂;
    . intro h φ hp sp₁; exact hy φ |>.mpr $ h φ hp $ hx (□φ) hp |>.mp sp₁;
  ) (cast def_world Qx) (cast def_world Qy)
  def_valuation Qx a : (ha : (atom a) ∈ T := by trivial) →
    FM.Valuation Qx a ↔ Quotient.lift (λ x => M.Valuation x a) (by
      simp; intro x y h;
      constructor;
      . intro hx; exact h a ha |>.mp hx;
      . intro hy; exact h a ha |>.mpr hy;
    ) (cast def_world Qx) := by tauto;

attribute [simp] FilterOf.def_world

namespace FilterationModel

end FilterationModel

abbrev StandardFilterationValuation (Qx : FilterEqvQuotient M T) (a : α) := (ha : (atom a) ∈ T) → Quotient.lift (λ x => M.Valuation x a) (by
  simp; intro x y h;
  constructor;
  . intro hx; exact h a ha |>.mp hx;
  . intro hy; exact h a ha |>.mpr hy;
) Qx


abbrev FinestFilterationFrame (M : Model α) (T : Theory α) [T.SubformulaClosed] : Kripke.Frame where
  World := FilterEqvQuotient M T
  Rel Qx Qy := ∃ x y, Qx = ⟦x⟧ ∧ Qy = ⟦y⟧ ∧ x ≺ y

abbrev FinestFilterationModel (M : Model α) (T : Theory α) [T.SubformulaClosed] : Kripke.Model α where
  Frame := FinestFilterationFrame M T
  Valuation := StandardFilterationValuation M T

instance FinestFilterationModel.filterOf {M} {T : Theory α} [T.SubformulaClosed] : FilterOf (FinestFilterationModel M T) M T where
  def_box := by
    intro Qx Qy rQxQy;
    obtain ⟨x, y, rfl, rfl, hxy⟩ := rQxQy;
    simp_all [Satisfies];

abbrev CoarsestFilterationFrame (M : Model α) (T : Theory α) [T.SubformulaClosed] : Kripke.Frame where
  World := FilterEqvQuotient M T
  Rel Qx Qy :=
    Quotient.lift₂ (λ x y => ∀ φ, □φ ∈ T → (x ⊧ □φ → y ⊧ φ)) (by
      intro x₁ y₁ x₂ y₂ hx hy;
      simp;
      constructor;
      . intro h φ hp sp₂; exact hy φ |>.mp $ h φ hp $ hx (□φ) hp |>.mpr sp₂;
      . intro h φ hp sp₁; exact hy φ |>.mpr $ h φ hp $ hx (□φ) hp |>.mp sp₁;
    ) Qx Qy

abbrev CoarsestFilterationModel (M : Model α) (T : Theory α) [T.SubformulaClosed] : Kripke.Model α where
  Frame := CoarsestFilterationFrame M T
  Valuation := StandardFilterationValuation M T

instance CoarsestFilterationModel.filterOf {M} {T : Theory α} [T.SubformulaClosed] : FilterOf (CoarsestFilterationModel M T) M T where
  def_box := by tauto

section

variable {M} {T : Theory α} [T.SubformulaClosed] {FM : Kripke.Model α}

lemma reflexive_filteration_model (h_filter : FilterOf FM M T) (hRefl : Reflexive M.Frame) : Reflexive FM.Frame := by
  intro Qx;
  obtain ⟨x, hx⟩ := Quotient.exists_rep (cast (h_filter.def_world) Qx);
  convert h_filter.def_rel₁ $ hRefl x <;> simp_all;

lemma serial_filteration_model (h_filter : FilterOf FM M T) (hSerial : Serial M.Frame) : Serial FM.Frame := by
  intro Qx;
  obtain ⟨x, hx⟩ := Quotient.exists_rep (cast (h_filter.def_world) Qx);
  obtain ⟨y, Rxy⟩ := hSerial x;
  use (cast (h_filter.def_world.symm) ⟦y⟧);
  convert h_filter.def_rel₁ $ Rxy;
  simp_all;

lemma symmetric_finest_filteration_model (hSymm : Symmetric M.Frame) : Symmetric (FinestFilterationModel M T).Frame := by
  intro Qx Qy RQxQy;
  obtain ⟨x, y, hx, hy, h⟩ := RQxQy; subst_vars;
  use y, x; simp;
  exact hSymm h;

end

end


section

variable {M : Model α} {T : Theory α} [T.SubformulaClosed]
         (FM : Model α) (filterOf : FilterOf FM M T)

theorem filteration {x : M.World} {φ : Formula α} (hs : φ ∈ T := by trivial) : x ⊧ φ ↔ (cast (filterOf.def_world.symm) ⟦x⟧) ⊧ φ := by
  induction φ using Formula.rec' generalizing x with
  | hatom a =>
    have := filterOf.def_valuation (cast filterOf.def_world.symm ⟦x⟧) a;
    simp_all [Satisfies];
  | hbox φ ihp =>
    constructor;
    . intro h Qy rQxQy;
      obtain ⟨y, ey⟩ := Quotient.exists_rep (cast (filterOf.def_world) Qy);
      have this := filterOf.def_box rQxQy; simp [←ey] at this;
      simpa [ey] using ihp (by trivial) |>.mp $ @this φ hs h;
    . intro h y rxy;
      have rQxQy := filterOf.def_rel₁ rxy;
      exact ihp (by trivial) |>.mpr $ h _ rQxQy;
  | himp φ ψ ihp ihq =>
    constructor;
    . rintro hxy hp;
      exact (ihq (by trivial) |>.mp $ hxy (ihp (by trivial) |>.mpr hp));
    . rintro hxy hp;
      exact (ihq (by trivial) |>.mpr $ hxy (ihp (by trivial) |>.mp hp));
  | _ => trivial

end

instance K_finite_complete [DecidableEq α] : Complete (Hilbert.K α) (AllFrameClass.{u}ꟳ#α) := ⟨by
  intro φ hp;
  apply K_complete.complete;
  intro F _ V x;
  let M : Kripke.Model α := ⟨F, V⟩;
  let FM := CoarsestFilterationModel M ↑φ.subformulae;

  apply filteration FM (CoarsestFilterationModel.filterOf) (by aesop) |>.mpr;
  apply hp (by
    suffices Finite (FilterEqvQuotient M φ.subformulae) by simp; use ⟨FM.Frame⟩;
    apply FilterEqvQuotient.finite;
    simp;
  ) FM.Valuation
⟩

instance  [DecidableEq α] : FiniteFrameProperty (Hilbert.K α) AllFrameClass where


instance KTB_finite_complete [DecidableEq α] [Inhabited α] : Complete (Hilbert.KTB α) (ReflexiveSymmetricFrameClass.{u}ꟳ#α) := ⟨by
  intro φ hp;
  apply KTB_complete.complete;
  intro F ⟨F_refl, F_symm⟩ V x;
  let M : Kripke.Model α := ⟨F, V⟩;
  let FM := FinestFilterationModel M φ.subformulae;
  apply filteration FM (FinestFilterationModel.filterOf) (by aesop) |>.mpr;
  apply hp (by
    suffices Finite (FilterEqvQuotient M φ.subformulae) by
      use ⟨FM.Frame⟩;
      refine ⟨⟨?_, ?_⟩, ?_⟩;
      . apply reflexive_filteration_model (FinestFilterationModel.filterOf);
        exact F_refl;
      . apply symmetric_finest_filteration_model;
        exact F_symm;
      . rfl;
    apply FilterEqvQuotient.finite;
    simp;
  ) FM.Valuation
⟩

instance [DecidableEq α] [Inhabited α] : FiniteFrameProperty (Hilbert.KTB α) ReflexiveSymmetricFrameClass where

section

open Kripke.Frame (TransitiveClosure)

variable {M : Model α} {T : Theory α} [T.SubformulaClosed]

abbrev FinestFilterationTransitiveClosureModel (M : Model α) (T : Theory α) [T.SubformulaClosed] : Kripke.Model α where
  Frame := (FinestFilterationFrame M T)^+
  Valuation := StandardFilterationValuation M T

namespace FinestFilterationTransitiveClosureModel

instance filterOf (M_trans : Transitive M.Frame) : FilterOf (FinestFilterationTransitiveClosureModel M T) M T where
  def_rel₁ := by
    intro x y hxy;
    apply TransitiveClosure.single;
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
        exact hpx _ (M_trans rxy ryv);
      . rename_i h;
        obtain ⟨w, z, rfl, rfl, _⟩ := h;
        intro φ hp hpx;
        apply hyz φ hp;
        intro v ryv;
        exact hpx _ (M_trans rxy ryv);

lemma rel_transitive : Transitive (FinestFilterationTransitiveClosureModel M T).Frame := Frame.TransitiveClosure.rel_transitive

lemma rel_symmetric (M_symm : Symmetric M.Frame) : Symmetric (FinestFilterationTransitiveClosureModel M T).Frame :=
  Frame.TransitiveClosure.rel_symmetric $ symmetric_finest_filteration_model M_symm

lemma rel_reflexive (M_trans : Transitive M.Frame) (M_refl : Reflexive M.Frame) : Reflexive (FinestFilterationTransitiveClosureModel M T).Frame := by
  exact reflexive_filteration_model (filterOf M_trans) M_refl;

end FinestFilterationTransitiveClosureModel

end

open FinestFilterationTransitiveClosureModel in
instance S4_finite_complete [Inhabited α] [DecidableEq α] : Complete (Hilbert.S4 α) (PreorderFrameClass.{u}ꟳ#α) := ⟨by
  intro φ hp;
  apply S4_complete.complete;
  intro F ⟨F_refl, F_trans⟩ V x;
  let M : Kripke.Model α := ⟨F, V⟩;
  let FM := FinestFilterationTransitiveClosureModel M φ.subformulae;
  apply @filteration α M φ.subformulae _ FM ?filterOf x φ (by simp) |>.mpr;
  apply hp (by
    suffices Finite (FilterEqvQuotient M φ.subformulae) by
      use ⟨FM.Frame⟩;
      refine ⟨⟨?_, rel_transitive⟩, rfl⟩;
      . exact rel_reflexive (by apply F_trans) F_refl;
    apply FilterEqvQuotient.finite;
    simp;
  ) FM.Valuation;
  . apply FinestFilterationTransitiveClosureModel.filterOf;
    exact F_trans;
⟩

instance [Inhabited α] [DecidableEq α] : FiniteFrameProperty (Hilbert.S4 α) PreorderFrameClass where


open FinestFilterationTransitiveClosureModel in
instance KT4B_finite_complete [Inhabited α] [DecidableEq α] : Complete (Hilbert.KT4B α) (EquivalenceFrameClass.{u}ꟳ#α) := ⟨by
  intro φ hp;
  apply KT4B_complete.complete;
  intro F ⟨F_refl, F_trans, F_symm⟩ V x;
  let M : Kripke.Model α := ⟨F, V⟩;
  let FM := FinestFilterationTransitiveClosureModel M φ.subformulae;
  apply @filteration α M φ.subformulae _ FM ?filterOf x φ (by simp) |>.mpr;
  apply hp (by
    suffices Finite (FilterEqvQuotient M φ.subformulae) by
      use ⟨FM.Frame⟩;
      refine ⟨⟨?refl, rel_transitive, ?symm⟩, rfl⟩;
      . exact rel_reflexive (by apply F_trans) F_refl;
      . exact rel_symmetric F_symm;
    apply FilterEqvQuotient.finite;
    simp;
  ) FM.Valuation;
  . apply FinestFilterationTransitiveClosureModel.filterOf
    exact F_trans;
⟩

instance [Inhabited α] [DecidableEq α] : FiniteFrameProperty (Hilbert.KT4B α) EquivalenceFrameClass where
-- MEMO: `𝐒𝟓 =ₛ 𝐊𝐓𝟒𝐁`だから決定可能性という面では`𝐒𝟓`も決定可能．

end Kripke

end LO.Modal
