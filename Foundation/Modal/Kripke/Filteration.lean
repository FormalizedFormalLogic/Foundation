import Mathlib.Data.Set.Finite.Powerset
import Foundation.Modal.Kripke.Closure
import Foundation.Modal.Subformulas

universe u v

namespace LO.Modal

namespace Kripke

open Formula (atom)
open Formula.Kripke
open FormulaSet.SubformulaClosed


section

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
  def_rel₁ : ∀ {x y : M.toFrame}, x ≺ y → Frame.Rel' (cast def_world.symm ⟦x⟧) (cast def_world.symm ⟦y⟧) := by tauto;
  def_box : ∀ {Qx Qy : FM.World}, Qx ≺ Qy → Quotient.lift₂ (λ x y => ∀ φ, □φ ∈ T → (x ⊧ □φ → y ⊧ φ)) (by
    intro x₁ y₁ x₂ y₂ hx hy;
    apply eq_iff_iff.mpr;
    constructor;
    . intro h φ hp sp₂; exact hy φ (FormulaSet.SubformulaClosed.mem_box hp) |>.mp $ h φ hp $ hx (□φ) hp |>.mpr sp₂;
    . intro h φ hp sp₁; exact hy φ (FormulaSet.SubformulaClosed.mem_box hp) |>.mpr $ h φ hp $ hx (□φ) hp |>.mp sp₁;
  ) (cast def_world Qx) (cast def_world Qy)
  def_valuation Qx a : (ha : (atom a) ∈ T := by trivial) →
    FM Qx a ↔ Quotient.lift (λ x => M x a) (by
      intro x y h;
      apply eq_iff_iff.mpr;
      constructor;
      . intro hx; exact h a ha |>.mp hx;
      . intro hy; exact h a ha |>.mpr hy;
    ) (cast def_world Qx) := by tauto;

attribute [simp] FilterOf.def_world

section

variable {M T}

lemma reflexive_filterOf_of_reflexive (h_filter : FilterOf FM M T) (hRefl : Reflexive M.toFrame) : Reflexive FM.Rel := by
  intro Qx;
  obtain ⟨x, hx⟩ := Quotient.exists_rep (cast (h_filter.def_world) Qx);
  convert h_filter.def_rel₁ $ hRefl x <;> simp_all;

lemma serial_filterOf_of_serial (h_filter : FilterOf FM M T) (hSerial : Serial M.toFrame) : Serial FM.Rel := by
  intro Qx;
  obtain ⟨x, hx⟩ := Quotient.exists_rep (cast (h_filter.def_world) Qx);
  obtain ⟨y, Rxy⟩ := hSerial x;
  use (cast (h_filter.def_world.symm) ⟦y⟧);
  convert h_filter.def_rel₁ $ Rxy;
  simp_all;

end


abbrev standardFilterationValuation (Qx : FilterEqvQuotient M T) (a : ℕ) := (ha : (atom a) ∈ T) → Quotient.lift (λ x => M x a) (by
  intro x y h;
  apply eq_iff_iff.mpr;
  constructor;
  . intro hx; exact h a ha |>.mp hx;
  . intro hy; exact h a ha |>.mpr hy;
) Qx


abbrev coarsestFilterationFrame (M : Model) (T : FormulaSet ℕ) [T.SubformulaClosed] : Kripke.Frame where
  World := FilterEqvQuotient M T
  Rel Qx Qy :=
    Quotient.lift₂ (λ x y => ∀ φ, □φ ∈ T → (x ⊧ □φ → y ⊧ φ)) (by
      intro x₁ y₁ x₂ y₂ hx hy;
      apply eq_iff_iff.mpr;
      constructor;
      . intro h φ hp sp₂; exact hy φ (FormulaSet.SubformulaClosed.mem_box hp) |>.mp $ h φ hp $ hx (□φ) hp |>.mpr sp₂;
      . intro h φ hp sp₁; exact hy φ (FormulaSet.SubformulaClosed.mem_box hp) |>.mpr $ h φ hp $ hx (□φ) hp |>.mp sp₁;
    ) Qx Qy

abbrev coarsestFilterationModel (M : Model) (T : FormulaSet ℕ) [T.SubformulaClosed] : Kripke.Model where
  toFrame := coarsestFilterationFrame M T
  Val := standardFilterationValuation M T

instance coarsestFilterationModel.filterOf {M} {T : FormulaSet ℕ} [T.SubformulaClosed] : FilterOf (coarsestFilterationModel M T) M T where
  def_box := by tauto


abbrev finestFilterationFrame (M : Model) (T : FormulaSet ℕ) [T.SubformulaClosed] : Kripke.Frame where
  World := FilterEqvQuotient M T
  Rel Qx Qy := ∃ x y, Qx = ⟦x⟧ ∧ Qy = ⟦y⟧ ∧ x ≺ y

abbrev finestFilterationModel (M : Model) (T : FormulaSet ℕ) [T.SubformulaClosed] : Kripke.Model where
  toFrame := finestFilterationFrame M T
  Val := standardFilterationValuation M T

namespace finestFilterationModel

variable {M T}

instance filterOf [T.SubformulaClosed] : FilterOf (finestFilterationModel M T) M T where
  def_box := by
    intro Qx Qy rQxQy;
    obtain ⟨x, y, rfl, rfl, _⟩ := rQxQy;
    simp_all [Satisfies];

lemma symmetric_of_symmetric (hSymm : Symmetric M.toFrame) : Symmetric (finestFilterationModel M T).Rel := by
  intro Qx Qy RQxQy;
  obtain ⟨x, y, hx, hy, h⟩ := RQxQy; subst_vars;
  use y, x;
  refine ⟨by trivial, by trivial, hSymm h⟩;

end finestFilterationModel


abbrev finestFilterationTransitiveClosureModel (M : Model) (T : FormulaSet ℕ) [T.SubformulaClosed] : Kripke.Model where
  toFrame := (finestFilterationFrame M T)^+
  Val := standardFilterationValuation M T

namespace finestFilterationTransitiveClosureModel

variable {M T}

instance filterOf (M_trans : Transitive M.Rel) : FilterOf (finestFilterationTransitiveClosureModel M T) M T where
  def_rel₁ := by
    intro x y hxy;
    apply Relation.TransGen.single;
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

lemma transitive : Transitive (finestFilterationTransitiveClosureModel M T).Rel := Frame.RelTransGen.transitive

lemma symmetric_of_symmetric (M_symm : Symmetric M.Rel) : Symmetric (finestFilterationTransitiveClosureModel M T).Rel :=
  Frame.RelTransGen.symmetric $ finestFilterationModel.symmetric_of_symmetric M_symm

lemma reflexive_of_transitive_reflexive (M_trans : Transitive M.Rel) (M_refl : Reflexive M.Rel) : Reflexive (finestFilterationTransitiveClosureModel M T).Rel := by
  exact reflexive_filterOf_of_reflexive (filterOf M_trans) M_refl;

end finestFilterationTransitiveClosureModel

end


section

variable {M : Model} {T : FormulaSet ℕ} [T.SubformulaClosed]
         (FM : Model) (filterOf : FilterOf FM M T)

theorem filteration {x : M.World} {φ : Formula ℕ} (hs : φ ∈ T) : x ⊧ φ ↔ (cast (filterOf.def_world.symm) ⟦x⟧) ⊧ φ := by
  induction φ using Formula.rec' generalizing x with
  | hatom a =>
    have := filterOf.def_valuation (cast filterOf.def_world.symm ⟦x⟧) a;
    simp_all [Satisfies];
  | hbox φ ihp =>
    constructor;
    . intro h Qy rQxQy;
      obtain ⟨y, ey⟩ := Quotient.exists_rep (cast (filterOf.def_world) Qy);
      have this := filterOf.def_box rQxQy; simp [←ey] at this;
      simpa [ey] using ihp (FormulaSet.SubformulaClosed.mem_box hs) |>.mp $ @this φ hs h;
    . intro h y rxy;
      have rQxQy := filterOf.def_rel₁ rxy;
      exact ihp (FormulaSet.SubformulaClosed.mem_box hs) |>.mpr $ h _ rQxQy;
  | himp φ ψ ihp ihq =>
    constructor;
    . rintro hxy hp;
      exact ihq (FormulaSet.SubformulaClosed.mem_imp₂ hs) |>.mp $ hxy (ihp (FormulaSet.SubformulaClosed.mem_imp₁ hs) |>.mpr hp);
    . rintro hxy hp;
      exact ihq (FormulaSet.SubformulaClosed.mem_imp₂ hs) |>.mpr $ hxy (ihp (FormulaSet.SubformulaClosed.mem_imp₁ hs) |>.mp hp);
  | _ => trivial

end

end Kripke

end LO.Modal
