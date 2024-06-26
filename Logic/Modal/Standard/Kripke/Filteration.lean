import Mathlib.SetTheory.Cardinal.Basic
import Logic.Modal.Standard.Formula
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Kripke.Completeness

universe u v

namespace Set

-- TODO: move to Vorspiel or Mathlib
-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Set.20is.20finite.2C.20then.20its.20powerset.20is.20finite/near/447338619
lemma powerset_finite_of_finite_set {s : Set α} (hs : s.Finite) : (𝒫 s).Finite := Set.Finite.finite_subsets hs

end Set


namespace LO.Modal.Standard

variable {α : Type u} [DecidableEq α]

namespace Kripke

open Formula (atom)
open Formula.Kripke

section

def filterEquiv (M : Kripke.Model α) (T : Theory α) [T.IsSubformulaClosed] (x y : M.World) := ∀ p ∈ T, x ⊧ p ↔ y ⊧ p

-- TODO: Model universe specifying is not needed: should be `Model.{u, v}`.
variable (M : Kripke.Model.{u, u} α) (T : Theory α) [T_closed : T.IsSubformulaClosed]

lemma filterEquiv.equivalence : Equivalence (filterEquiv M T) where
  refl := by intro x p _; rfl;
  symm := by intro x y h p hp; exact h _ hp |>.symm;
  trans := by
    intro x y z exy eyz;
    intro p hp;
    exact Iff.trans (exy p hp) (eyz p hp)

def FilterEqvSetoid : Setoid (M.World) := ⟨filterEquiv M T, filterEquiv.equivalence M T⟩

abbrev FilterEqvQuotient := Quotient (FilterEqvSetoid M T)

-- set_option pp.universes true in
lemma FilterEqvQuotient.finite (T_finite : T.Finite) : Finite (FilterEqvQuotient M T) := by
  apply Cardinal.lt_aleph0_iff_finite.mp;

  let f : FilterEqvQuotient M T → 𝒫 T := λ (Qx : FilterEqvQuotient M T) => Quotient.lift (λ x => ⟨{ p ∈ T | x ⊧ p }, (by simp_all)⟩) (by
    intro x y hxy; simp;
    apply Set.eq_of_subset_of_subset;
    . rintro p ⟨hp, hx⟩; exact ⟨hp, (hxy p hp).mp hx⟩;
    . rintro p ⟨hp, hy⟩; exact ⟨hp, (hxy p hp).mpr hy⟩;
  ) Qx;
  apply LE.le.trans_lt $ Cardinal.mk_le_of_injective (f := f) $ by
      intro Qx Qy h;
      obtain ⟨x, hx⟩ := Quotient.exists_rep Qx; subst hx;
      obtain ⟨y, hy⟩ := Quotient.exists_rep Qy; subst hy;
      simp [f] at h;
      apply Quotient.eq''.mpr;
      intro p hp;
      constructor;
      . intro hpx;
        have := h.subset; simp at this;
        exact this p hp hpx |>.2;
      . intro hpy;
        have := h.symm.subset; simp at this;
        exact this p hp hpy |>.2;
  apply Set.Finite.lt_aleph0;
  exact Set.powerset_finite_of_finite_set T_finite;

instance : Inhabited (FilterEqvQuotient M T) := ⟨⟦﹫⟧⟩

class FilterationModel (M : Model α) (T : Theory α) [T_closed : T.IsSubformulaClosed] extends Model α where
  def_world : Frame.World = FilterEqvQuotient M T := by rfl
  def_rel₁ : ∀ {x y : M.Frame}, x ≺ y → Frame.Rel' (cast def_world.symm ⟦x⟧) (cast def_world.symm ⟦y⟧) := by tauto;
  def_rel₂ : ∀ {Qx Qy : Frame.World}, Qx ≺ Qy → Quotient.lift₂ (λ x y => ∀ p, □p ∈ T → (x ⊧ □p → y ⊧ p)) (by
    intro x₁ y₁ x₂ y₂ hx hy;
    simp;
    constructor;
    . intro h p hp sp₂;
      exact hy _ (T_closed.closed.def_box hp) |>.mp $ h p hp $ hx _ hp |>.mpr sp₂;
    . intro h p hp sp₁;
      exact hy _ (T_closed.closed.def_box hp) |>.mpr $ h p hp $ hx _ hp |>.mp sp₁;
  ) (cast def_world Qx) (cast def_world Qy) := by tauto;
  def_valuation Qx a : (ha : (atom a) ∈ T) →
    Valuation Qx a ↔ Quotient.lift (λ x => M.Valuation x a) (by
      simp; intro x y h;
      constructor;
      . intro hx; exact h a ha |>.mp hx;
      . intro hy; exact h a ha |>.mpr hy;
    ) (cast def_world Qx) := by tauto;

abbrev FinestFilterationFrame (M : Model α) (T : Theory α) [T.IsSubformulaClosed] : Kripke.Frame where
  World := FilterEqvQuotient M T
  Rel := λ Qx Qy => ∃ x y, Qx = ⟦x⟧ ∧ Qy = ⟦y⟧ ∧ x ≺ y

abbrev FinestFilterationModel (M : Model α) (T : Theory α) [T.IsSubformulaClosed] : Kripke.FilterationModel M T where
  Frame := FinestFilterationFrame M T
  Valuation Qx a := (ha : (atom a) ∈ T) → Quotient.lift (λ x => M.Valuation x a) (by
    simp; intro x y h;
    constructor;
    . intro hx; exact h a ha |>.mp hx;
    . intro hy; exact h a ha |>.mpr hy;
  ) Qx
  def_rel₂ := by
    intro Qx Qy rQxQy;
    obtain ⟨x, y, rfl, rfl, hxy⟩ := rQxQy;
    simp_all [Satisfies];


abbrev CoarsestFilterationFrame (M : Model α) (T : Theory α) [T_closed : T.IsSubformulaClosed] : Kripke.Frame where
  World := FilterEqvQuotient M T
  Rel := λ Qx Qy => Quotient.lift₂ (λ x y => ∀ p, □p ∈ T → (x ⊧ □p → y ⊧ p)) (by
    intro x₁ y₁ x₂ y₂ hx hy;
    simp;
    constructor;
    . intro h p hp sp₂;
      exact hy _ (T_closed.closed.def_box hp) |>.mp $ h p hp $ hx _ hp |>.mpr sp₂;
    . intro h p hp sp₁;
      exact hy _ (T_closed.closed.def_box hp) |>.mpr $ h p hp $ hx _ hp |>.mp sp₁;
  ) Qx Qy

abbrev CoarsestFilterationModel (M : Model α) (T : Theory α) [T.IsSubformulaClosed] : Kripke.FilterationModel M T where
  Frame := CoarsestFilterationFrame M T
  Valuation Qx a := (ha : (atom a) ∈ T) → Quotient.lift (λ x => M.Valuation x a) (by
    simp; intro x y h;
    constructor;
    . intro hx; exact h a ha |>.mp hx;
    . intro hy; exact h a ha |>.mpr hy;
  ) Qx

end


section

variable {M : Model α} {T : Theory α} [T_closed : T.IsSubformulaClosed]
variable (FM : Kripke.FilterationModel M T)

theorem filteration {x : M.World} {p : Formula α} (hs : p ∈ T) : x ⊧ p ↔ (cast FM.def_world.symm ⟦x⟧) ⊧ p := by
  induction p using Formula.rec' generalizing x with
  | hatom a =>
    have := FM.def_valuation (cast FM.def_world.symm ⟦x⟧) a hs;
    simp_all [Satisfies];
  | hand p q ihp ihq =>
    constructor;
    . have ⟨sp, sq⟩ := T_closed.closed.def_and hs
      rintro ⟨hp, hq⟩;
      constructor;
      . exact ihp sp |>.mp hp;
      . exact ihq sq |>.mp hq;
    . have ⟨sp, sq⟩ := T_closed.closed.def_and hs
      rintro ⟨hp, hq⟩;
      constructor;
      . exact ihp sp |>.mpr hp;
      . exact ihq sq |>.mpr hq;
  | hor p q ihp ihq =>
    constructor;
    . have ⟨sp, sq⟩ := T_closed.closed.def_or hs
      rintro (hp | hq);
      . left; exact (ihp sp |>.mp hp);
      . right; exact (ihq sq |>.mp hq);
    . have ⟨sp, sq⟩ := T_closed.closed.def_or hs
      rintro (hp | hq);
      . left; exact (ihp sp |>.mpr hp);
      . right; exact (ihq sq |>.mpr hq);
  | himp p q ihp ihq =>
    constructor;
    . have ⟨sp, sq⟩ := T_closed.closed.def_imp hs
      rintro hxy hp;
      exact (ihq sq |>.mp $ hxy (ihp sp |>.mpr hp));
    . rintro hxy hp;
      have ⟨sp, sq⟩ := T_closed.closed.def_imp hs
      exact (ihq sq |>.mpr $ hxy (ihp sp |>.mp hp));
  | hbox p ihp =>
    constructor;
    . intro h Qy rQxQy;
      obtain ⟨y, ey⟩ := Quotient.exists_rep (cast FM.def_world Qy);
      have H := FM.def_rel₂ rQxQy;
      simp [←ey] at H;
      have h₂ := @ihp y (T_closed.closed.def_box hs) |>.mp $ @H p hs h;
      simpa [ey] using h₂;
    . intro h y rxy;
      have rQxQy := FM.def_rel₁ rxy;
      exact ihp (T_closed.closed.def_box hs) |>.mpr $ h rQxQy;
  | _ => simp_all;

end

instance K_finite_complete : Complete (𝐊 : DeductionParameter α) AllFrameClassꟳ# := ⟨by
  intro p hp;
  apply K_complete.complete;
  intro F _ V x;
  let M : Kripke.Model α := ⟨F, V⟩;
  let FM : Kripke.FilterationModel M p.Subformulas := CoarsestFilterationModel M p.Subformulas;

  apply filteration FM (by simp) |>.mpr;
  apply hp (by
    suffices Finite (FilterEqvQuotient M p.Subformulas) by simp; use ⟨FM.Frame⟩;
    apply FilterEqvQuotient.finite;
    simp_all;
  ) FM.Valuation
⟩

class FiniteFrameProperty (Λ : DeductionParameter α) where
  FFC : FiniteFrameClass
  [complete : Complete Λ FFC#]

instance : FiniteFrameProperty (α := α) 𝐊 where
  FFC := AllFrameClassꟳ

end Kripke

end LO.Modal.Standard
