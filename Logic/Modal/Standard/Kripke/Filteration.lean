import Logic.Modal.Standard.Formula
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Kripke.Completeness

namespace LO.Modal.Standard

variable [DecidableEq α] [Inhabited α]

def Formula.Subformulas: Formula α → Finset (Formula α)
  | ⊤      => {⊤}
  | ⊥      => {⊥}
  | atom a => {(atom a)}
  | p ⟶ q => insert (p ⟶ q) (p.Subformulas ∪ q.Subformulas)
  | p ⋏ q  => insert (p ⋏ q) (p.Subformulas ∪ q.Subformulas)
  | p ⋎ q  => insert (p ⋎ q) (p.Subformulas ∪ q.Subformulas)
  | box p  => insert (□p) p.Subformulas

namespace Formula.Subformulas

@[simp]
lemma mem_self (p : Formula α) : p ∈ p.Subformulas := by induction p using Formula.rec' <;> simp [Subformulas];

end Formula.Subformulas


def Theory.Subformulas (T : Theory α) := ⋃ i ∈ T, i.Subformulas.toSet

def Theory.SubformulaClosed (T : Theory α) := ∀ p ∈ T, ↑(p.Subformulas) ⊆ T

namespace Theory.SubformulaClosed

variable {T : Theory α} (T_closed : T.SubformulaClosed) {p q : Formula α}

@[simp]
lemma def_and : p ⋏ q ∈ T → p ∈ T ∧ q ∈ T := by
  intro h;
  constructor;
  all_goals apply (T_closed _ h); simp [Formula.Subformulas];

@[simp]
lemma def_or : p ⋎ q ∈ T → p ∈ T ∧ q ∈ T := by
  intro h;
  constructor;
  all_goals apply (T_closed _ h); simp [Formula.Subformulas];

@[simp]
lemma def_imp : p ⟶ q ∈ T → p ∈ T ∧ q ∈ T := by
  intro h;
  constructor;
  all_goals apply (T_closed _ h); simp [Formula.Subformulas];

@[simp]
lemma def_box : □p ∈ T → p ∈ T := by
  intro h;
  apply (T_closed _ h); simp [Formula.Subformulas];

end Theory.SubformulaClosed


class Theory.IsSubformulaClosed (T : Theory α) where
  closed : T.SubformulaClosed

instance {p : Formula α} : Theory.IsSubformulaClosed (p.Subformulas).toSet where
  closed := by
    induction p using Formula.rec' with
    | hand p q ihp ihq =>
      simp_all [Theory.SubformulaClosed, Formula.Subformulas];
      rintro r (hp | hq);
      . have := ihp r hp;
        sorry;
      . have := ihq r hq;
        sorry;
    | hor p q ihp ihq => sorry;
    | himp p q ihp ihq => sorry;
    | hbox p ihp => sorry;
    | _ => simp_all [Theory.SubformulaClosed, Formula.Subformulas];

namespace Kripke

open Formula (atom)
open Formula.Kripke


section

def filterEquiv (T : Theory α) [T.IsSubformulaClosed] (M : Kripke.Model α) (x y : M.World) := ∀ p ∈ T, x ⊧ p ↔ y ⊧ p

variable (M : Kripke.Model α) (T : Theory α) [T_closed : T.IsSubformulaClosed]

lemma filterEquiv.equivalence : Equivalence (filterEquiv T M) where
  refl := by intro x p _; rfl;
  symm := by intro x y h p hp; exact h _ hp |>.symm;
  trans := by
    intro x y z exy eyz;
    intro p hp;
    exact Iff.trans (exy p hp) (eyz p hp)

def FilterEqvSetoid : Setoid (M.World) := ⟨filterEquiv T M, filterEquiv.equivalence M T⟩

abbrev FilterEqvQuotient := Quotient (FilterEqvSetoid M T)

lemma FilterEqvQuotient.finite (T_finite : T.Finite) : Finite (FilterEqvQuotient M T) := by
  sorry;

instance : Inhabited (FilterEqvQuotient M T) := ⟨⟦﹫⟧⟩

class IsFilterationModel (FM : Model α) (M : Model α) (T : Theory α) [T_closed : T.IsSubformulaClosed] where
  def_world : FM.World = FilterEqvQuotient M T := by rfl
  def_rel₁ : ∀ {x y : M.Frame}, x ≺ y → (cast def_world.symm ⟦x⟧) ≺ (cast def_world.symm ⟦y⟧) := by tauto;
  def_rel₂ : ∀ {Qx Qy : FM.World}, Qx ≺ Qy → Quotient.lift₂ (λ x y => ∀ p, □p ∈ T → (x ⊧ □p → y ⊧ p)) (by
    intro x₁ y₁ x₂ y₂ hx hy;
    simp;
    constructor;
    . intro h p hp sp₂;
      exact hy _ (T_closed.closed.def_box hp) |>.mp $ h p hp $ hx _ hp |>.mpr sp₂;
    . intro h p hp sp₁;
      exact hy _ (T_closed.closed.def_box hp) |>.mpr $ h p hp $ hx _ hp |>.mp sp₁;
  ) (cast def_world Qx) (cast def_world Qy) := by tauto;
  def_valuation Qx a : (ha : (atom a) ∈ T) →
    FM.Valuation Qx a ↔ Quotient.lift (λ x => M.Valuation x a) (by
      simp; intro x y h;
      constructor;
      . intro hx; exact h a ha |>.mp hx;
      . intro hy; exact h a ha |>.mpr hy;
    ) (cast def_world Qx) := by tauto;

abbrev FinestFilterationFrame (M : Model α) (T : Theory α) [T.IsSubformulaClosed] : Kripke.Frame where
  World := FilterEqvQuotient M T
  Rel := λ Qx Qy => ∃ x y, Qx = ⟦x⟧ ∧ Qy = ⟦y⟧ ∧ x ≺ y

abbrev FinestFilterationModel (M : Model α) (T : Theory α) [T.IsSubformulaClosed] : Kripke.Model α where
  Frame := FinestFilterationFrame M T
  Valuation Qx a := (ha : (atom a) ∈ T) → Quotient.lift (λ x => M.Valuation x a) (by
    simp; intro x y h;
    constructor;
    . intro hx; exact h a ha |>.mp hx;
    . intro hy; exact h a ha |>.mpr hy;
  ) Qx

instance instFinestFilteration {T : Theory α} [T.IsSubformulaClosed] {M} : IsFilterationModel (FinestFilterationModel M T) M T where
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

abbrev CoarsestFilterationModel (M : Model α) (T : Theory α) [T.IsSubformulaClosed] : Kripke.Model α where
  Frame := CoarsestFilterationFrame M T
  Valuation Qx a := (ha : (atom a) ∈ T) → Quotient.lift (λ x => M.Valuation x a) (by
    simp; intro x y h;
    constructor;
    . intro hx; exact h a ha |>.mp hx;
    . intro hy; exact h a ha |>.mpr hy;
  ) Qx

instance instCoarsestFilteration {T : Theory α} [T.IsSubformulaClosed] {M} : IsFilterationModel (CoarsestFilterationModel M T) M T where

end


section

variable {M : Model α} {T : Theory α} [T_closed : T.IsSubformulaClosed]
variable (FM : Model α) [FM_filter : IsFilterationModel FM M T]

theorem filteration {x : M.World} {p : Formula α} (hs : p ∈ T) : x ⊧ p ↔ (cast FM_filter.def_world.symm ⟦x⟧) ⊧ p := by
  induction p using Formula.rec' generalizing x with
  | hatom a =>
    have := FM_filter.def_valuation (cast FM_filter.def_world.symm ⟦x⟧) a hs;
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
      obtain ⟨y, ey⟩ := Quotient.exists_rep (cast FM_filter.def_world Qy);
      have H := FM_filter.def_rel₂ rQxQy;
      simp [←ey] at H;
      have h₂ := @ihp y (T_closed.closed.def_box hs) |>.mp $ @H p hs h;
      simpa [ey] using h₂;
    . intro h y rxy;
      have rQxQy := FM_filter.def_rel₁ rxy;
      exact ihp (T_closed.closed.def_box hs) |>.mpr $ h rQxQy;
  | _ => simp_all;

end

instance K_finite_complete : Complete (𝐊 : DeductionParameter α) AllFrameClassꟳ# := ⟨by
  intro p hp;
  apply K_complete.complete;
  intro F _ V x;
  let FM : Kripke.Model α := CoarsestFilterationModel ⟨F, V⟩ p.Subformulas;
  have := instCoarsestFilteration (T := p.Subformulas.toSet) (M := ⟨F, V⟩); -- TODO: remove this?

  apply filteration (T := p.Subformulas) FM (by simp) |>.mpr;
  apply hp (by
    simp [FrameClass.restrictFinite, AllFrameClass, FrameClass.alt, FiniteFrameClass.toFrameClass];
    suffices Finite (FilterEqvQuotient ⟨F, V⟩ p.Subformulas) by use ⟨FM.Frame⟩;
    apply FilterEqvQuotient.finite;
    simp_all;
  ) FM.Valuation
⟩

end Kripke

end LO.Modal.Standard
