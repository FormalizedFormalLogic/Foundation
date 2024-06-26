import Mathlib.SetTheory.Cardinal.Basic
import Logic.Modal.Standard.Formula
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Kripke.Completeness

namespace Set

-- TODO: move to Vorspiel or Mathlib
-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Set.20is.20finite.2C.20then.20its.20powerset.20is.20finite
lemma powerset_finite_of_finite_set {s : Set α} (hs : s.Finite) : (𝒫 s).Finite := by
  apply Cardinal.lt_aleph0_iff_finite.mp;
  simpa using Cardinal.power_lt_aleph0 (Cardinal.nat_lt_aleph0 2) $ Cardinal.lt_aleph0_iff_finite.mpr hs

end Set


namespace LO.Modal.Standard

variable [DecidableEq α] [Inhabited α]

def Formula.Subformulas: Formula α → Finset (Formula α)
  | ⊤      => {⊤}
  | ⊥      => {⊥}
  | atom a => {(atom a)}
  | p ⟶ q => insert (p ⟶ q) (p.Subformulas ∪ q.Subformulas)
  | p ⋏ q  => {p ⋏ q} ∪ (p.Subformulas ∪ q.Subformulas)
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
    | hbox p ihp =>
      simp_all [Theory.SubformulaClosed, Formula.Subformulas];
      rintro r hp;
      exact Set.Subset.trans (ihp r hp) $ Set.Subset.trans (Set.subset_insert _ _) $ Set.insert_subset_insert $ by rfl;
    | hand p q ihp ihq =>
      simp_all [Theory.SubformulaClosed, Formula.Subformulas];
      rintro r (hp | hq);
      . exact Set.Subset.trans (ihp r hp) $ Set.Subset.trans (Set.subset_insert _ _) $ Set.insert_subset_insert $ Set.subset_union_left;
      . exact Set.Subset.trans (ihq r hq) $ Set.Subset.trans (Set.subset_insert _ _) $ Set.insert_subset_insert $ Set.subset_union_right;
    | hor p q ihp ihq =>
      simp_all [Theory.SubformulaClosed, Formula.Subformulas];
      rintro r (hp | hq);
      . exact Set.Subset.trans (ihp r hp) $ Set.Subset.trans (Set.subset_insert _ _) $ Set.insert_subset_insert $ Set.subset_union_left;
      . exact Set.Subset.trans (ihq r hq) $ Set.Subset.trans (Set.subset_insert _ _) $ Set.insert_subset_insert $ Set.subset_union_right;
    | himp p q ihp ihq =>
      simp_all [Theory.SubformulaClosed, Formula.Subformulas];
      rintro r (hp | hq);
      . exact Set.Subset.trans (ihp r hp) $ Set.Subset.trans (Set.subset_insert _ _) $ Set.insert_subset_insert $ Set.subset_union_left;
      . exact Set.Subset.trans (ihq r hq) $ Set.Subset.trans (Set.subset_insert _ _) $ Set.insert_subset_insert $ Set.subset_union_right;
    | _ => simp_all [Theory.SubformulaClosed, Formula.Subformulas];

namespace Kripke

open Formula (atom)
open Formula.Kripke


section

def filterEquiv (T : Theory α) [T.IsSubformulaClosed] (M : Kripke.Model α) (x y : M.World) := ∀ p ∈ T, x ⊧ p ↔ y ⊧ p

variable (M : Kripke.Model.{u, u} α) (T : Theory α) [T_closed : T.IsSubformulaClosed]

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
  apply Cardinal.lt_aleph0_iff_finite.mp;

  let f : FilterEqvQuotient M T → 𝒫 T := λ (Qx : FilterEqvQuotient M T) => Quotient.lift (λ x => ⟨{ p ∈ T | x ⊧ p }, (by simp_all)⟩) (by
    intro x y hxy;
    simp;
    apply Set.eq_of_subset_of_subset;
    . rintro p ⟨hp, hx⟩; exact ⟨hp, (hxy p hp).mp hx⟩;
    . rintro p ⟨hp, hy⟩; exact ⟨hp, (hxy p hp).mpr hy⟩;
  ) Qx;
  have := Cardinal.mk_le_of_injective (f := f) $ by
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
  apply LE.le.trans_lt this;
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
