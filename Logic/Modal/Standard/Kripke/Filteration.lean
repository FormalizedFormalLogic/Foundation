import Logic.Modal.Standard.Kripke.Completeness
import Logic.Modal.Standard.Kripke.Geach

universe u v

namespace LO.Modal.Standard

variable {α : Type u} [DecidableEq α] [Inhabited α]

open Formula in
class Theory.SubformulaClosed' (T : Theory α) where
  natom_closed : ∀ {a}, natom a ∈ T → atom a ∈ T
  and_closed   : ∀ {p q}, p ⋏ q ∈ T → p ∈ T ∧ q ∈ T
  or_closed    : ∀ {p q}, p ⋎ q ∈ T → p ∈ T ∧ q ∈ T
  box_closed   : ∀ {p}, □p ∈ T → p ∈ T
  dia_closed   : ∀ {p}, ◇p ∈ T → p ∈ T

namespace Theory.SubformulaClosed'

variable [Theory.SubformulaClosed' T]

open Theory.SubformulaClosed'

lemma and_closed₁ (hpq : p ⋏ q ∈ T) : p ∈ T := (and_closed hpq).1
lemma and_closed₂ (hpq : p ⋏ q ∈ T) : q ∈ T := (and_closed hpq).2

lemma or_closed₁ (hpq : p ⋎ q ∈ T) : p ∈ T := (or_closed hpq).1
lemma or_closed₂ (hpq : p ⋎ q ∈ T) : q ∈ T := (or_closed hpq).2

instance {p : Formula α} : Theory.SubformulaClosed' (𝒮 p).toSet where
  natom_closed := by sorry;
  and_closed   := by sorry;
  or_closed    := by sorry;
  box_closed   := by sorry;
  dia_closed   := by sorry;

/-
attribute [aesop safe 5 forward]
  Theory.SubformulaClosed'.natom_closed
  Theory.SubformulaClosed'.and_closed
  Theory.SubformulaClosed'.or_closed
  Theory.SubformulaClosed'.box_closed
  Theory.SubformulaClosed'.dia_closed
-/

end Theory.SubformulaClosed'

namespace Kripke

open Formula (atom natom)
open Formula.Kripke

section

open Theory.SubformulaClosed' in
macro_rules | `(tactic| trivial) => `(tactic|
    first
    | apply natom_closed $ by assumption
    | apply and_closed₁ $ by assumption
    | apply and_closed₂ $ by assumption
    | apply or_closed₁ $ by assumption
    | apply or_closed₂ $ by assumption
    | apply box_closed $ by assumption
    | apply dia_closed $ by assumption
  )

def filterEquiv (M : Kripke.Model α) (T : Theory α) [T.SubformulaClosed'] (x y : M.World) := ∀ p, (_ : p ∈ T := by trivial) → x ⊧ p ↔ y ⊧ p

variable (M : Kripke.Model α) (T : Theory α) [T_closed : T.SubformulaClosed']

lemma filterEquiv.equivalence : Equivalence (filterEquiv M T) where
  refl := by intro x p _; rfl;
  symm := by intro x y h p hp; exact h _ hp |>.symm;
  trans := by
    intro x y z exy eyz;
    intro p hp;
    exact Iff.trans (exy p hp) (eyz p hp)

def FilterEqvSetoid : Setoid (M.World) := ⟨filterEquiv M T, filterEquiv.equivalence M T⟩

abbrev FilterEqvQuotient := Quotient (FilterEqvSetoid M T)

lemma FilterEqvQuotient.finite (T_finite : T.Finite) : Finite (FilterEqvQuotient M T) := by
  have : Finite (𝒫 T) := Set.Finite.powerset T_finite
  let f : FilterEqvQuotient M T → 𝒫 T :=
    λ (Qx : FilterEqvQuotient M T) => Quotient.lift (λ x => ⟨{ p ∈ T | x ⊧ p }, (by simp_all)⟩) (by
      intro x y hxy; simp;
      apply Set.eq_of_subset_of_subset;
      . rintro p ⟨hp, hx⟩; exact ⟨hp, (hxy p hp).mp hx⟩;
      . rintro p ⟨hp, hy⟩; exact ⟨hp, (hxy p hp).mpr hy⟩;
      ) Qx
  have hf : Function.Injective f := by
    intro Qx Qy h;
    obtain ⟨x, rfl⟩ := Quotient.exists_rep Qx;
    obtain ⟨y, rfl⟩ := Quotient.exists_rep Qy;
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
  exact Finite.of_injective f hf

instance : Nonempty (FilterEqvQuotient M T) := ⟨⟦﹫⟧⟩

class Model.FilterOf (FM : Model α) (M : Model α) (T : Theory α) [T.SubformulaClosed'] where
  def_world : FM.World = FilterEqvQuotient M T := by rfl
  def_rel₁ : ∀ {x y : M.Frame}, x ≺ y → Frame.Rel' (cast def_world.symm ⟦x⟧) (cast def_world.symm ⟦y⟧) := by tauto;
  def_box : ∀ {Qx Qy : FM.World}, Qx ≺ Qy → Quotient.lift₂ (λ x y => ∀ p, □p ∈ T → (x ⊧ □p → y ⊧ p)) (by
    intro x₁ y₁ x₂ y₂ hx hy;
    simp;
    constructor;
    . intro h p hp sp₂; exact hy p |>.mp $ h p hp $ hx (□p) hp |>.mpr sp₂;
    . intro h p hp sp₁; exact hy p |>.mpr $ h p hp $ hx (□p) hp |>.mp sp₁;
  ) (cast def_world Qx) (cast def_world Qy) := by tauto;
  def_dia : ∀ {Qx Qy : FM.World}, Qx ≺ Qy → Quotient.lift₂ (λ x y => ∀ p, ◇p ∈ T → (y ⊧ p → x ⊧ ◇p)) (by
    intro x₁ y₁ x₂ y₂ hx hy;
    simp;
    constructor;
    . intro h p hp sp₁; exact hx (◇p) |>.mp $ h p (by trivial) $ hy p |>.mpr sp₁;
    . intro h p hp sp₂; exact hx (◇p) |>.mpr $ h p (by trivial) $ hy p |>.mp sp₂;
  ) (cast def_world Qx) (cast def_world Qy) := by tauto;
  def_valuation Qx a : (ha : (atom a) ∈ T := by trivial) →
    FM.Valuation Qx a ↔ Quotient.lift (λ x => M.Valuation x a) (by
      simp; intro x y h;
      constructor;
      . intro hx; exact h a ha |>.mp hx;
      . intro hy; exact h a ha |>.mpr hy;
    ) (cast def_world Qx) := by tauto;

attribute [simp] Model.FilterOf.def_world

namespace FilterationModel

end FilterationModel

abbrev StandardFilterationValuation (Qx : FilterEqvQuotient M T) (a : α) := (ha : (atom a) ∈ T) → Quotient.lift (λ x => M.Valuation x a) (by
  simp; intro x y h;
  constructor;
  . intro hx; exact h a ha |>.mp hx;
  . intro hy; exact h a ha |>.mpr hy;
) Qx


abbrev FinestFilterationFrame (M : Model α) (T : Theory α) [T.SubformulaClosed'] : Kripke.Frame where
  World := FilterEqvQuotient M T
  Rel Qx Qy := ∃ x y, Qx = ⟦x⟧ ∧ Qy = ⟦y⟧ ∧ x ≺ y

abbrev FinestFilterationModel (M : Model α) (T : Theory α) [T.SubformulaClosed'] : Kripke.Model α where
  Frame := FinestFilterationFrame M T
  Valuation := StandardFilterationValuation M T

@[simp]
instance FinestFilterationModel.filterOf {M} {T : Theory α} [T.SubformulaClosed'] : (FinestFilterationModel M T).FilterOf M T where


abbrev CoarsestFilterationFrame (M : Model α) (T : Theory α) [T.SubformulaClosed'] : Kripke.Frame where
  World := FilterEqvQuotient M T
  Rel Qx Qy := Quotient.lift₂ (λ x y => ∀ p, □p ∈ T → (x ⊧ □p → y ⊧ p)) (by
    intro x₁ y₁ x₂ y₂ hx hy;
    simp;
    constructor;
    . intro h p hp sp₂; exact hy p |>.mp $ h p hp $ hx (□p) hp |>.mpr sp₂;
    . intro h p hp sp₁; exact hy p |>.mpr $ h p hp $ hx (□p) hp |>.mp sp₁;
  ) Qx Qy

noncomputable abbrev CoarsestFilterationModel (M : Model α) (T : Theory α) [T.SubformulaClosed'] : Kripke.Model α where
  Frame := CoarsestFilterationFrame M T
  Valuation := StandardFilterationValuation M T

@[simp]
instance CoarsestFilterationModel.filterOf {M} {T : Theory α} [T.SubformulaClosed'] : (CoarsestFilterationModel M T).FilterOf M T where

section

variable {M} {T : Theory α} [T.SubformulaClosed'] {FM : Kripke.Model α} (h_filter : FM.FilterOf M T)

lemma reflexive_filteration_model (hRefl : Reflexive M.Frame) : Reflexive FM.Frame := by
  intro Qx;
  obtain ⟨x, hx⟩ := Quotient.exists_rep (cast (h_filter.def_world) Qx);
  convert h_filter.def_rel₁ $ hRefl x <;> simp_all;

lemma serial_filteration_model (hSerial : Serial M.Frame) : Serial FM.Frame := by
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

variable {M : Model α} {T : Theory α} [T.SubformulaClosed']
         (FM : Model α) (filterOf : FM.FilterOf M T)

theorem filteration {x : M.World} {p : Formula α} (hs : p ∈ T) : x ⊧ p ↔ (cast (filterOf.def_world.symm) ⟦x⟧) ⊧ p := by
  induction p using Formula.rec' generalizing x with
  | hatom a =>
    have := filterOf.def_valuation (cast filterOf.def_world.symm ⟦x⟧) a;
    simp_all [Satisfies];
  | hnatom a =>
    apply Iff.not;
    have := filterOf.def_valuation (cast filterOf.def_world.symm ⟦x⟧) a;
    simp_all [Satisfies];
  | hbox p ihp =>
    constructor;
    . intro h Qy rQxQy;
      obtain ⟨y, ey⟩ := Quotient.exists_rep (cast (filterOf.def_world) Qy);
      have this := filterOf.def_box rQxQy; simp [←ey] at this;
      simpa [ey] using ihp (by trivial) |>.mp $ @this p hs h;
    . intro h y rxy;
      have rQxQy := filterOf.def_rel₁ rxy;
      exact ihp (by trivial) |>.mpr $ h _ rQxQy;
  | hdia p ihp =>
    constructor;
    . rintro ⟨y, Rxy, h⟩;
      use ?_;
      constructor;
      . exact filterOf.def_rel₁ Rxy
      . exact ihp (by trivial) |>.mp h;
    . intro h;
      obtain ⟨Qy, RQxQy, hy⟩ := h;
      obtain ⟨y, ey⟩ := Quotient.exists_rep (cast (filterOf.def_world) Qy);
      have := filterOf.def_dia (Qy := Qy) RQxQy; simp [←ey] at this;
      exact this p (by trivial) $ @ihp y (by trivial) |>.mpr (by aesop);
  | hand p q ihp ihq =>
    constructor;
    . rintro ⟨hp, hq⟩; exact ⟨ihp (by trivial) |>.mp hp, ihq (by trivial) |>.mp hq⟩;
    . rintro ⟨hp, hq⟩; exact ⟨ihp (by trivial) |>.mpr hp, ihq (by trivial) |>.mpr hq⟩;
  | hor p q ihp ihq =>
    constructor;
    . rintro (hp | hq);
      . left; exact ihp (by trivial) |>.mp hp;
      . right; exact ihq (by trivial) |>.mp hq;
    . rintro (hp | hq);
      . left; exact ihp (by trivial) |>.mpr hp;
      . right; exact ihq (by trivial) |>.mpr hq;
  | _ => trivial

end

instance K_finite_complete : Complete (𝐊 : DeductionParameter α) AllFrameClass.{u}ꟳ# := ⟨by
  intro p hp;
  apply K_complete.complete;
  intro F _ V x;
  let M : Kripke.Model α := ⟨F, V⟩;
  let FM := CoarsestFilterationModel M ↑(𝒮 p);

  apply filteration FM (CoarsestFilterationModel.filterOf) (by aesop) |>.mpr;
  apply hp (by
    suffices Finite (FilterEqvQuotient M p.Subformulas) by
      simp [FrameClass.restrictFinite];
      use ⟨FM.Frame⟩;
    apply FilterEqvQuotient.finite;
    simp;
  ) FM.Valuation
⟩

class FiniteFrameProperty (Λ : DeductionParameter α) (𝔽 : FrameClass.{u}) where
  [complete : Complete Λ 𝔽ꟳ#]
  [sound : Sound Λ 𝔽ꟳ#]

instance : FiniteFrameProperty (α := α) 𝐊 AllFrameClass where


instance KTB_finite_complete : Complete (𝐊𝐓𝐁 : DeductionParameter α) ReflexiveSymmetricFrameClass.{u}ꟳ# := ⟨by
  intro p hp;
  apply KTB_complete.complete;
  intro F ⟨F_refl, F_symm⟩ V x;
  let M : Kripke.Model α := ⟨F, V⟩;
  let FM := FinestFilterationModel M (𝒮 p);
  apply filteration FM (FinestFilterationModel.filterOf) (by aesop) |>.mpr;
  apply hp (by
    suffices Finite (FilterEqvQuotient M (𝒮 p)) by
      simp [FrameClass.restrictFinite];
      use ⟨FM.Frame⟩;
      refine ⟨⟨?refl, ?symm⟩, (by simp)⟩;
      . exact reflexive_filteration_model (FinestFilterationModel.filterOf) F_refl;
      . exact symmetric_finest_filteration_model F_symm;
    apply FilterEqvQuotient.finite;
    simp;
  ) FM.Valuation
⟩

instance : FiniteFrameProperty (α := α) 𝐊𝐓𝐁 ReflexiveSymmetricFrameClass where

section

open Frame (TransitiveClosure)

variable {M : Model α} (M_trans : Transitive M.Frame) {T : Theory α} [T.SubformulaClosed']

noncomputable abbrev FinestFilterationTransitiveClosureModel (M : Model α) (T : Theory α) [T.SubformulaClosed'] : Kripke.Model α where
  Frame := (FinestFilterationFrame M T)^+
  Valuation := StandardFilterationValuation M T

namespace FinestFilterationTransitiveClosureModel

@[instance]
def filterOf : (FinestFilterationTransitiveClosureModel M T).FilterOf M T where
  def_rel₁ := by
    intro x y hxy;
    apply TransitiveClosure.single;
    tauto;
  def_box := by
    intro Qx Qy RQxQy;
    induction RQxQy using Relation.TransGen.head_induction_on with
    | base rxy =>
      obtain ⟨x, y, rfl, rfl, rxy⟩ := rxy;
      intro p _ hpx;
      exact hpx _ rxy;
    | ih ha hxy hyz =>
      obtain ⟨x, y, rfl, rfl, rxy⟩ := ha;
      obtain ⟨w, z, _, rfl, _⟩ := hxy;
      . intro p hp hpx;
        apply hyz p hp;
        intro v ryv;
        exact hpx _ (M_trans rxy ryv);
      . rename_i h;
        obtain ⟨w, z, rfl, rfl, _⟩ := h;
        intro p hp hpx;
        apply hyz p hp;
        intro v ryv;
        exact hpx _ (M_trans rxy ryv);

lemma rel_transitive : Transitive (FinestFilterationTransitiveClosureModel M T).Frame := Frame.TransitiveClosure.rel_transitive

lemma rel_symmetric (M_symm : Symmetric M.Frame) : Symmetric (FinestFilterationTransitiveClosureModel M T).Frame :=
  Frame.TransitiveClosure.rel_symmetric $ symmetric_finest_filteration_model M_symm

lemma rel_reflexive (M_refl : Reflexive M.Frame) : Reflexive (FinestFilterationTransitiveClosureModel M T).Frame := by
  exact reflexive_filteration_model (filterOf M_trans) M_refl;

end FinestFilterationTransitiveClosureModel

end

open FinestFilterationTransitiveClosureModel in
instance S4_finite_complete : Complete (𝐒𝟒 : DeductionParameter α)  PreorderFrameClass.{u}ꟳ# := ⟨by
  intro p hp;
  apply S4_complete.complete;
  intro F ⟨F_refl, F_trans⟩ V x;
  let M : Kripke.Model α := ⟨F, V⟩;
  let FM := FinestFilterationTransitiveClosureModel M (𝒮 p);
  apply @filteration α M (𝒮 p) _ FM ?filterOf x p (by sorry) |>.mpr;
  apply hp (by
    suffices Finite (FilterEqvQuotient M (𝒮 p)) by
      simp [FrameClass.restrictFinite];
      use { toFrame := FM.Frame, World_finite := by aesop };
      refine ⟨⟨?refl, rel_transitive⟩, (by simp)⟩;
      . exact rel_reflexive (by simpa using F_trans) F_refl;
    apply FilterEqvQuotient.finite;
    simp;
  ) FM.Valuation;
  . apply FinestFilterationTransitiveClosureModel.filterOf;
    exact F_trans;
⟩

instance : FiniteFrameProperty (α := α) 𝐒𝟒 PreorderFrameClass where


open FinestFilterationTransitiveClosureModel in
instance KT4B_finite_complete : Complete (𝐊𝐓𝟒𝐁 : DeductionParameter α) EquivalenceFrameClass.{u}ꟳ# := ⟨by
  intro p hp;
  apply KT4B_complete.complete;
  intro F ⟨F_refl, F_trans, F_symm⟩ V x;
  let M : Kripke.Model α := ⟨F, V⟩;
  let FM := FinestFilterationTransitiveClosureModel M (𝒮 p);
  apply @filteration α M (𝒮 p) _ FM ?filterOf x p (by sorry) |>.mpr;
  apply hp (by
    suffices Finite (FilterEqvQuotient M (𝒮 p)) by
      simp [FrameClass.restrictFinite];
      use { toFrame := FM.Frame, World_finite := by aesop };
      refine ⟨⟨?refl, rel_transitive, ?symm⟩, (by simp)⟩;
      . exact rel_reflexive (by simpa using F_trans) F_refl;
      . exact rel_symmetric F_symm;
    apply FilterEqvQuotient.finite;
    simp;
  ) FM.Valuation;
  . apply FinestFilterationTransitiveClosureModel.filterOf
    exact F_trans;
⟩

instance : FiniteFrameProperty (α := α) 𝐊𝐓𝟒𝐁 EquivalenceFrameClass where
-- MEMO: `𝐒𝟓 =ₛ 𝐊𝐓𝟒𝐁`だから決定可能性という面では`𝐒𝟓`も決定可能．

end Kripke

end LO.Modal.Standard
