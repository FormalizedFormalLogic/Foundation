import Logic.Modal.Standard.Kripke.GL
import Logic.Modal.Standard.Kripke.Preservation

def Assymetric (rel : α → α → Prop) := ∀ ⦃x y⦄, (rel x y) → ¬(rel x y)

lemma irreflexive_of_assymetric (h : Assymetric rel) : Irreflexive rel := by simp_all [Assymetric, Irreflexive];


namespace LO.Modal.Standard

namespace Kripke

-- open System
open Kripke
open Formula.Kripke

variable {α} [Inhabited α] [DecidableEq α]


def Frame.isRooted (F : Frame) (r : F.World) : Prop := ∀ w ≠ r, r ≺ w

def Frame.isWeakRooted (F : Frame) (r : F.World) : Prop := ∀ w, r ≺ w

@[simp]
lemma Frame.rooted_of_weak_rooted {F : Frame} {r : F.World} (h : F.isWeakRooted r) : F.isRooted r := by
  intros w _;
  exact h w;

section ComplexityLimit

def Frame.ComplexityLimit {F : Kripke.Frame} (w : F.World) (p : Formula α) : Kripke.Frame where
  World := { x | ∃ n ≤ p.complexity, w ≺^[n] x }
  default := ⟨w, by use 0; simp⟩
  Rel x y := x.1 ≺ y.1

def Model.ComplexityLimit {M : Kripke.Model α} (w : M.World) (p : Formula α) : Kripke.Model α where
  Frame := M.Frame.ComplexityLimit w p
  Valuation x a := M.Valuation x.1 a

open Formula.Subformulas

variable {M : Kripke.Model α} {w : M.World} {p q : Formula α} (hq : q ∈ 𝒮 p) {x : M.World}

lemma iff_satisfy_complexity_limit_modelAux
  (hx : ∃ n ≤ p.complexity - q.complexity, w ≺^[n] x)
  : x ⊧ q ↔ Satisfies (M.ComplexityLimit w p) ⟨x, (by obtain ⟨n, _, _⟩ := hx; use n; exact ⟨by omega, by assumption⟩)⟩ q := by
  induction q using Formula.rec' generalizing x p with
  | hbox q ihq =>
    obtain ⟨n, hn, hx⟩ := hx;
    simp [Formula.complexity] at hn;
    have : n + 1 ≤ p.complexity - q.complexity := by sorry; -- TODO 正しいはずなのだが`omega`ではなぜか通らない
    constructor;
    . rintro h ⟨y, hy⟩ Rxy;
      apply ihq (mem_box (by assumption)) ?_ |>.mp;
      . exact h Rxy;
      . use (n + 1);
        constructor;
        . assumption;
        . apply Frame.RelItr'.forward.mpr;
          use x; constructor; assumption; exact Rxy;
    . rintro h y Rxy;
      apply ihq (mem_box (by assumption)) ?_ |>.mpr;
      . exact h Rxy;
      . use (n + 1);
        constructor;
        . assumption;
        . apply Frame.RelItr'.forward.mpr;
          use x;
  | hneg q ih =>
    obtain ⟨n, hn, hx⟩ := hx;
    simp [Formula.complexity] at hn;
    apply Iff.not;
    apply ih (mem_neg (by assumption));
    use n; constructor; omega; assumption;
  | hand q₁ q₂ ihq₁ ihq₂ =>
    obtain ⟨n, hn, hx⟩ := hx;
    simp [Formula.complexity] at hn;
    constructor;
    . rintro ⟨hq₁, hq₂⟩;
      constructor;
      . apply ihq₁ (mem_and (by assumption) |>.1) ?_ |>.mp hq₁;
        use n; constructor; omega; assumption;
      . apply ihq₂ (mem_and (by assumption) |>.2) ?_ |>.mp hq₂;
        use n; constructor; omega; assumption;
    . rintro ⟨hq₁, hq₂⟩;
      constructor;
      . apply ihq₁ (mem_and (by assumption) |>.1) ?_ |>.mpr hq₁;
        use n; constructor; omega; assumption;
      . apply ihq₂ (mem_and (by assumption) |>.2) ?_ |>.mpr hq₂;
        use n; constructor; omega; assumption;
  | himp q₁ q₂ ihq₁ ihq₂ =>
    obtain ⟨n, hn, hx⟩ := hx;
    simp [Formula.complexity] at hn;
    constructor;
    . rintro hq₁ hq₂;
      apply ihq₂ (mem_imp (by assumption) |>.2) ?_ |>.mp;
      apply hq₁;
      apply ihq₁ (mem_imp (by assumption) |>.1) ?_ |>.mpr hq₂;
      use n; constructor; omega; assumption;
      use n; constructor; omega; assumption;
    . rintro hq₁ hq₂;
      apply ihq₂ (mem_imp (by assumption) |>.2) ?_ |>.mpr;
      apply hq₁;
      apply ihq₁ (mem_imp (by assumption) |>.1) ?_ |>.mp hq₂;
      use n; constructor; omega; assumption;
      use n; constructor; omega; assumption;
  | hor q₁ q₂ ihq₁ ihq₂ =>
    obtain ⟨n, hn, hx⟩ := hx;
    simp [Formula.complexity] at hn;
    constructor;
    . rintro (hq₁ | hq₂);
      . left;  apply ihq₁ (mem_or (by assumption) |>.1) ?_ |>.mp hq₁;
        use n; constructor; omega; assumption;
      . right; apply ihq₂ (mem_or (by assumption) |>.2) ?_ |>.mp hq₂;
        use n; constructor; omega; assumption;
    . rintro (hq₁ | hq₂);
      . left;  apply ihq₁ (mem_or (by assumption) |>.1) ?_ |>.mpr hq₁;
        use n; constructor; omega; assumption;
      . right; apply ihq₂ (mem_or (by assumption) |>.2) ?_ |>.mpr hq₂;
        use n; constructor; omega; assumption;
  | _ => simp [Satisfies, Model.ComplexityLimit];

abbrev zero (w : M.World) : (M.ComplexityLimit w p).World := ⟨w, (by use 0; simp)⟩
scoped postfix:max "⁰" => zero

lemma iff_satisfy_complexity_limit_model : w ⊧ p ↔ Satisfies (M.ComplexityLimit w p) w⁰ p := by
  apply iff_satisfy_complexity_limit_modelAux (show p ∈ 𝒮 p by simp);
  use 0; simp;

lemma zero_complexity_limit_model_zero {q₁ q₂} (hq₁ : p ∈ 𝒮 q₁) (hq₂ : p ∈ 𝒮 q₂)
  : Satisfies (M.ComplexityLimit w q₁) w⁰ p → Satisfies (M.ComplexityLimit w q₂) w⁰ p := by
  intro h;
  apply @iff_satisfy_complexity_limit_modelAux α _ M w q₂ p (by assumption) w ?_ |>.mp;
  apply @iff_satisfy_complexity_limit_modelAux α _ M w q₁ p (by assumption) w ?_ |>.mpr h;
  use 0; simp;
  use 0; simp;

lemma zero_complexity_limit_model (hq : p ∈ 𝒮 q) : Satisfies (M.ComplexityLimit w p) w⁰ p ↔ Satisfies (M.ComplexityLimit w q) w⁰ p := by
  constructor;
  . apply zero_complexity_limit_model_zero <;> simp_all;
  . apply zero_complexity_limit_model_zero <;> simp_all;

end ComplexityLimit


section

/-
def Frame.Cuttage (F : Kripke.Frame) (S : Set F.World) [S_inhabited : Inhabited S] : Kripke.Frame where
  World := { w | (∃ s ∈ S, s ≺ w) ∨ w ∈ S }
  default := ⟨S_inhabited.default, by simp⟩
  Rel x y := x.1 ≺ y.1
infix:100 "↾" => Frame.Cuttage

lemma Frame.Cuttage.root_seeds (h : s ∈ S) : (F↾S).isRoot ⟨s, (by simp_all)⟩ := by
  rintro ⟨x, (⟨y, hy₁, hy₂⟩ | hx)⟩;
  . sorry;
  . sorry;
-/

-- lemma Frame.SubframeGeneration.eq_world {F : Kripke.Frame} {X : Set F.World} [Inhabited X] {w : F.World} : w ∈ (F↾X).World ↔ (∃ x ∈ X, x ≺ w) ∨ w ∈ X := by

abbrev Frame.Cuttage (F : Kripke.Frame) (r : F.World) : Kripke.Frame where
  World := { w | w = r ∨ r ≺ w }
  default := ⟨r, by simp⟩
  Rel x y := x.1 ≺ y.1
infix:100 "↾" => Frame.Cuttage

@[simp]
lemma Frame.Cuttage.default_root {F : Kripke.Frame} {r : F.World} : (F↾r).isRooted (F↾r).default := by
  rintro ⟨x, (rfl | hr)⟩;
  . intros; simp_all;
  . intros; exact hr;


def Model.Cuttage (M : Kripke.Model α) (r : M.World) : Kripke.Model α where
  Frame := M.Frame↾r
  Valuation w a := M.Valuation w.1 a
infix:100 "↾" => Model.Cuttage

section

variable {M : Kripke.Model α} {r y : M.World} {p : Formula α}

/-
lemma cuttage_back (Rrx : r ≺ y) : Satisfies (M↾y) ⟨y, (by simp)⟩ p → Satisfies (M↾r) ⟨y, (by aesop)⟩ p := by
  induction p using Formula.rec' with
  | hbox p ih => sorry;
  | hor p q ihp ihq =>
    rintro (hp | hq);
    . left; exact ihp hp;
    . right; exact ihq hq;
  | himp p q ihp ihq =>
    rintro hpq hp;
    sorry;;
    exact ihq (hp $ ihp hq);
  | hneg p ih =>
    simp_all [Model.Cuttage, Satisfies];
  | _ => simp_all [Model.Cuttage, Satisfies];

lemma cuttage_on_root {M : Kripke.Model α} {r : M.World} {p : Formula α} : r ⊧ p ↔ Satisfies (M↾r) ⟨r, (by simp)⟩ p := by
  -- simp [Model.PointSubframeGeneration, Model.SubframeGeneration];
  induction p using Formula.rec' generalizing r with
  | hbox p ih =>
    constructor;
    . rintro hr ⟨y, (rfl | Rry)⟩ h;
      . exact ih.mp $ hr h;
      . have : y ⊧ p := hr Rry;
        exact cuttage_back Rry $ ih.mp this;
    . intro h y Rry;
      have := @h ⟨y, (by aesop)⟩ Rry;
      have := cuttage_back Rry this;
  | _ => simp_all [Model.Cuttage, Satisfies];
    -- simp_all [Satisfies];
-/

open Formula.Subformulas

/--
  r : M.World
  h : Satisfies (Model.ComplexityLimit r (□p)) r⁰ (□p)
  x : (M↾r).Frame.World
  Rrx : ⟨r, ⋯⟩ ≺ x
  this✝² : r ⊧ □p
  this✝¹ : Satisfies M (↑x) p
  this✝ : Satisfies (Model.ComplexityLimit (↑x) p) (↑x)⁰ p
  this : Satisfies (M↾↑x) ⟨↑x, ⋯⟩ p
  ⊢ Satisfies (M↾r) x p
-/

lemma forward {r : M.World} {x : (M↾r).World} (Rrx : (M↾r).Frame.Rel' ⟨r, (by simp)⟩ x) : Satisfies (M↾x.1) ⟨x.1, (by simp)⟩ p ↔ Satisfies (M↾r) x p := by
  induction p using Formula.rec' generalizing r with
  | hbox p ihp =>
    constructor;
    . rintro h y Rxy;
      sorry;
      -- apply @ihp r |>.mp;
      -- apply @ihp y.1|>.mp;
      -- . sorry;
      -- . have := @h ⟨y.1, (by aesop)⟩ Rxy;
      --   exact @ihp x.1 _ _ this;
    . sorry;
  | _ => sorry;

lemma limit_cuttage : Satisfies (M.ComplexityLimit r p) r⁰ p ↔ Satisfies (M↾r) ⟨r, (by simp)⟩ p := by
  induction p using Formula.rec' generalizing r with
  | hatom => simp [Model.ComplexityLimit, Model.Cuttage, Satisfies];
  | hverum => simp [Model.ComplexityLimit, Model.Cuttage, Satisfies];
  | hfalsum => simp [Model.ComplexityLimit, Model.Cuttage, Satisfies];
  | hneg p ihp =>
    apply Iff.not;
    constructor;
    . rintro hp; apply ihp.mp; exact zero_complexity_limit_model (mem_neg (by simp)) |>.mpr hp;
    . rintro hp; apply zero_complexity_limit_model (mem_neg (by simp)) |>.mp $ ihp.mpr hp;
  | hand p q ihp ihq =>
    constructor;
    . rintro ⟨hp, hq⟩;
      constructor;
      . apply ihp.mp; exact zero_complexity_limit_model (mem_and (r := q) (by simp) |>.1) |>.mpr hp;
      . apply ihq.mp; exact zero_complexity_limit_model (mem_and (q := p) (by simp) |>.2) |>.mpr hq;
    . rintro ⟨hp, hq⟩;
      apply iff_satisfy_complexity_limit_model.mp;
      constructor;
      . exact iff_satisfy_complexity_limit_model.mpr $ ihp.mpr hp;
      . exact iff_satisfy_complexity_limit_model.mpr $ ihq.mpr hq;
  | hor p q ihp ihq =>
    constructor;
    . rintro (hp | hq);
      . left; apply ihp.mp; exact zero_complexity_limit_model (mem_or (r := q) (by simp) |>.1) |>.mpr hp;
      . right; apply ihq.mp; exact zero_complexity_limit_model (mem_or (q := p) (by simp) |>.2) |>.mpr hq;
    . rintro (hp | hq);
      . apply iff_satisfy_complexity_limit_model.mp; left;
        exact iff_satisfy_complexity_limit_model.mpr $ ihp.mpr hp;
      . apply iff_satisfy_complexity_limit_model.mp; right;
        exact iff_satisfy_complexity_limit_model.mpr $ ihq.mpr hq;
  | himp p q ihp ihq =>
    constructor;
    . rintro hpq hp;
      apply ihq.mp;
      apply zero_complexity_limit_model (q := p ⟶ q) (mem_imp (q := p) (by simp) |>.2) |>.mpr;
      apply hpq;
      exact zero_complexity_limit_model (mem_imp (r := q) (by simp) |>.1) |>.mp $ ihp.mpr hp;
    . rintro hpq;
      apply iff_satisfy_complexity_limit_model.mp;
      intro hp;
      apply iff_satisfy_complexity_limit_model.mpr;
      apply ihq.mpr;
      apply hpq;
      apply ihp.mp;
      exact iff_satisfy_complexity_limit_model.mp hp;
  | hbox p ihp =>
    constructor;
    . rintro h x Rrx;
      have : r ⊧ □p := @iff_satisfy_complexity_limit_model α _ M r (□p) |>.mpr h;
      have := iff_satisfy_complexity_limit_model.mp $ this Rrx;
      sorry;
      -- exact forward Rrx $ ihp.mp this
    . sorry;
      /-
      rintro h;
      apply iff_satisfy_complexity_limit_model.mp;
      rintro x Rrx;
      apply iff_satisfy_complexity_limit_model.mpr;
      apply ihp.mpr;
      apply forward ;
      have := @h ⟨x, (by sorry)⟩ Rrx;
      have := @ihp r;
      sorry;
      -/


lemma cuttage_on_root₂ : r ⊧ p ↔ Satisfies (M↾r) ⟨r, (by simp)⟩ p := Iff.trans iff_satisfy_complexity_limit_model limit_cuttage

end

end


section PointGenerated

/-
class Frame.PointSubframeGenerated (F₁ : Kripke.Frame) (F₂ : Kripke.Frame) (w : F₁.World) where
  toFun : F₁.World → F₂.World
  rel₁ : w ≺ x → toFun w ≺ toFun x
  r : F₁.World → F₁.World → Prop := λ x y => x ≺ y ∨ x = w ∧ y = w
-/

infix:100 "↾" => Frame.SubframeGeneration

end PointGenerated

structure TransitiveTree extends Kripke.Frame where
  root : World
  def_root : Frame.isRooted _ root
  rel_assymetric : Assymetric Rel
  rel_transitive : Transitive Rel
  rel_comparable : ∀ x y z : World, (y ≺ x ∧ z ≺ x) → (y ≺ z ∨ z ≺ y ∨ y = z)

structure FiniteTransitiveTree extends TransitiveTree, FiniteFrame where

set_option linter.unusedVariables false in
protected abbrev FiniteTransitiveTree.Dep (α : Type u) := FiniteTransitiveTree
protected abbrev FiniteTransitiveTree.alt (T : FiniteTransitiveTree) {α} : FiniteTransitiveTree.Dep α := T
postfix:max "#" => FiniteTransitiveTree.alt

namespace FiniteTransitiveTree

instance : Semantics (Formula α) (FiniteTransitiveTree.Dep α) := ⟨fun T ↦ Formula.Kripke.ValidOnFrame T.toFrame⟩

end FiniteTransitiveTree


section TreeUnravelling

def Frame.TreeUnravelling (F : Frame) (r : F.World) : Kripke.Frame where
  World := { c : List F.World | [r] <+: c ∧ c.Chain' F.Rel }
  default := ⟨[r], (by simp)⟩
  Rel cx cy := (cx.1.length + 1 = cy.1.length) ∧ cx.1 <+: cy.1

abbrev Frame.TransitiveTreeUnravelling (F : Frame) (r : F.World) := F.TreeUnravelling r |>.TransitiveClosure


namespace Frame.TreeUnravelling

variable {F : Frame} {r : F.World}

@[simp]
lemma not_nil {c : (F.TreeUnravelling r).World} : c.1 ≠ [] := by
  by_contra;
  have := c.2.1;
  simp_all;

lemma _root_.List.last_length_1 {α} {l : List α} (h : l.length = 1) : l = [l.getLast (by aesop)] := by
  match l with
  | [r] => rfl

def p_morphism (F : Frame) (r : F) : F.TreeUnravelling r →ₚ F where
  toFun c := c.1.getLast (by simp)
  forth {cx cy} h := by
    have ⟨h₁, ⟨cz, hxzy⟩⟩ := h;
    have hz := List.last_length_1 (l := cz) (by simp [←hxzy] at h₁; tauto);
    simp;
    generalize ex : cx.1.getLast (by simp) = x;
    generalize ey : cy.1.getLast (by simp) = y;
    generalize ez : cz.getLast (by rw [hz]; tauto) = z;
    have eyz : y = z := by
      rw [hz] at hxzy;
      sorry;
    sorry;
  back {cx y} h := by
    simp_all;
    use ⟨cx.1 ++ [y], ?_⟩;
    simp_all; constructor <;> simp;
    constructor;
    . obtain ⟨i, hi⟩ := cx.2.1;
      use (i ++ [y]);
      simp_rw [←List.append_assoc, hi];
    . apply List.Chain'.append;
      . exact cx.2.2;
      . simp;
      . intro z hz; simp;
        convert h;
        exact List.mem_getLast?_eq_getLast hz |>.2;

variable (hr : F.isWeakRooted r)

@[simp]
lemma p_morphism.surjective_of_root : Function.Surjective (p_morphism F r) := by
  intro x;
  use ⟨[r, x], ?_⟩
  simp [p_morphism];
  constructor;
  . use [x]; simp;
  . simp; exact hr x;

lemma validOnBaseFrame : (F.TreeUnravelling r)# ⊧ p → F# ⊧ p
  := iff_formula_valid_on_frame_surjective_morphism (p_morphism F r) (by simp_all)

end Frame.TreeUnravelling


namespace Frame.TransitiveTreeUnravelling

variable {F : Frame} {r : F.World} {p : Formula α}

@[simp]
lemma not_nil {c : (F.TransitiveTreeUnravelling r).World} : c.1 ≠ [] := by
  by_contra;
  have := c.2.1;
  simp_all;

def p_morphism (F : Frame) (F_trans : Transitive F) (r : F) : F.TransitiveTreeUnravelling r →ₚ F where
  toFun c := c.1.getLast (by simp)
  forth {cx cy} h := by
    simp;
    sorry;
  back {cx y} h := by
    simp_all;
    use ⟨(cx.1 ++ [y]), ?_⟩;
    sorry;
    sorry;

variable (F_trans : Transitive F) (hr : F.isWeakRooted r)

@[simp]
lemma p_morphism.surjective_of_root : Function.Surjective (p_morphism F F_trans r) := by
  intro x;
  use ⟨[r, x], ?_⟩
  simp [p_morphism];
  constructor;
  . use [x]; simp;
  . simpa using @hr x;

lemma validOnBaseFrame : (F.TransitiveTreeUnravelling r)# ⊧ p → F# ⊧ p
  := iff_formula_valid_on_frame_surjective_morphism (p_morphism F F_trans r) (by simp_all)

end Frame.TransitiveTreeUnravelling


def Model.TreeUnravelling (M : Kripke.Model α) (r : M.World) : Kripke.Model α where
  Frame := M.Frame.TreeUnravelling r
  Valuation c a := M.Valuation (c.1.getLast (by simp)) a

def Model.TransitiveTreeUnravelling (M : Kripke.Model α) (r : M.World) : Kripke.Model α where
  Frame := M.Frame.TransitiveTreeUnravelling r
  Valuation c a := M.Valuation (c.1.getLast (by simp)) a

end TreeUnravelling



variable {p : Formula α}

lemma validOnFTT_Aux (h : TransitiveIrreflexiveFrameClass.{u}ꟳ# ⊧ p) : ∀ F : FiniteTransitiveTree.{u}, F# ⊧ p := by
  simp at h;
  intro T;
  apply @h T.toFrame T.toFiniteFrame;
  . exact T.rel_transitive;
  . exact irreflexive_of_assymetric T.rel_assymetric;
  . tauto;

lemma validOnFTT_root (h : ∀ F : FiniteTransitiveTree.{u}, F# ⊧ p) : ∀ T : FiniteTransitiveTree.{u}, ∀ V, ∀ x, Satisfies ⟨T.toFrame, V⟩ x p := by
  intro T V x;
  exact h T V x;

lemma validOnFTT_root' : (∀ F : FiniteTransitiveTree.{u}, ∀ V, ∀ x, Satisfies ⟨F.toFrame, V⟩ x p) → TransitiveIrreflexiveFrameClass.{u}ꟳ# ⊧ p := by
  contrapose; push_neg;
  intro h; simp [ValidOnFrame, ValidOnModel] at h;
  obtain ⟨_, F, F_trans, F_irrefl, rfl, h⟩ := h;
  have a := @Frame.TransitiveTreeUnravelling.validOnBaseFrame α F -- F_trans (by sorry);
  /-

  let M : Model α := { Frame := F, Valuation := V };

  let CF : Kripke.FiniteFrame := {
    World := { c | [w] <+: c ∧ List.Chain' F.Rel c },
    World_inhabited := ⟨[w], (by simp)⟩,
    World_finite := by sorry,
    Rel := λ X Y => (X.1.length < Y.1.length) ∧ (X.1 <+: Y.1),
  };
  let CM : Model α := {
    Frame := CF,
    Valuation := λ X a => V (X.1.getLast (by aesop)) a
  };

  have H : ∀ q, ∀ X : CM.World, Satisfies CM X q ↔ Satisfies M (X.1.getLast (by aesop)) q := by
    intro q X;
    induction q using Formula.rec' generalizing X with
    | hbox q ih =>
      constructor;
      . intro h y Rxy;
        have := @h ⟨(X.1).concat y, (by simp; sorry)⟩ (by aesop);
        simpa using @ih _ |>.mp this;
      . intro h Y RXY;
        simp [Satisfies] at h;
        obtain ⟨lXY, ⟨Z, RZY⟩⟩ := RXY;
        sorry;
    | _ => sorry; -- simp_all [Satisfies]; try aesop;

  let W : CF.World := ⟨[w], (by simp)⟩;
  let GM : Kripke.Model α := (CM↾W);
  have h₁ : ¬Satisfies CM W p := H p W |>.not.mpr h;
  have h₂ : ¬Satisfies GM ⟨W, _⟩ p := @satisfies_on_root α CM W p |>.not.mp h₁;
  use {
    World := GM.World,
    World_inhabited := ⟨W, (by aesop)⟩,
    World_finite := by sorry,
    Rel := GM.Frame.Rel,
    root := ⟨W, (by aesop)⟩,
    def_root := by sorry,
    rel_assymetric := by sorry,
    rel_transitive := by sorry,
    rel_comparable := by sorry,
  }, GM.Valuation, ⟨W, (by aesop)⟩;
  exact h₂;
  -/

end Kripke

end LO.Modal.Standard
