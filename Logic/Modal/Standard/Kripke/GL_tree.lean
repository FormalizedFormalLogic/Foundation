import Logic.Modal.Standard.Kripke.GL
import Logic.Modal.Standard.Kripke.Preservation

def Assymetric (rel : α → α → Prop) := ∀ ⦃x y⦄, (rel x y) → ¬(rel x y)

lemma irreflexive_of_assymetric (h : Assymetric rel) : Irreflexive rel := by simp_all [Assymetric, Irreflexive];

-- TODO: move
lemma List.last_length_1 {α} {l : List α} (h : l.length = 1) : l = [l.getLast (by aesop)] := by
  match l with
  | [r] => rfl

-- TODO: move
lemma List.interpolant {α} {l₁ l₂ : List α} (h_length : l₁.length + 1 = l₂.length) (h_prefix : l₁ <+: l₂)
  : ∃ z, l₁ ++ [z] = l₂ := by
    obtain ⟨l₃, rfl⟩ := h_prefix;
    use l₃.getLast (by aesop);
    have : l₃ = [l₃.getLast _] := List.last_length_1 (by simp_all);
    rw [←this];

namespace LO.Modal.Standard

namespace Kripke

-- open System
open Kripke
open Formula.Kripke

variable {α} [Inhabited α] [DecidableEq α]


def Frame.isStrictRooted (F : Frame) (r : F.World) : Prop := ∀ w ≠ r, r ≺ w

def Frame.isRooted (F : Frame) (r : F.World) : Prop := ∀ w, r ≺ w

@[simp]
lemma Frame.strictly_rooted_of_rooted {F : Frame} {r : F.World} (h : F.isRooted r) : F.isStrictRooted r := by
  intros w _;
  exact h w;


-- TODO: 証明したがおそらく不要．
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


open Relation (TransGen ReflTransGen)

structure RootedFrame extends Kripke.Frame where
  root : World
  default := root
  def_root : ∀ w ≠ root, root ≺* w


section

def Frame.Cuttage (F : Kripke.Frame) (r : F.World) : Kripke.RootedFrame where
  World := { w | r ≺* w }
  Rel x y := x.1 ≺ y.1
  root := ⟨r, by tauto⟩
  def_root := by
    rintro ⟨w, hw⟩ ne_wr;
    simp at hw;
    sorry
    -- rintro x (rfl | ⟨Rrz, Rzx⟩);
    -- . simp;
    -- . rename_i z;
    --   replace Rzx : Rel ⟨z, Rrz⟩ ⟨x, ReflTransGen.tail Rrz Rzx⟩ := Rzx;
    --   exact ReflTransGen.tail (by sorry) Rzx;
      -- have : self.Rel ⟨z, (by sorry)⟩ ⟨x, (by sorry)⟩ := by sorry;
      -- rename_i z hzx;
infix:100 "↾" => Frame.Cuttage


def Model.Cuttage (M : Kripke.Model α) (r : M.World) : Kripke.Model α where
  Frame := (M.Frame↾r).toFrame
  Valuation w a := M.Valuation w.1 a
infix:100 "↾" => Model.Cuttage

/-
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
-/

def Frame.downward {F : Kripke.Frame} (x : F.World) : Type u := { w // w ≺+ x }
postfix:100 "↓" => Frame.downward

structure Tree extends Kripke.RootedFrame where
  branching : ∀ x : World, ∀ y z : x↓, y ≠ z → (y.1 ≺ z.1 ∨ z.1 ≺ y.1) -- linear order

structure TransitiveTree extends Kripke.Tree where
  rel_irreflexive : Irreflexive Rel
  rel_transitive : Transitive Rel

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
  Rel cx cy := ∃ z, cx.1 ++ [z] = cy.1

namespace Frame.TreeUnravelling

variable {F : Frame} {r : F.World}

@[simp]
lemma not_nil {c : (F.TreeUnravelling r).World} : c.1 ≠ [] := by
  have := c.2.1;
  by_contra;
  simp_all;

@[simp]
lemma irreflexive : Irreflexive (F.TreeUnravelling r).Rel := by
  intro x; simp [TreeUnravelling];

def PMorphism (F : Frame) (r : F) : F.TreeUnravelling r →ₚ F where
  toFun c := c.1.getLast (by simp)
  forth {cx cy} h := by
    obtain ⟨z, hz⟩ := h;
    have ⟨_, _, h⟩ := @List.chain'_append _ F.Rel cx.1 [z] |>.mp (by rw [hz]; exact cy.2.2);
    refine h (cx.1.getLast (by aesop)) ?hx (cy.1.getLast (by aesop)) ?hy;
    . exact List.getLast?_eq_getLast_of_ne_nil (by simp);
    . rw [←@List.getLast_append_singleton _ z cx.1]; simp_all;
  back {cx y} h := by
    simp_all;
    use ⟨cx.1 ++ [y], ?_⟩;
    . constructor;
      . simp;
      . use y;
    . constructor;
      . obtain ⟨i, hi⟩ := cx.2.1;
        use (i ++ [y]);
        simp_rw [←List.append_assoc, hi];
      . apply List.Chain'.append;
        . exact cx.2.2;
        . simp;
        . intro z hz; simp;
          convert h;
          exact List.mem_getLast?_eq_getLast hz |>.2;

variable (hr : F.isRooted r)

@[simp]
lemma PMorphism.surjective_of_rooted : Function.Surjective (PMorphism F r) := by
  intro x;
  use ⟨[r, x], ?_⟩
  simp [PMorphism];
  constructor;
  . use [x]; simp;
  . simp; exact hr x;

lemma validOnBaseFrame : (F.TreeUnravelling r)# ⊧ p → F# ⊧ p
  := iff_formula_valid_on_frame_surjective_morphism (PMorphism F r) (by simp_all)

end Frame.TreeUnravelling


def Model.TreeUnravelling (M : Kripke.Model α) (r : M.World) : Kripke.Model α where
  Frame := M.Frame.TreeUnravelling r
  Valuation c a := M.Valuation (c.1.getLast (by simp)) a

namespace Model.TreeUnravelling

variable {M : Kripke.Model α} {r : M.World} {p : Formula α}

def PMorphism (M : Kripke.Model α) (r : M.World) : M.TreeUnravelling r →ₚ M :=
  Model.PseudoEpimorphism.mkAtomic (Frame.TreeUnravelling.PMorphism M.Frame r) $ by aesop;

end Model.TreeUnravelling

end TreeUnravelling


/-
section TransitiveTreeUnravelling

abbrev Frame.TransitiveTreeUnravelling (F : Frame) (r : F.World) :=
  letI FX := (F↾r).TreeUnravelling (⟨r, by simp⟩) |>.TransitiveClosure
  FX

namespace Frame.TransitiveTreeUnravelling

variable {F : Frame} {r : F.World} {p : Formula α}

@[simp]
lemma not_nil {c : (F.TransitiveTreeUnravelling r).World} : c.1 ≠ [] := by
  by_contra;
  have := c.2.1;
  simp_all;

@[simp]
lemma transitive : Transitive (F.TransitiveTreeUnravelling r).Rel := by simp

def PMorphism (F : Frame) (r : F) (F_trans : Transitive F): F.TransitiveTreeUnravelling r →ₚ F where
  toFun c := c.1.getLast (by simp)
  forth {cx cy} h := by
    obtain ⟨h₁, h₂⟩ := h;
    sorry;
    sorry;
  back {cx y} h := by
    simp_all;
    use ⟨(cx.1 ++ [y]), ?_⟩;
    . constructor;
      . simp;
      . sorry;
    . simp;
      constructor;
      . obtain ⟨i, hi⟩ := cx.2.1;
        use (i ++ [y]);
        simp_rw [←List.append_assoc, hi];;
      . apply List.Chain'.append;
        . exact cx.2.2;
        . simp;
        . intro z hz; simp;
          convert h;
          exact List.mem_getLast?_eq_getLast hz |>.2;

variable (F_trans : Transitive F)

@[simp]
lemma PMorphism.surjective_of_weak_rooted (hr : F.isRooted r) : Function.Surjective (PMorphism F r F_trans) := by
  intro x;
  use ⟨[r, x], ?_⟩
  simp [PMorphism];
  constructor;
  . use [x]; simp;
  . simpa using @hr x;

lemma validOnBaseFrame_of_weak_rooted (hr : F.isRooted r) : (F.TransitiveTreeUnravelling r)# ⊧ p → F# ⊧ p
  := iff_formula_valid_on_frame_surjective_morphism (TransitiveTreeUnravelling.PMorphism F r F_trans) (by simp_all)


@[simp]
lemma PMorphism.surjective_of_reflexive_rooted (hRefl : Reflexive F.Rel) (hr : F.isStrictRooted r) : Function.Surjective (TransitiveTreeUnravelling.PMorphism F r F_trans) := by
  intro x;
  use ⟨[r, x], ?_⟩;
  simp [PMorphism];
  constructor;
  . use [x]; simp;
  . simp;
    by_cases hx : x = r;
    . subst hx; exact hRefl x;
    . exact hr x hx;

lemma validOnBaseFrame_of_reflexive_rooted (hRefl : Reflexive F.Rel) (hr : F.isStrictRooted r) : (F.TransitiveTreeUnravelling r)# ⊧ p → F# ⊧ p
  := iff_formula_valid_on_frame_surjective_morphism (TransitiveTreeUnravelling.PMorphism F r F_trans) (by simp_all)

end Frame.TransitiveTreeUnravelling


def Model.TransitiveTreeUnravelling (M : Kripke.Model α) (r : M.World) : Kripke.Model α where
  Frame := M.Frame.TransitiveTreeUnravelling r
  Valuation c a := M.Valuation (c.1.getLast (by simp)) a

namespace Model.TransitiveTreeUnravelling

def PMorphism (M : Kripke.Model α) (r : M.World) (M_trans : Transitive M.Frame) : (M.TransitiveTreeUnravelling r) →ₚ M :=
  Model.PseudoEpimorphism.mkAtomic (Frame.TransitiveTreeUnravelling.PMorphism M.Frame r M_trans) $ by aesop;

variable {M : Kripke.Model α} {r : M.World} (M_trans : Transitive M.Frame)

lemma modal_equivalence : ((M.TransitiveTreeUnravelling r), w) ↭ (M, w.1.getLast (by simp)) := by
    have H := @modal_equivalence_of_modal_morphism _ (M.TransitiveTreeUnravelling r) M (PMorphism M r M_trans) w;
    intro p;
    have Hp := @H p;
    constructor;
    . intro hp;
      exact Hp.mp hp;
    . intro hp;
      exact Hp.mpr hp;

end Model.TransitiveTreeUnravelling

end TransitiveTreeUnravelling
-/


section TreeUnravelling

abbrev Frame.TreeUnravelling₂ (F : Frame) (r : F.World) : TransitiveTree :=
  letI Fx := ((F↾r).TreeUnravelling (F↾r).root).TransitiveClosure;
  {
    World := Fx.World
    Rel := Fx.Rel
    root := Fx.default
    def_root := by
      rintro ⟨w, ⟨z, rfl⟩, hw₂⟩ enr;
      sorry;
    branching := by
      rintro x y z hne;
      sorry;
    rel_transitive := by simp [Fx];
    rel_irreflexive := by
      simp [Irreflexive];
      intro x Rxx;
      simp [Fx] at Rxx;
      sorry;
  }

abbrev Frame.mkFiniteTransitiveTree (F : TransitiveTree) (_ : Finite F.World) : FiniteTransitiveTree where
  World := F.World
  default := F.default
  def_root := F.def_root
  rel_irreflexive := F.rel_irreflexive
  rel_transitive := F.rel_transitive
  branching := F.branching

abbrev FiniteFrame.TreeUnravelling (F : FiniteFrame) (r : F.World) : FiniteTransitiveTree :=
  Frame.mkFiniteTransitiveTree (F.TreeUnravelling₂ r) $ by
    simp [Frame.TreeUnravelling₂];
    sorry;

end TreeUnravelling


variable {p : Formula α}

lemma validOnFTT_Aux (h : TransitiveIrreflexiveFrameClass.{u}ꟳ# ⊧ p) : ∀ T : FiniteTransitiveTree.{u}, T# ⊧ p := by
  simp at h;
  intro T;
  apply @h T.toFrame T.toFiniteFrame;
  . exact T.rel_transitive;
  . exact T.rel_irreflexive;
  . tauto;

lemma validOnFTT_root (h : ∀ F : FiniteTransitiveTree.{u}, F# ⊧ p) : ∀ T : FiniteTransitiveTree.{u}, ∀ V, Satisfies ⟨T.toFrame, V⟩ T.root p := by
  intro T V; exact h T V _;

-- set_option pp.proofs true in
lemma validOnFTT_root' : (∀ T : FiniteTransitiveTree.{u}, ∀ V, Satisfies ⟨T.toFrame, V⟩ T.root p) → TransitiveIrreflexiveFrameClass.{u}ꟳ# ⊧ p := by
  contrapose; push_neg;
  intro h; simp [ValidOnFrame, ValidOnModel] at h;
  obtain ⟨_, F, F_trans, F_irrefl, rfl, V, x, hx⟩ := h;
  let T := F.TreeUnravelling x;
  let TV : Valuation T.toFrame α := λ x a => V (x.1.getLast (by simp)).1 a
  use T, TV;
  apply @modal_equivalence_of_modal_morphism α ⟨T.toFrame, TV⟩ ⟨F, V⟩ ?m T.root p |>.not.mpr ?s;
  . exact {
      toFun := λ c => c.1.getLast (by simp) |>.1
      atomic := by simp;
      back := by
        simp;
        rintro ⟨ws, hw₁, hw₂⟩ v hwv;
        let v' : (F.toFrame↾x).World := ⟨v, ?hv⟩;
        use ⟨ws ++ [v'], ?hwv⟩;
        . constructor;
          . simp;
          . apply Frame.TransitiveClosure.single;
            use v';
        . constructor;
          . obtain ⟨i, hi⟩ := hw₁;
            use (i ++ [v']);
            simp_rw [←List.append_assoc, hi];
          . apply List.Chain'.append;
            . exact hw₂;
            . simp;
            . sorry;
        . simp_all;
          sorry;
      forth := by
        -- rintro cx cy ⟨z, hz⟩;
        -- have := @List.chain'_append _ T.Rel;
        sorry;
        -- obtain ⟨z, hz⟩ := h;
        -- have ⟨_, _, h⟩ := @List.chain'_append _ F.Rel cx [z] |>.mp (by rw [hz]; exact cy.2.2);
        -- refine h (cx.1.getLast (by aesop)) ?hx (cy.1.getLast (by aesop)) ?hy;
        -- . exact List.getLast?_eq_getLast_of_ne_nil (by simp);
        -- . rw [←@List.getLast_append_singleton _ z cx.1]; simp_all;
    }
  . exact hx;

end

end Kripke

end LO.Modal.Standard
