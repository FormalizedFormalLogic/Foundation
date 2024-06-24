import Logic.Logic.System
import Logic.Modal.Standard.Formula
import Logic.Modal.Standard.Deduction

universe u v

namespace LO.Modal.Standard

def RelItr (R : α → α → Prop) : ℕ → α → α → Prop
  | 0 => (· = ·)
  | n + 1 => fun x y ↦ ∃ z, R x z ∧ RelItr R n z y

namespace RelItr

@[simp]
lemma iff_zero {R : α → α → Prop} {x y : α} : RelItr R 0 x y ↔ x = y := iff_of_eq rfl

@[simp]
lemma iff_succ {R : α → α → Prop} {x y : α} : RelItr R (n + 1) x y ↔ ∃ z, R x z ∧ RelItr R n z y := iff_of_eq rfl

@[simp]
lemma eq : RelItr (α := α) (· = ·) n = (· = ·) := by
  induction n with
  | zero => rfl;
  | succ n ih => aesop

end RelItr

namespace Kripke


structure Frame (δ) where
  [δ_inhabited : Inhabited δ]
  Rel : Rel δ δ

set_option linter.unusedVariables false in
abbrev Frame.World (F : Frame δ) := δ

abbrev Frame.default {F : Frame δ} : F.World := F.δ_inhabited.default
scoped notation "﹫" => Frame.default


instance : CoeFun (Frame δ) (λ F => F.World → F.World → Prop) := ⟨Frame.Rel⟩

abbrev Frame.Rel' {F : Frame δ} (x y : F.World) := F.Rel x y
scoped infix:45 " ≺ " => Frame.Rel'

protected abbrev Frame.RelItr' {F : Frame δ} (n : ℕ) (x y : F.World) : Prop := RelItr (· ≺ ·) n x y
scoped notation x:45 " ≺^[" n "] " y:46 => Frame.RelItr' n x y

instance : CoeFun (Frame δ) (λ _ => δ → δ → Prop) := ⟨Frame.Rel⟩

-- protected def Frame.finite (F : Frame δ) := Finite F.World

set_option linter.unusedVariables false in
/-- dependent-version frame -/
abbrev Frame.Dep (δ) (α : Type*) := Frame δ

abbrev Frame.alt (F : Frame δ) (α : Type*) : Frame.Dep δ α := F
notation:max F:max "[" α "]" => Frame.alt F α


structure FiniteFrame (δ) extends Frame δ where
  [δ_finite : Finite δ]

instance : Coe (FiniteFrame δ) (Frame δ) := ⟨λ F ↦ F.toFrame⟩


abbrev FrameClass := Set ((δ : Type*) × Frame δ)

set_option linter.unusedVariables false in
/-- dependent-version frame class -/
abbrev FrameClass.Dep (α : Type*) := FrameClass

abbrev FrameClass.alt (𝔽 : FrameClass) (α : Type*) : FrameClass.Dep α := 𝔽
notation:max 𝔽:max "[" α "]" => FrameClass.alt 𝔽 α

-- abbrev FrameClass.finite (𝔽 : FrameClass) := ∀ {δ F}, ⟨δ, F⟩ ∈ 𝔽 → F.finite

def FrameClass.toFinite (𝔽 : FrameClass) : FrameClass := { ⟨δ, F⟩ | Finite δ ∧ ⟨δ, F⟩ ∈ 𝔽 }
postfix:max "ᶠ" => FrameClass.toFinite


abbrev FiniteFrameClass := Set ((δ : Type*) × FiniteFrame δ)

/-
set_option linter.unusedVariables false in
/-- dependent-version frame class -/
abbrev FiniteFrameClass.Dep (α : Type*) := FiniteFrameClass

abbrev FiniteFrameClass.alt (𝔽 : FiniteFrameClass) (α : Type*) : FiniteFrameClass.Dep α := 𝔽
notation:max 𝔽:max "[" α "]" => FiniteFrameClass.alt 𝔽 α
-/

def FiniteFrameClass.toFrameClass (𝔽 : FiniteFrameClass) : FrameClass := { ⟨δ, F⟩ | ∃ F', ⟨δ, F'⟩ ∈ 𝔽 ∧ F'.toFrame = F }
instance : Coe (FiniteFrameClass) (FrameClass) := ⟨FiniteFrameClass.toFrameClass⟩


/-- Frame with single world and identiy relation -/
abbrev TerminalFrame : FiniteFrame (Fin 1) where
  Rel := λ _ _ => True

@[simp]
lemma TerminalFrame.iff_rel' {x y : TerminalFrame.World} : x ≺ y ↔ x = y := by
  simp [Frame.Rel']; ext1; simp;

@[simp]
lemma TerminalFrame.iff_relItr' {x y : TerminalFrame.World} : x ≺^[n] y ↔ x = y := by
  induction n <;> aesop;


abbrev PointFrame : FiniteFrame (Fin 1) where
  Rel := (λ _ _ => False)

@[simp]
lemma PointFrame.iff_rel' {x y : PointFrame.World} : ¬(x ≺ y) := by simp [Frame.Rel'];


/-
namespace FrameClass

variable  {𝔽 𝔽₁ 𝔽₂ : FrameClass}

abbrev Nonempty (𝔽 : FrameClass) := ∃ (α : Type), 𝔽.Nonempty

abbrev UNonempty (𝔽 : FrameClass) := ∃ (α : Type*), (𝔽 α).Nonempty

abbrev union (𝔽₁ 𝔽₂ : FrameClass) : FrameClass := λ α => 𝔽₁ α ∪ 𝔽₂ α
instance : Union FrameClass := ⟨FrameClass.union⟩

abbrev inter (𝔽₁ 𝔽₂ : FrameClass) : FrameClass := λ α => 𝔽₁ α ∩ 𝔽₂ α
instance : Inter FrameClass := ⟨FrameClass.inter⟩

abbrev subset (𝔽₁ 𝔽₂ : FrameClass) := ∀ α, 𝔽₁ α ⊆ 𝔽₂ α
instance : HasSubset FrameClass := ⟨FrameClass.subset⟩

@[refl]
lemma subset_self : 𝔽 ⊆ 𝔽 := by intro; rfl;

end FrameClass
-/

-- abbrev FrameClass.heq (𝔽₁ 𝔽₂ : FrameClass) := ∀ α, 𝔽₁ α = 𝔽₂ α

-- def FrameClass.mem (F : Frame δ) (𝔽 : FrameClass) : Prop := F ∈ 𝔽 α

-- abbrev FiniteFrameClass (δ) := Set (FiniteFrame δ)

/-
-/

abbrev Valuation (F : Frame δ) (α : Type*) := F.World → α → Prop

structure Model (δ α) where
  Frame : Frame δ
  Valuation : Valuation Frame α

abbrev Model.World (M : Model δ α) := M.Frame.World
-- instance : CoeSort (Model α) (Type _) where coe := Model.World


end Kripke


variable {δ α : Type*}

open Standard.Kripke

def Formula.kripke_satisfies (M : Kripke.Model δ α) (x : M.World) : Formula α → Prop
  | atom a  => M.Valuation x a
  | verum   => True
  | falsum  => False
  | and p q => (kripke_satisfies M x p) ∧ (kripke_satisfies M x q)
  | or p q  => (kripke_satisfies M x p) ∨ (kripke_satisfies M x q)
  | imp p q => (kripke_satisfies M x p) → (kripke_satisfies M x q)
  | box p   => ∀ {y}, x ≺ y → (kripke_satisfies M y p)

namespace Formula.kripke_satisfies

-- protected instance semantics : Semantics (Formula α) ((M : Model δ α) × M.World) := ⟨fun ⟨M, x⟩ ↦ Formula.kripke_satisfies M x⟩
protected instance semantics {M : Model δ α} : Semantics (Formula α) (M.World) := ⟨fun x ↦ Formula.kripke_satisfies M x⟩

variable {M : Model δ α} {x : M.World} {p q : Formula α}

@[simp] protected lemma iff_models : x ⊧ p ↔ kripke_satisfies M x p := iff_of_eq rfl

lemma and_def : x ⊧ p ⋏ q ↔ x ⊧ p ∧ x ⊧ q := by
  constructor;
  . intro ⟨hp, hq⟩; exact ⟨hp, hq⟩;
  . intro h; exact ⟨h.1, h.2⟩;

protected instance tarski : Semantics.Tarski (M.World) where
  realize_top := by intro; trivial;
  realize_bot := by aesop;
  realize_not := by aesop;
  realize_and := and_def;
  realize_or  := by aesop;
  realize_imp := by aesop;


lemma dia_def : x ⊧ ◇p ↔ ∃ y, x ≺ y ∧ y ⊧ p := by simp [kripke_satisfies];

lemma multibox_def : x ⊧ □^[n]p ↔ ∀ {y}, x ≺^[n] y → y ⊧ p := by
  induction n generalizing x with
  | zero => aesop;
  | succ n ih =>
    constructor;
    . intro h y Rxy;
      simp [kripke_satisfies] at h;
      obtain ⟨u, Rxu, Ruy⟩ := Rxy;
      exact (ih.mp $ h Rxu) Ruy;
    . simp;
      intro h y Rxy;
      apply ih.mpr;
      intro u Ryu;
      exact h _ Rxy Ryu;

lemma multidia_def : x ⊧ ◇^[n]p ↔ ∃ y, x ≺^[n] y ∧ y ⊧ p := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih =>
    constructor;
    . intro h;
      replace h : x ⊧ (◇◇^[n]p) := by simpa using h;
      obtain ⟨v, hwv, hv⟩ := dia_def.mp h;
      obtain ⟨x, hvx, hx⟩ := ih.mp hv;
      use x;
      constructor;
      . use v;
      . assumption;
    . intro h;
      obtain ⟨y, Rxy, hy⟩ := h;
      obtain ⟨u, Rxu, Ruy⟩ := Rxy;
      simp;
      apply dia_def.mpr;
      use u;
      constructor;
      . exact Rxu;
      . apply ih.mpr;
        use y;

end Formula.kripke_satisfies


def Formula.valid_on_KripkeModel (M : Model δ α) (p : Formula α) := ∀ x : M.World, x ⊧ p

namespace Formula.valid_on_KripkeModel

protected instance : Semantics (Formula α) (Model δ α) := ⟨fun M ↦ Formula.valid_on_KripkeModel M⟩

@[simp] protected lemma iff_models {M : Model δ α} : M ⊧ f ↔ valid_on_KripkeModel M f := iff_of_eq rfl

instance : Semantics.Bot (Model δ α) where
  realize_bot M := by simp [valid_on_KripkeModel, kripke_satisfies]; use ﹫;

end Formula.valid_on_KripkeModel


def Formula.valid_on_KripkeFrame (F : Frame δ) (p : Formula α) := ∀ V, (⟨F, V⟩ : Model δ α) ⊧ p

namespace Formula.valid_on_KripkeFrame

protected instance semantics : Semantics (Formula α) (Frame.Dep δ α) := ⟨fun F ↦ Formula.valid_on_KripkeFrame F⟩

variable {F : Frame.Dep δ α}

@[simp] protected lemma models_iff : F ⊧ p ↔ valid_on_KripkeFrame F p := iff_of_eq rfl


instance : Semantics.Bot (Frame.Dep δ α) where
  realize_bot _ := by simp [valid_on_KripkeFrame];


protected lemma axiomK : F ⊧* 𝗞 := by
  simp [valid_on_KripkeFrame, valid_on_KripkeModel, System.Axioms.K];
  intro _ p q e V x; subst e;
  intro h₁ h₂ y Rxy;
  exact h₁ Rxy $ h₂ Rxy;

protected lemma nec (h : F ⊧ p) : F ⊧ □p := by
  intro V x y _;
  exact h V y;

protected lemma mdp (hpq : F ⊧ p ⟶ q) (hp : F ⊧ p) : F ⊧ q := by
  intro V x;
  exact (hpq V x) (hp V x);

end Formula.valid_on_KripkeFrame


@[simp] def Formula.valid_on_KripkeFrameClass (𝔽 : FrameClass) (p : Formula α) := ∀ {δ}, ∀ {F : Frame δ}, ⟨δ, F⟩ ∈ 𝔽 → F[α] ⊧ p

namespace Formula.valid_on_KripkeFrameClass

protected instance semantics : Semantics (Formula α) (FrameClass.Dep α) := ⟨fun 𝔽 ↦ valid_on_KripkeFrameClass 𝔽⟩

variable {𝔽 : FrameClass.Dep α}

@[simp] protected lemma models_iff : 𝔽 ⊧ p ↔ Formula.valid_on_KripkeFrameClass 𝔽 p := iff_of_eq rfl


protected lemma axiomK : 𝔽 ⊧* 𝗞 := by
  simp only [Semantics.RealizeSet.setOf_iff];
  rintro f ⟨p, q, _⟩ _ F _;
  apply (Semantics.RealizeSet.setOf_iff.mp $ valid_on_KripkeFrame.axiomK) f;
  use p, q;

protected lemma nec (h : 𝔽 ⊧ p) : 𝔽 ⊧ □p := by
  intro _ _ hF;
  apply valid_on_KripkeFrame.nec;
  exact h hF;

protected lemma mdp (hpq : 𝔽 ⊧ p ⟶ q) (hp : 𝔽 ⊧ p) : 𝔽 ⊧ q := by
  intro _ _ hF;
  exact valid_on_KripkeFrame.mdp (hpq hF) (hp hF)

end Formula.valid_on_KripkeFrameClass


namespace AxiomSet

variable {Ax Ax₁ Ax₂ : AxiomSet α}

def DefinesKripkeFrameClass (Ax : AxiomSet α) (𝔽 : FrameClass) := ∀ {δ}, ∀ {F : Frame δ}, F[α] ⊧* Ax ↔ ⟨δ, F⟩ ∈ 𝔽

lemma DefinesKripkeFrameClass.union (defines₁ : Ax₁.DefinesKripkeFrameClass 𝔽₁) (defines₂ : Ax₂.DefinesKripkeFrameClass 𝔽₂)
  : (Ax₁ ∪ Ax₂).DefinesKripkeFrameClass (𝔽₁ ∩ 𝔽₂) := by
  intro _ F;
  simp only [Semantics.RealizeSet.union_iff];
  constructor;
  . intro ⟨h₁, h₂⟩;
    constructor;
    . exact defines₁.mp h₁;
    . exact defines₂.mp h₂;
  . intro ⟨h₁, h₂⟩;
    constructor;
    . apply defines₁.mpr h₁;
    . apply defines₂.mpr h₂;


def FinitelyDefinesKripkeFrameClass (Ax : AxiomSet α) (𝔽 : FiniteFrameClass) := ∀ {δ}, ∀ {F : FiniteFrame δ}, (↑F : Frame δ)[α] ⊧* Ax ↔ ⟨δ, F⟩ ∈ 𝔽

lemma FinitelyDefinesKripkeFrameClass.union (defines₁ : Ax₁.FinitelyDefinesKripkeFrameClass 𝔽₁) (defines₂ : Ax₂.FinitelyDefinesKripkeFrameClass 𝔽₂)
  : (Ax₁ ∪ Ax₂).FinitelyDefinesKripkeFrameClass (𝔽₁ ∩ 𝔽₂) := by
  intro _ F;
  simp [Semantics.RealizeSet.union_iff];
  constructor;
  . rintro ⟨h₁, h₂⟩;
    constructor;
    . exact defines₁.mp h₁;
    . exact defines₂.mp h₂;
  . intro ⟨h₁, h₂⟩;
    constructor;
    . exact defines₁.mpr h₁;
    . exact defines₂.mpr h₂;

/-
lemma DefinesKripkeFrameClass.toFinitely (defines : Ax.DefinesKripkeFrameClass 𝔽) : Ax.FinitelyDefinesKripkeFrameClass 𝔽 := by
  intro _ F;
  constructor;
  . intro h;
    exact defines.mp h
  . rintro h₁;
    exact defines.mpr h₁;
-/
/-
instance {𝔽 : FrameClass α} (ne : 𝔽ᶠ.Nonempty) : 𝔽.Nonempty := by
  obtain ⟨F, hF⟩ := ne;
  simp [FrameClass.toFinite] at hF;
  use F;
  exact hF.1;
-/

end AxiomSet


namespace Kripke

open Formula
open AxiomSet (DefinesKripkeFrameClass)

abbrev AllFrameClass : FrameClass := Set.univ

lemma AllFrameClass.nonempty : AllFrameClass.Nonempty.{0} := by
  use ⟨Fin 1, TerminalFrame⟩;
  trivial;

lemma axiomK_defines : 𝗞.DefinesKripkeFrameClass (α := α) (AllFrameClass) := by
  intro F;
  simp only [Set.mem_univ, iff_true];
  exact valid_on_KripkeFrame.axiomK;

lemma axiomK_union_definability {Ax : AxiomSet α} : (Ax.DefinesKripkeFrameClass 𝔽) ↔ (𝗞 ∪ Ax).DefinesKripkeFrameClass 𝔽 := by
  constructor;
  . intro defines _ F;
    simp [DefinesKripkeFrameClass] at defines;
    constructor;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff] at h;
      exact defines.mp h.2;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff];
      constructor;
      . apply valid_on_KripkeFrame.axiomK;
      . exact defines.mpr h;
  . intro defines _ F;
    simp only [DefinesKripkeFrameClass] at defines;
    constructor;
    . intro h;
      apply defines.mp;
      simp only [Semantics.RealizeSet.union_iff];
      constructor;
      . apply valid_on_KripkeFrame.axiomK;
      . exact h;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff] at defines;
      exact defines.mpr h |>.2;


/-
def nonempty_of_exist_finiteFrame {𝔽 : FrameClass α} (h : ∃ (F : FiniteFrame δ), F.toFrame ∈ 𝔽) : 𝔽ᶠ.Nonempty := by
  obtain ⟨F, hF⟩ := h;
  use F.toFrame;
  constructor;
  . assumption;
  . exact F.World_finite;
-/

end Kripke


namespace DeductionParameter

open Kripke
variable {Λ Λ₁ Λ₂ : DeductionParameter α} [Λ.IsNormal]
variable {Ax : AxiomSet α}

abbrev DefinesKripkeFrameClass (Λ : DeductionParameter α) [Λ.IsNormal] (𝔽 : FrameClass) := AxiomSet.DefinesKripkeFrameClass (Ax(Λ)) 𝔽

lemma DefinesKripkeFrameClass.toAx (defines : Λ.DefinesKripkeFrameClass 𝔽) : Ax(Λ).DefinesKripkeFrameClass 𝔽 := by
  simp [DefinesKripkeFrameClass] at defines;
  exact defines;

lemma DefinesKripkeFrameClass.toAx' (defines : Axᴺ.DefinesKripkeFrameClass 𝔽) : Ax.DefinesKripkeFrameClass 𝔽 := by
  simp [DefinesKripkeFrameClass] at defines;
  exact axiomK_union_definability.mpr defines;

lemma DefinesKripkeFrameClass.ofAx (defines : Ax.DefinesKripkeFrameClass 𝔽) [Axᴺ.IsNormal] : (Ax)ᴺ.DefinesKripkeFrameClass 𝔽 := by
  apply axiomK_union_definability.mp;
  assumption;


-- abbrev FinitelyDefinesKripkeFrameClass (Λ : DeductionParameter α) [Λ.IsNormal] (𝔽 : FrameClass) := AxiomSet.FinitelyDefinesKripkeFrameClass (Ax(Λ)) 𝔽

end DeductionParameter



end LO.Modal.Standard
