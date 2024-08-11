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

lemma forward {R} {n : ℕ} : (RelItr R (n + 1) x y) ↔ ∃ z, RelItr R n x z ∧ R z y := by
  induction n generalizing x y with
  | zero => simp_all;
  | succ n ih =>
    constructor;
    . rintro ⟨z, Rxz, Rzy⟩;
      obtain ⟨w, Rzw, Rwy⟩ := ih.mp Rzy;
      use w;
      constructor;
      . use z;
      . assumption;
    . rintro ⟨z, ⟨w, Rxw, Rwz⟩, Rzy⟩;
      use w;
      constructor;
      . assumption;
      . apply ih.mpr;
        use z;

end RelItr

namespace Kripke


structure Frame where
  World : Type*
  Rel : Rel World World
  [World_nonempty : Nonempty World]

instance {F : Frame} : Nonempty F.World := F.World_nonempty

instance : CoeSort Frame (Type u) := ⟨Frame.World⟩
instance : CoeFun Frame (λ F => F.World → F.World → Prop) := ⟨Frame.Rel⟩

abbrev Frame.Rel' {F : Frame} (x y : F.World) := F.Rel x y
scoped infix:45 " ≺ " => Frame.Rel'

protected abbrev Frame.RelItr' {F : Frame} (n : ℕ) : _root_.Rel F.World F.World := RelItr (· ≺ ·) n
scoped notation x:45 " ≺^[" n "] " y:46 => Frame.RelItr' n x y

noncomputable abbrev Frame.default {F : Frame} : F.World := Classical.choice F.World_nonempty
notation "﹫" => Frame.default

namespace Frame.RelItr'

lemma congr {F : Frame} {x y : F.World} {n m : ℕ} (h : x ≺^[n] y) (he : n = m := by omega) : x ≺^[m] y := by
  subst_vars; exact h;


lemma forward {F : Frame} {x y : F.World} : x ≺^[n + 1] y ↔ ∃ z, x ≺^[n] z ∧ z ≺ y := RelItr.forward

lemma comp {F : Frame} {x y : F.World} {n m : ℕ} : (∃ z, x ≺^[n] z ∧ z ≺^[m] y) ↔ x ≺^[n + m] y := by
  constructor;
  . rintro ⟨z, hzx, hzy⟩;
    induction n generalizing x with
    | zero => simp_all;
    | succ n ih =>
      suffices x ≺^[(n + m + 1)] y by apply congr this;
      obtain ⟨w, hxw, hwz⟩ := hzx;
      use w;
      constructor;
      . exact hxw;
      . exact @ih w hwz;
  . rintro h;
    induction n generalizing x with
    | zero => simp_all;
    | succ n ih =>
      have rxy : x ≺^[n + m + 1] y := congr h;
      obtain ⟨w, rxw, rwy⟩ := rxy;
      obtain ⟨u, rwu, ruy⟩ := @ih w rwy;
      use u;
      constructor;
      . use w;
      . assumption;

lemma comp' {F : Frame} {x y : F.World} {n m : ℕ+} : (∃ z, x ≺^[n] z ∧ z ≺^[m] y) ↔ x ≺^[n + m] y := comp

end Frame.RelItr'


set_option linter.unusedVariables false in
/-- dependent-version frame -/
abbrev Frame.Dep (α : Type*) := Frame

abbrev Frame.alt (F : Frame) {α} : Frame.Dep α := F
scoped postfix:max "#" => Frame.alt


structure FiniteFrame extends Frame where
  [World_finite : Finite World]

instance {F : FiniteFrame} : Finite (F.World) := F.World_finite
instance : Coe (FiniteFrame) (Frame) := ⟨λ F ↦ F.toFrame⟩


open Relation (ReflTransGen TransGen)

protected abbrev Frame.RelReflTransGen {F : Frame} : _root_.Rel F.World F.World:= ReflTransGen (· ≺ ·)
scoped infix:45 " ≺^* " => Frame.RelReflTransGen

namespace Frame.RelReflTransGen

variable {F : Frame}

@[simp] lemma single {x y : F.World} (hxy : x ≺ y) : x ≺^* y := ReflTransGen.single hxy

@[simp] lemma reflexive : Reflexive F.RelReflTransGen := Relation.reflexive_reflTransGen

@[simp] lemma refl {x : F.World} : x ≺^* x := reflexive x

@[simp] lemma transitive : Transitive F.RelReflTransGen := Relation.transitive_reflTransGen

@[simp] lemma symmetric : Symmetric F.Rel → Symmetric F.RelReflTransGen := ReflTransGen.symmetric

end Frame.RelReflTransGen


abbrev Frame.TransitiveReflexiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^* ·)
postfix:max "^*" => Frame.TransitiveReflexiveClosure

namespace Frame.TransitiveReflexiveClosure

variable {F : Frame}

lemma single {x y : F.World} (hxy : x ≺ y) : F^* x y := ReflTransGen.single hxy

lemma rel_reflexive : Reflexive F^* := by intro x; exact ReflTransGen.refl;

lemma rel_transitive : Transitive F^* := by simp;

lemma rel_symmetric : Symmetric F.Rel → Symmetric F^* := ReflTransGen.symmetric

end Frame.TransitiveReflexiveClosure


def Frame.RelItr'.toReflTransGen {F : Frame} {x y : F.World} {n : ℕ} (h : x ≺^[n] y) : x ≺^* y := by
  induction n generalizing x y with
  | zero => subst h; exact Relation.ReflTransGen.refl;
  | succ n ih =>
    obtain ⟨z, Rxz, Rzy⟩ := h;
    exact Relation.ReflTransGen.head Rxz $ ih Rzy;


protected abbrev Frame.RelTransGen {F : Frame} : _root_.Rel F.World F.World := TransGen (· ≺ ·)
scoped infix:45 " ≺^+ " => Frame.RelTransGen

namespace Frame.RelTransGen

variable {F : Frame}

@[simp] lemma single {x y : F.World} (hxy : x ≺ y) : x ≺^+ y := TransGen.single hxy

@[simp]
lemma transitive : Transitive F.RelTransGen := λ _ _ _ => TransGen.trans

@[simp]
lemma symmetric (hSymm : Symmetric F.Rel) : Symmetric F.RelTransGen := by
  intro x y rxy;
  induction rxy with
  | single h => exact TransGen.single $ hSymm h;
  | tail _ hyz ih => exact TransGen.trans (TransGen.single $ hSymm hyz) ih

end Frame.RelTransGen



abbrev Frame.TransitiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^+ ·)
scoped postfix:max "^+" => Frame.TransitiveClosure

namespace Frame.TransitiveClosure

variable {F : Frame}

lemma single {x y : F.World} (hxy : x ≺ y) : F^+ x y := TransGen.single hxy

lemma rel_transitive : Transitive F^+ := by simp;

lemma rel_symmetric (hSymm : Symmetric F.Rel) : Symmetric F.TransitiveClosure := by simp_all

end Frame.TransitiveClosure


abbrev FrameClass := Set (Frame)

set_option linter.unusedVariables false in
/-- dependent-version frame class -/
abbrev FrameClass.Dep (α : Type*) := FrameClass

abbrev FrameClass.alt (𝔽 : FrameClass) {α} : FrameClass.Dep α := 𝔽
scoped postfix:max "#" => FrameClass.alt


abbrev FiniteFrameClass := Set (FiniteFrame)

@[simp]
def FiniteFrameClass.toFrameClass (𝔽 : FiniteFrameClass) : FrameClass := { F | ∃ F', F' ∈ 𝔽 ∧ F'.toFrame = F }
instance : Coe (FiniteFrameClass) (FrameClass) := ⟨FiniteFrameClass.toFrameClass⟩

@[simp]
def FrameClass.toFiniteFrameClass (𝔽 : FrameClass) : FiniteFrameClass := { F | F.toFrame ∈ 𝔽 }
instance : Coe (FrameClass) (FiniteFrameClass) := ⟨FrameClass.toFiniteFrameClass⟩

@[simp]
abbrev FrameClass.restrictFinite (𝔽 : FrameClass) : FrameClass := FiniteFrameClass.toFrameClass ↑𝔽
postfix:max "ꟳ" => FrameClass.restrictFinite

lemma FrameClass.iff_mem_restrictFinite {𝔽 : FrameClass} (h : F ∈ 𝔽) (F_finite : Finite F.World) : F ∈ 𝔽ꟳ := by
  simp;
  use { toFrame := F, World_finite := F_finite };


/-- Frame with single world and identiy relation -/
abbrev terminalFrame : FiniteFrame where
  World := Unit;
  Rel := λ _ _ => True

@[simp]
lemma terminalFrame.iff_rel' {x y : terminalFrame.World} : x ≺ y ↔ x = y := by
  simp [Frame.Rel'];

@[simp]
lemma terminalFrame.iff_relItr' {x y : terminalFrame.World} : x ≺^[n] y ↔ x = y := by
  induction n with
  | zero => simp;
  | succ n ih => simp_all; use ();


abbrev PointFrame : FiniteFrame where
  World := Unit
  Rel := (λ _ _ => False)

@[simp]
lemma PointFrame.iff_rel' {x y : PointFrame.World} : ¬(x ≺ y) := by simp [Frame.Rel'];


abbrev Valuation (F : Frame) (α : Type*) := F.World → α → Prop

structure Model (α) where
  Frame : Frame
  Valuation : Valuation Frame α

abbrev Model.World (M : Model α) := M.Frame.World
instance : CoeSort (Model α) (Type u) := ⟨Model.World⟩

/-
structure FiniteModel (α) extends Model α where
  [World_finite : Finite World]

instance {M : FiniteModel α} : Finite M.World := M.World_finite

def FiniteModel.FiniteFrame (M : FiniteModel α) : Kripke.FiniteFrame where
  World := M.World
  Rel := M.Frame.Rel
-/

end Kripke


variable {World α : Type*}

open Standard.Kripke

def Formula.Kripke.Satisfies (M : Kripke.Model α) (x : M.World) : Formula α → Prop
  | atom a  => M.Valuation x a
  | natom a => ¬M.Valuation x a
  | ⊤  => True
  | ⊥  => False
  | p ⋏ q => (Satisfies M x p) ∧ (Satisfies M x q)
  | p ⋎ q => (Satisfies M x p) ∨ (Satisfies M x q)
  | □p   => ∀ y, x ≺ y → (Satisfies M y p)
  | ◇p   => ∃ y, x ≺ y ∧ (Satisfies M y p)

namespace Formula.Kripke.Satisfies

protected instance semantics {M : Kripke.Model α} : Semantics (Formula α) (M.World) := ⟨fun x ↦ Formula.Kripke.Satisfies M x⟩

variable {M : Kripke.Model α} {x : M.World} {p q : Formula α}

@[simp] protected lemma iff_models : x ⊧ p ↔ Kripke.Satisfies M x p := iff_of_eq rfl

lemma or_def : x ⊧ p ⋎ q ↔ x ⊧ p ∨ x ⊧ q := by constructor <;> { simp [Satisfies]; }

lemma and_def : x ⊧ p ⋏ q ↔ x ⊧ p ∧ x ⊧ q := by constructor <;> { simp [Satisfies]; }

lemma not_def : x ⊧ ~p ↔ ¬(x ⊧ p) := by
  induction p using Formula.rec' generalizing x with
  | hbox p ih =>
    simp_all [Satisfies];
    constructor;
    . rintro ⟨y, Rxy, h⟩;
      use y;
      constructor;
      . assumption;
      . exact ih.mp h;
    . rintro ⟨y, Rxy, h⟩;
      use y;
      constructor;
      . assumption;
      . exact ih.mpr h;
  | hdia p ih =>
    simp_all [Satisfies];
    constructor;
    . intro h y Rxy; exact ih.mp $ h y Rxy;
    . intro h y Rxy; exact ih.mpr $ h y Rxy;
  | _ =>
    simp_all [Satisfies]
    try tauto;

@[simp]
lemma imp_def : x ⊧ p ⟶ q ↔ (x ⊧ p) → (x ⊧ q) := by
  constructor;
  . intro hpq;
    apply imp_iff_not_or (b := x ⊧ q) |>.mpr;
    rcases hpq with (hp | hq);
    . left; exact not_def.mp hp;
    . right; exact hq;
  . intro hpq;
    simp only [Formula.imp_eq];
    rcases imp_iff_not_or.mp hpq with (hp | hq);
    . left; exact not_def.mpr hp;
    . right; exact hq;

protected instance tarski : Semantics.Tarski (M.World) where
  realize_top := by intro; tauto;
  realize_bot := by tauto;
  realize_not := not_def;
  realize_and := and_def;
  realize_or  := or_def;
  realize_imp := imp_def;


lemma dia_def : x ⊧ ◇p ↔ ∃ y, x ≺ y ∧ y ⊧ p := by simp [Kripke.Satisfies];

lemma multibox_def : x ⊧ □^[n]p ↔ ∀ {y}, x ≺^[n] y → y ⊧ p := by
  induction n generalizing x with
  | zero => aesop;
  | succ n ih =>
    constructor;
    . intro h y Rxy;
      simp [Kripke.Satisfies] at h;
      obtain ⟨u, Rxu, Ruy⟩ := Rxy;
      exact (ih.mp $ h _ Rxu) Ruy;
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

lemma trans (hpq : x ⊧ p ⟶ q) (hqr : x ⊧ q ⟶ r) : x ⊧ p ⟶ r := by simp_all;

lemma mdp (hpq : x ⊧ p ⟶ q) (hp : x ⊧ p) : x ⊧ q := by simp_all;

end Formula.Kripke.Satisfies


def Formula.Kripke.ValidOnModel (M : Kripke.Model α) (p : Formula α) := ∀ x : M.World, x ⊧ p

namespace Formula.Kripke.ValidOnModel

protected instance : Semantics (Formula α) (Kripke.Model α) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

@[simp] protected lemma iff_models {M : Kripke.Model α} : M ⊧ f ↔ Kripke.ValidOnModel M f := iff_of_eq rfl

instance : Semantics.Bot (Kripke.Model α) where
  realize_bot M := by simp [Kripke.ValidOnModel, Kripke.Satisfies];

variable {M : Model α} {p q r : Formula α}

protected lemma mdp (hpq : M ⊧ p ⟶ q) (hp : M ⊧ p) : M ⊧ q := by
  intro x;
  exact (Satisfies.imp_def.mp $ hpq x) (hp x);

protected lemma nec (h : M ⊧ p) : M ⊧ □p := by
  intro x y _;
  exact h y;

protected lemma verum : M ⊧ ⊤ := by intro; tauto;

protected lemma imply₁ : M ⊧ (Axioms.Imply₁ p q) := by simp [ValidOnModel]; tauto;

protected lemma imply₂ : M ⊧ (Axioms.Imply₂ p q r) := by simp [ValidOnModel]; tauto;

protected lemma andElim₁ : M ⊧ (Axioms.AndElim₁ p q) := by simp [ValidOnModel]; tauto;

protected lemma andElim₂ : M ⊧ (Axioms.AndElim₂ p q) := by simp [ValidOnModel];

protected lemma andInst : M ⊧ (Axioms.AndInst p q) := by simp [ValidOnModel]; tauto;

protected lemma orInst₁ : M ⊧ (Axioms.OrInst₁ p q) := by simp [ValidOnModel]; tauto;

protected lemma orInst₂ : M ⊧ (Axioms.OrInst₂ p q) := by simp [ValidOnModel]; tauto;

protected lemma orElim : M ⊧ (Axioms.OrElim p q r) := by simp [ValidOnModel]; tauto;

protected lemma dne : M ⊧ (Axioms.DNE p) := by simp [ValidOnModel];

protected lemma negEquiv : M ⊧ (Axioms.NegEquiv p) := by simp [ValidOnModel];

protected lemma diaDual : M ⊧ (Axioms.DiaDuality p) := by
  intro x;
  simp [ValidOnModel, Satisfies];
  constructor;
  . rintro ⟨y, Rxy, hy⟩; use y;
    constructor;
    . exact Rxy;
    . intro h; replace h:= Satisfies.not_def.mp h;
      contradiction;
  . rintro ⟨y, Rxy, hy⟩; use y;
    constructor;
    . exact Rxy;
    . replace hy := Satisfies.not_def.not.mp hy;
      tauto;

protected lemma axiomK : M ⊧ (Axioms.K p q)  := by
  intro V;
  apply Satisfies.imp_def.mpr;
  intro hpq;
  apply Satisfies.imp_def.mpr;
  intro hp x Rxy;
  replace hpq := Satisfies.imp_def.mp $ hpq x Rxy;
  replace hp := hp x Rxy;
  exact hpq hp;

end Formula.Kripke.ValidOnModel


def Formula.Kripke.ValidOnFrame (F : Frame) (p : Formula α) := ∀ V, (⟨F, V⟩ : Kripke.Model α) ⊧ p

namespace Formula.Kripke.ValidOnFrame

protected instance semantics : Semantics (Formula α) (Frame.Dep α) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

variable {F : Frame.Dep α}

@[simp] protected lemma models_iff : F ⊧ p ↔ Kripke.ValidOnFrame F p := iff_of_eq rfl

instance : Semantics.Bot (Frame.Dep α) where
  realize_bot _ := by simp [Kripke.ValidOnFrame];

protected lemma mdp (hpq : F ⊧ p ⟶ q) (hp : F ⊧ p) : F ⊧ q := by intro V; exact ValidOnModel.mdp (hpq V) (hp V);

protected lemma nec (h : F ⊧ p) : F ⊧ □p := by intro V; exact ValidOnModel.nec (h V);

protected lemma verum : F ⊧ ⊤ := by intros _; tauto;

protected lemma imply₁ : F ⊧ (Axioms.Imply₁ p q) := by intro V; exact ValidOnModel.imply₁ (M := ⟨F, V⟩);

protected lemma imply₂ : F ⊧ (Axioms.Imply₂ p q r) := by intro V; exact ValidOnModel.imply₂ (M := ⟨F, V⟩);

protected lemma andElim₁ : F ⊧ (Axioms.AndElim₁ p q) := by intro V; exact ValidOnModel.andElim₁ (M := ⟨F, V⟩);

protected lemma andElim₂ : F ⊧ (Axioms.AndElim₂ p q) := by intro V; exact ValidOnModel.andElim₂ (M := ⟨F, V⟩);

protected lemma andInst : F ⊧ (Axioms.AndInst p q) := by intro V; exact ValidOnModel.andInst (M := ⟨F, V⟩);

protected lemma orInst₁ : F ⊧ (Axioms.OrInst₁ p q) := by intro V; exact ValidOnModel.orInst₁ (M := ⟨F, V⟩);

protected lemma orInst₂ : F ⊧ (Axioms.OrInst₂ p q) := by intro V; exact ValidOnModel.orInst₂ (M := ⟨F, V⟩);

protected lemma orElim : F ⊧ (Axioms.OrElim p q r) := by intro V; exact ValidOnModel.orElim (M := ⟨F, V⟩);

protected lemma dne : F ⊧ (Axioms.DNE p) := by intro V; exact ValidOnModel.dne (M := ⟨F, V⟩);

protected lemma negEquiv : F ⊧ (Axioms.NegEquiv p) := by intro V; exact ValidOnModel.negEquiv (M := ⟨F, V⟩);

protected lemma diaDual : F ⊧ (Axioms.DiaDuality p) := by intro V; exact ValidOnModel.diaDual (M := ⟨F, V⟩);

protected lemma axiomK : F ⊧ (Axioms.K p q) := by intro V; exact ValidOnModel.axiomK (M := ⟨F, V⟩);

protected lemma axiomK_set : F ⊧* 𝗞 := by
  simp [Semantics.realizeSet_iff];
  rintro f x y rfl;
  exact ValidOnFrame.axiomK;

end Formula.Kripke.ValidOnFrame


@[simp] def Formula.Kripke.ValidOnFrameClass (𝔽 : FrameClass) (p : Formula α) := ∀ {F : Frame}, F ∈ 𝔽 → F# ⊧ p

namespace Formula.Kripke.ValidOnFrameClass

protected instance semantics : Semantics (Formula α) (FrameClass.Dep α) := ⟨fun 𝔽 ↦ Kripke.ValidOnFrameClass 𝔽⟩

variable {𝔽 : FrameClass.Dep α}

@[simp] protected lemma models_iff : 𝔽 ⊧ p ↔ Formula.Kripke.ValidOnFrameClass 𝔽 p := iff_of_eq rfl


@[simp] protected lemma mdp (hpq : 𝔽 ⊧ p ⟶ q) (hp : 𝔽 ⊧ p) : 𝔽 ⊧ q := by intro _ hF; exact ValidOnFrame.mdp (hpq hF) (hp hF)

@[simp] protected lemma nec (h : 𝔽 ⊧ p) : 𝔽 ⊧ □p := by intro _ hF; exact ValidOnFrame.nec (h hF);

@[simp] protected lemma verum : 𝔽 ⊧ ⊤ := by intro _ _; tauto;

@[simp] protected lemma imply₁ : 𝔽 ⊧ (Axioms.Imply₁ p q) := by intro _ _; exact ValidOnFrame.imply₁;

@[simp] protected lemma imply₂ : 𝔽 ⊧ (Axioms.Imply₂ p q r)  := by intro _ _; exact ValidOnFrame.imply₂;

@[simp] protected lemma andElim₁ : 𝔽 ⊧ (Axioms.AndElim₁ p q) := by intro _ _; exact ValidOnFrame.andElim₁;

@[simp] protected lemma andElim₂ : 𝔽 ⊧ (Axioms.AndElim₂ p q) := by intro _ _; exact ValidOnFrame.andElim₂;

@[simp] protected lemma andInst : 𝔽 ⊧ (Axioms.AndInst p q) := by intro _ _; exact ValidOnFrame.andInst;

@[simp] protected lemma orInst₁ : 𝔽 ⊧ (Axioms.OrInst₁ p q) := by intro _ _; exact ValidOnFrame.orInst₁;

@[simp] protected lemma orInst₂ : 𝔽 ⊧ (Axioms.OrInst₂ p q) := by intro _ _; exact ValidOnFrame.orInst₂;

@[simp] protected lemma orElim : 𝔽 ⊧ (Axioms.OrElim p q r) := by intro _ _; exact ValidOnFrame.orElim;

@[simp] protected lemma dne : 𝔽 ⊧ (Axioms.DNE p) := by intro _ _; exact ValidOnFrame.dne;

@[simp] protected lemma negEquiv : 𝔽 ⊧ (Axioms.NegEquiv p) := by intro _ _; exact ValidOnFrame.negEquiv;

@[simp] protected lemma diaDual : 𝔽 ⊧ (Axioms.DiaDuality p) := by intro _ _; exact ValidOnFrame.diaDual;

@[simp] protected lemma axiomK : 𝔽 ⊧ (Axioms.K p q) := by intro _ _; exact ValidOnFrame.axiomK;

protected lemma axiomK_set : 𝔽 ⊧* 𝗞 := by
  simp [Semantics.realizeSet_iff];
  rintro f x y rfl;
  exact ValidOnFrameClass.axiomK;

end ValidOnFrameClass

end Formula.Kripke

namespace Kripke

open Formula.Kripke

lemma iff_not_validOnFrameClass {𝔽 : FrameClass} : ¬(𝔽# ⊧ p) ↔ ∃ F ∈ 𝔽, ∃ V x, ¬Satisfies ⟨F, V⟩ x p := by
  simp [ValidOnFrame, ValidOnModel, Satisfies];

lemma iff_not_set_validOnFrameClass {𝔽 : FrameClass} : ¬(𝔽# ⊧* T) ↔ ∃ p ∈ T, ∃ F ∈ 𝔽, ∃ V x, ¬Satisfies ⟨F, V⟩ x p  := by
  simp [Semantics.realizeSet_iff, ValidOnFrame, ValidOnModel, Satisfies];

lemma iff_not_validOnFrame {F : Frame} : ¬(F# ⊧* T) ↔ ∃ p ∈ T, ∃ V x, ¬Satisfies ⟨F, V⟩ x p  := by
  simp [Semantics.realizeSet_iff, ValidOnFrame, ValidOnModel, Satisfies];

end Kripke

namespace AxiomSet

variable {Ax Ax₁ Ax₂ : AxiomSet α}

def DefinesKripkeFrameClass (Ax : AxiomSet α) (𝔽 : FrameClass) := ∀ {F : Frame}, F# ⊧* Ax ↔ F ∈ 𝔽

lemma DefinesKripkeFrameClass.union (defines₁ : Ax₁.DefinesKripkeFrameClass 𝔽₁) (defines₂ : Ax₂.DefinesKripkeFrameClass 𝔽₂)
  : (Ax₁ ∪ Ax₂).DefinesKripkeFrameClass (𝔽₁ ∩ 𝔽₂) := by
  intro F;
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


def FinitelyDefinesKripkeFrameClass (Ax : AxiomSet α) (𝔽 : FiniteFrameClass) := ∀ {F : FiniteFrame}, (↑F : Frame)# ⊧* Ax ↔ F ∈ 𝔽

lemma FinitelyDefinesKripkeFrameClass.union (defines₁ : Ax₁.FinitelyDefinesKripkeFrameClass 𝔽₁) (defines₂ : Ax₂.FinitelyDefinesKripkeFrameClass 𝔽₂)
  : (Ax₁ ∪ Ax₂).FinitelyDefinesKripkeFrameClass (𝔽₁ ∩ 𝔽₂) := by
  intro F;
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

end AxiomSet


namespace Kripke

open Formula
open AxiomSet (DefinesKripkeFrameClass)

abbrev AllFrameClass : FrameClass := Set.univ

lemma AllFrameClass.nonempty : AllFrameClass.Nonempty.{0} := by
  use terminalFrame;
  trivial;

lemma axiomK_defines : DefinesKripkeFrameClass (α := α) 𝗞 AllFrameClass := by
  intro F;
  simp only [Set.mem_univ, iff_true];
  exact Kripke.ValidOnFrame.axiomK_set;

lemma axiomK_union_definability {Ax : AxiomSet α} : (DefinesKripkeFrameClass Ax 𝔽) ↔ DefinesKripkeFrameClass (𝗞 ∪ Ax) 𝔽 := by
  constructor;
  . intro defines F;
    simp [DefinesKripkeFrameClass] at defines;
    constructor;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff] at h;
      exact defines.mp h.2;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff];
      constructor;
      . apply Kripke.ValidOnFrame.axiomK_set;
      . exact defines.mpr h;
  . intro defines F;
    simp only [DefinesKripkeFrameClass] at defines;
    constructor;
    . intro h;
      apply defines.mp;
      simp only [Semantics.RealizeSet.union_iff];
      constructor;
      . apply Kripke.ValidOnFrame.axiomK_set;
      . exact h;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff] at defines;
      exact defines.mpr h |>.2;

end Kripke


namespace DeductionParameter

open Kripke
variable {Λ Λ₁ Λ₂ : DeductionParameter α} [Λ.IsNormal]
variable {Ax : AxiomSet α}

abbrev DefinesKripkeFrameClass (Λ : DeductionParameter α) [Λ.IsNormal] (𝔽 : FrameClass) := AxiomSet.DefinesKripkeFrameClass (Ax(Λ)) 𝔽

lemma DefinesKripkeFrameClass.toAx (defines : Λ.DefinesKripkeFrameClass 𝔽) : Ax(Λ).DefinesKripkeFrameClass 𝔽 := by
  simp [DefinesKripkeFrameClass] at defines;
  exact defines;

lemma DefinesKripkeFrameClass.toAx' (defines : (𝝂Ax).DefinesKripkeFrameClass 𝔽) : Ax.DefinesKripkeFrameClass 𝔽 := by
  simp [DefinesKripkeFrameClass] at defines;
  exact axiomK_union_definability.mpr defines;

lemma DefinesKripkeFrameClass.ofAx (defines : Ax.DefinesKripkeFrameClass 𝔽) [(𝝂Ax).IsNormal] : (𝝂Ax).DefinesKripkeFrameClass 𝔽 := by
  apply axiomK_union_definability.mp;
  assumption;

end DeductionParameter

end LO.Modal.Standard
