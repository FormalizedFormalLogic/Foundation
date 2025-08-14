import Foundation.Vorspiel.HRel.Basic
import Foundation.Modal.Axioms
import Foundation.Modal.Formula
import Foundation.Modal.Logic.Basic

namespace LO.Modal

open Entailment


namespace Kripke

structure Frame where
  World : Type
  Rel : HRel World
  [world_nonempty : Nonempty World]
attribute [simp] Frame.world_nonempty

instance : CoeSort Frame (Type) := ⟨Frame.World⟩
instance : CoeFun Frame (λ F => HRel F.World) := ⟨Frame.Rel⟩
instance {F : Frame} : Nonempty F.World := F.world_nonempty

namespace Frame

open Relation

variable {F : Frame} {x y : F.World}

abbrev Rel' (x y : F.World) := F.Rel x y
infix:45 " ≺ " => Frame.Rel'

abbrev InvRel (x y : F.World) := F.Rel y x
infix:45 " ≻ " => Frame.InvRel

abbrev RelItr' (n : ℕ) := F.Rel.Iterate n
notation x:45 " ≺^[" n:0 "] " y:46 => Frame.RelItr' n x y

@[mk_iff]
class IsFinite (F : Frame) : Prop where [world_finite : Finite F.World]
attribute [simp, instance] IsFinite.world_finite

instance [Finite F.World] : F.IsFinite := ⟨⟩

end Frame



section

def whitepoint : Frame := ⟨Unit, λ _ _ => True⟩

instance : Finite whitepoint.World := by
  dsimp [whitepoint];
  infer_instance

def blackpoint : Frame := ⟨Unit, λ _ _ => False⟩

instance : Finite blackpoint.World := by
  dsimp [blackpoint];
  infer_instance;
instance : IsIrrefl _ blackpoint.Rel := by tauto
instance : IsTrans _ blackpoint.Rel := ⟨by tauto⟩
instance : IsStrictOrder _ blackpoint.Rel where
-- instance : IsConnected _ blackpoint.Rel := ⟨by tauto⟩

end


abbrev FrameClass := Set (Frame)


abbrev Valuation (F : Frame) := F.World → ℕ → Prop

structure Model extends Frame where
  Val : Valuation toFrame
instance : CoeSort Model Type := ⟨λ M => M.toFrame.World⟩
instance : CoeFun (Model) (λ M => M.World → ℕ → Prop) := ⟨fun m => m.Val⟩

end Kripke


namespace Formula.Kripke

def Satisfies (M : Kripke.Model) (x : M.World) : Formula ℕ → Prop
  | atom a  => M x a
  | ⊥  => False
  | φ ➝ ψ => (Satisfies M x φ) ➝ (Satisfies M x ψ)
  | □φ   => ∀ y, x ≺ y → (Satisfies M y φ)

namespace Satisfies

protected instance semantics {M : Kripke.Model} : Semantics (Formula ℕ) (M.World) := ⟨fun x ↦ Formula.Kripke.Satisfies M x⟩

variable {M : Kripke.Model} {x : M.World} {φ ψ : Formula ℕ}

@[simp] protected lemma iff_models : x ⊧ φ ↔ Kripke.Satisfies M x φ := iff_of_eq rfl

@[simp] lemma atom_def : x ⊧ atom a ↔ M x a := by simp [Satisfies];

protected lemma bot_def : ¬x ⊧ ⊥ := by simp [Satisfies];

protected lemma imp_def : x ⊧ φ ➝ ψ ↔ (x ⊧ φ) → (x ⊧ ψ) := by tauto;
protected lemma not_imp_def : ¬(x ⊧ φ ➝ ψ) ↔ (x ⊧ φ) ∧ ¬(x ⊧ ψ) := by constructor <;> . contrapose!; tauto;

protected lemma imp_def₂ : x ⊧ φ ➝ ψ ↔ ¬x ⊧ φ ∨ x ⊧ ψ := by tauto;

protected lemma or_def : x ⊧ φ ⋎ ψ ↔ x ⊧ φ ∨ x ⊧ ψ := by simp [Satisfies]; tauto;

protected lemma and_def : x ⊧ φ ⋏ ψ ↔ x ⊧ φ ∧ x ⊧ ψ := by simp [Satisfies];

protected lemma not_def : x ⊧ ∼φ ↔ ¬(x ⊧ φ) := by simp [Satisfies];

protected lemma top_def : x ⊧ ⊤ := by simp [Satisfies];

protected lemma box_def : x ⊧ □φ ↔ ∀ y, x ≺ y → y ⊧ φ := by simp [Satisfies];
protected lemma not_box_def : ¬x ⊧ □φ ↔ (∃ y, x ≺ y ∧ ¬y ⊧ φ) := by simp [Satisfies];

protected lemma dia_def : x ⊧ ◇φ ↔ ∃ y, x ≺ y ∧ y ⊧ φ := by simp [Satisfies];
protected lemma not_dia_def : ¬x ⊧ ◇φ ↔ ∀ y, x ≺ y → ¬(y ⊧ φ) := by simp [Satisfies];

protected instance : Semantics.Tarski (M.World) where
  realize_top := λ _ => Satisfies.top_def;
  realize_bot := λ _ => Satisfies.bot_def;
  realize_imp := Satisfies.imp_def;
  realize_not := Satisfies.not_def;
  realize_or := Satisfies.or_def;
  realize_and := Satisfies.and_def;

lemma iff_def : x ⊧ φ ⭤ ψ ↔ (x ⊧ φ ↔ x ⊧ ψ) := by simp [Satisfies];

@[simp] lemma negneg_def : x ⊧ ∼∼φ ↔ x ⊧ φ := by simp;

lemma multibox_dn : x ⊧ □^[n](∼∼φ) ↔ x ⊧ □^[n]φ := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih =>
    suffices x ⊧ (□□^[n](∼∼φ)) ↔ x ⊧ (□□^[n]φ) by simpa;
    constructor;
    . intro h y Rxy;
      exact ih.mp $ (h y Rxy);
    . intro h y Rxy;
      exact ih.mpr $ (h y Rxy);

lemma box_dn : x ⊧ □(∼∼φ) ↔ x ⊧ □φ := multibox_dn (n := 1)

lemma multidia_dn : x ⊧ ◇^[n](∼∼φ) ↔ x ⊧ ◇^[n]φ := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih =>
    suffices x ⊧ (◇◇^[n](∼∼φ)) ↔ x ⊧ (◇◇^[n]φ) by simpa;
    constructor;
    . intro h;
      obtain ⟨y, Rxy, h⟩ := Satisfies.dia_def.mp h;
      apply Satisfies.dia_def.mpr;
      use y;
      constructor;
      . exact Rxy;
      . exact ih.mp h;
    . intro h;
      obtain ⟨y, Rxy, h⟩ := Satisfies.dia_def.mp h;
      apply Satisfies.dia_def.mpr;
      use y;
      constructor;
      . exact Rxy;
      . exact ih.mpr h;

lemma dia_dn : x ⊧ ◇(∼∼φ) ↔ x ⊧ ◇φ := multidia_dn (n := 1)

lemma multibox_def : x ⊧ □^[n]φ ↔ ∀ {y}, x ≺^[n] y → y ⊧ φ := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih =>
    constructor;
    . rintro h y ⟨z, Rxz, Rzy⟩;
      replace h : ∀ y, x ≺ y → y ⊧ □^[n]φ := Satisfies.box_def.mp $ by simpa using h;
      exact (ih.mp $ h _ Rxz) Rzy;
    . suffices (∀ {y z}, x ≺ z → z ≺^[n] y → Satisfies M y φ) → x ⊧ (□□^[n]φ) by simpa;
      intro h y Rxy;
      apply ih.mpr;
      intro z Ryz;
      exact h Rxy Ryz;

lemma multidia_def : x ⊧ ◇^[n]φ ↔ ∃ y, x ≺^[n] y ∧ y ⊧ φ := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih =>
    constructor;
    . intro h;
      replace h : x ⊧ (◇◇^[n]φ) := by simpa using h;
      obtain ⟨y, Rxy, hv⟩ := Satisfies.dia_def.mp h;
      obtain ⟨x, Ryx, hx⟩ := ih.mp hv;
      use x;
      constructor;
      . use y;
      . assumption;
    . rintro ⟨y, ⟨z, Rxz, Rzy⟩, hy⟩;
      suffices x ⊧ ◇◇^[n]φ by simpa;
      apply Satisfies.dia_def.mpr;
      use z;
      constructor;
      . assumption;
      . apply ih.mpr;
        use y;

lemma disj_def : x ⊧ ⋁Γ ↔ ∃ φ ∈ Γ, x ⊧ φ := by
  induction Γ using List.induction_with_singleton with
  | hcons φ Γ hΓ ih =>
    suffices x ⊧ φ ∨ x ⊧ ⋁Γ ↔ x ⊧ φ ∨ ∃ a ∈ Γ, x ⊧ a by simp [List.disj₂_cons_nonempty hΓ];
    constructor;
    . rintro (_ | h)
      . tauto;
      . right; exact ih.mp h;
    . rintro (_ | h);
      . tauto;
      . right; exact ih.mpr h;
  | _ => simp;

lemma conj₁_def {Γ : List _} : x ⊧ Γ.conj ↔ ∀ φ ∈ Γ, x ⊧ φ := by induction Γ <;> simp;

lemma conj_def : x ⊧ ⋀Γ ↔ ∀ φ ∈ Γ, x ⊧ φ := by
  induction Γ using List.induction_with_singleton with
  | hcons φ Γ hΓ ih =>
    suffices (x ⊧ φ ∧ x ⊧ ⋀Γ) ↔ (x ⊧ φ ∧ ∀ φ ∈ Γ, x ⊧ φ) by simp [List.conj₂_cons_nonempty hΓ];
    constructor;
    . intro ⟨_, hΓ⟩;
      constructor;
      . assumption;
      . exact ih.mp hΓ;
    . intro ⟨_, hΓ⟩;
      constructor;
      . assumption;
      . apply ih.mpr hΓ;
  | _ => simp;

lemma fconj_def {Γ : Finset _} : x ⊧ Γ.conj ↔ ∀ φ ∈ Γ, x ⊧ φ := by
  simp only [Semantics.realize_finset_conj];

lemma fdisj_def {Γ : Finset _} : x ⊧ Γ.disj ↔ ∃ φ ∈ Γ, x ⊧ φ := by
  simp only [Semantics.realize_finset_disj];

lemma trans (hpq : x ⊧ φ ➝ ψ) (hqr : x ⊧ ψ ➝ χ) : x ⊧ φ ➝ χ := by simp_all;

lemma mdp (hpq : x ⊧ φ ➝ ψ) (hp : x ⊧ φ) : x ⊧ ψ := by simp_all;


lemma intro_neg_semiequiv (h : x ⊧ φ → x ⊧ ψ) : x ⊧ ∼ψ → x ⊧ ∼φ := by
  contrapose;
  simp_all [Satisfies];

lemma intro_multibox_semiequiv (h : ∀ y, x ≺^[n] y → y ⊧ φ → y ⊧ ψ) : x ⊧ □^[n]φ → x ⊧ □^[n]ψ := by
  induction n generalizing x with
  | zero => simp_all;
  | succ n ih =>
    intro hφ;
    apply Satisfies.multibox_def.mpr;
    rintro y ⟨z, Rxz, Rzy⟩;
    replace hφ : x ⊧ □□^[n]φ := by simpa using hφ;
    refine Satisfies.multibox_def.mp (@ih z ?_ (Satisfies.box_def.mp hφ z Rxz)) Rzy;
    . intro w Rzw;
      apply h w;
      use z;

lemma intro_box_semiequiv (h : ∀ y, x ≺ y → y ⊧ φ → y ⊧ ψ) : x ⊧ □φ → x ⊧ □ψ := by
  apply intro_multibox_semiequiv (n := 1);
  simpa;

lemma intro_multidia_semiequiv (h : ∀ y, x ≺^[n] y → y ⊧ φ → y ⊧ ψ) : x ⊧ ◇^[n]φ → x ⊧ ◇^[n]ψ := by
  induction n generalizing x with
  | zero => simp_all;
  | succ n ih =>
    simp only [Dia.multidia_succ];
    apply intro_neg_semiequiv;
    apply intro_box_semiequiv;
    intro y Rxy;
    apply intro_neg_semiequiv;
    apply ih;
    intro z Ryz;
    apply h;
    use y;

lemma intro_dia_semiequiv (h : ∀ y, x ≺ y → y ⊧ φ → y ⊧ ψ) : x ⊧ ◇φ → x ⊧ ◇ψ := by
  apply intro_multidia_semiequiv (n := 1);
  simpa;


lemma intro_negEquiv (h : x ⊧ φ ↔ x ⊧ ψ) : x ⊧ ∼φ ↔ x ⊧ ∼ψ := by
  constructor;
  . apply intro_neg_semiequiv $ h.mpr;
  . apply intro_neg_semiequiv $ h.mp;

lemma intro_multibox_equiv (h : ∀ y, x ≺^[n] y → (y ⊧ φ ↔ y ⊧ ψ)) : x ⊧ □^[n]φ ↔ x ⊧ □^[n]ψ := by
  constructor;
  . apply intro_multibox_semiequiv; intro y Rxy; apply h y Rxy |>.mp;
  . apply intro_multibox_semiequiv; intro y Rxy; apply h y Rxy |>.mpr;

lemma intro_box_equiv (h : ∀ y, x ≺ y → (y ⊧ φ ↔ y ⊧ ψ)) : x ⊧ □φ ↔ x ⊧ □ψ := by
  apply intro_multibox_equiv (n := 1);
  simpa;

lemma intro_multidia_equiv (h : ∀ y, x ≺^[n] y → (y ⊧ φ ↔ y ⊧ ψ)) : x ⊧ ◇^[n]φ ↔ x ⊧ ◇^[n]ψ := by
  constructor;
  . apply intro_multidia_semiequiv; intro y Rxy; apply h y Rxy |>.mp;
  . apply intro_multidia_semiequiv; intro y Rxy; apply h y Rxy |>.mpr;

lemma intro_dia_equiv (h : ∀ y, x ≺ y → (y ⊧ φ ↔ y ⊧ ψ)) : x ⊧ ◇φ ↔ x ⊧ ◇ψ := by
  apply intro_multidia_equiv (n := 1);
  simpa;


lemma dia_dual : x ⊧ ◇φ ↔ x ⊧ ∼□(∼φ) := by simp [Satisfies];

lemma multidia_dual : x ⊧ ◇^[n]φ ↔ x ⊧ ∼□^[n](∼φ) := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih =>
    constructor;
    . intro h;
      replace h : x ⊧ ◇◇^[n]φ := by simpa using h;
      obtain ⟨y, Rxy, hy⟩ := Satisfies.dia_def.mp h;
      suffices ¬x ⊧ (□□^[n](∼φ)) by simpa;
      apply Satisfies.box_def.not.mpr;
      push_neg;
      use y;
      constructor;
      . exact Rxy;
      . apply Satisfies.not_def.mp;
        apply ih.mp;
        exact hy;
    . intro h;
      replace h : ¬x ⊧ (□□^[n](∼φ)) := by simpa using h;
      suffices x ⊧ ◇◇^[n]φ by simpa;
      apply Satisfies.dia_def.mpr;
      have := Satisfies.box_def.not.mp h;
      push_neg at this;
      obtain ⟨y, Rxy, hy⟩ := this;
      use y;
      constructor;
      . exact Rxy;
      . apply ih.mpr;
        exact Satisfies.not_def.mpr hy;

lemma box_dual : x ⊧ □φ ↔ x ⊧ ∼◇(∼φ) := by simp [Satisfies];

lemma multibox_dual : x ⊧ □^[n]φ ↔ x ⊧ ∼◇^[n](∼φ) := by
  constructor;
  . contrapose;
    intro h;
    exact
      multibox_dn.not.mp
      $ Satisfies.not_def.mp
      $ multidia_dual.mp
      $ negneg_def.mp
      $ Satisfies.not_def.mpr h
  . contrapose;
    intro h;
    apply Satisfies.not_def.mp;
    apply negneg_def.mpr;
    apply multidia_dual.mpr;
    apply Satisfies.not_def.mpr;
    apply multibox_dn.not.mpr;
    exact h;

lemma not_imp : ¬(x ⊧ φ ➝ ψ) ↔ x ⊧ φ ⋏ ∼ψ := by simp [Satisfies];

lemma iff_subst_self {x : F.World} (s : Substitution ℕ) :
  letI U : Kripke.Valuation F := λ w a => Satisfies ⟨F, V⟩ w ((atom a)⟦s⟧);
  Satisfies ⟨F, U⟩ x φ ↔ Satisfies ⟨F, V⟩ x (φ⟦s⟧) := by
  induction φ generalizing x with
  | hatom a => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | hbox φ ih =>
    constructor;
    . intro hbφ y Rxy;
      apply ih.mp;
      exact hbφ y Rxy;
    . intro hbφ y Rxy;
      apply ih.mpr;
      exact hbφ y Rxy;
  | himp φ ψ ihφ ihψ =>
    constructor;
    . intro hφψ hφ;
      apply ihψ.mp;
      apply hφψ;
      apply ihφ.mpr;
      exact hφ;
    . intro hφψs hφ;
      apply ihψ.mpr;
      apply hφψs;
      apply ihφ.mp;
      exact hφ;

end Satisfies


def ValidOnModel (M : Kripke.Model) (φ : Formula ℕ) := ∀ x : M.World, x ⊧ φ

namespace ValidOnModel

instance semantics : Semantics (Formula ℕ) (Kripke.Model) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

@[simp] protected lemma iff_models {M : Kripke.Model} : M ⊧ f ↔ Kripke.ValidOnModel M f := iff_of_eq rfl

variable {M : Kripke.Model} {φ ψ χ : Formula ℕ}

protected lemma bot_def : ¬M ⊧ ⊥ := by simp [Kripke.ValidOnModel];

protected lemma top_def : M ⊧ ⊤ := by simp [Kripke.ValidOnModel];

instance : Semantics.Bot (Kripke.Model) where
  realize_bot := λ _ => ValidOnModel.bot_def;

instance : Semantics.Top (Kripke.Model) where
  realize_top := λ _ => ValidOnModel.top_def;


lemma iff_not_exists_world {M : Kripke.Model} : (¬M ⊧ φ) ↔ (∃ x : M.World, ¬x ⊧ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;

alias ⟨exists_world_of_not, not_of_exists_world⟩ := iff_not_exists_world


protected lemma mdp (hpq : M ⊧ φ ➝ ψ) (hp : M ⊧ φ) : M ⊧ ψ := by
  intro x;
  exact (Satisfies.imp_def.mp $ hpq x) (hp x);

protected lemma nec (h : M ⊧ φ) : M ⊧ □φ := by
  intro x y _;
  exact h y;

lemma multinec (n) (h : M ⊧ φ) : M ⊧ □^[n]φ := by
  induction n with
  | zero => tauto;
  | succ n ih => simpa using ValidOnModel.nec ih;

protected lemma imply₁ : M ⊧ (Axioms.Imply₁ φ ψ) := by simp [ValidOnModel]; tauto;

protected lemma imply₂ : M ⊧ (Axioms.Imply₂ φ ψ χ) := by simp [ValidOnModel]; tauto;

protected lemma elimContra : M ⊧ (Axioms.ElimContra φ ψ) := by simp [ValidOnModel, Satisfies]; tauto;

protected lemma axiomK : M ⊧ (Axioms.K φ ψ)  := by
  intro V;
  apply Satisfies.imp_def.mpr;
  intro hpq;
  apply Satisfies.imp_def.mpr;
  intro hp x Rxy;
  replace hpq := Satisfies.imp_def.mp $ hpq x Rxy;
  replace hp := hp x Rxy;
  exact hpq hp;

end ValidOnModel


def ValidOnFrame (F : Kripke.Frame) (φ : Formula ℕ) := ∀ V, (⟨F, V⟩ : Kripke.Model) ⊧ φ

namespace ValidOnFrame

instance semantics : Semantics (Formula ℕ) (Kripke.Frame) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

variable {F : Kripke.Frame}

@[simp] protected lemma models_iff : F ⊧ φ ↔ Kripke.ValidOnFrame F φ := iff_of_eq rfl

lemma models_set_iff : F ⊧* Φ ↔ ∀ φ ∈ Φ, F ⊧ φ := by simp [Semantics.realizeSet_iff];

protected lemma top_def : F ⊧ ⊤ := by simp [ValidOnFrame];

protected lemma bot_def : ¬F ⊧ ⊥ := by simp [ValidOnFrame];

instance : Semantics.Top (Kripke.Frame) where
  realize_top _ := ValidOnFrame.top_def;

instance : Semantics.Bot (Kripke.Frame) where
  realize_bot _ := ValidOnFrame.bot_def

lemma iff_not_exists_valuation : (¬F ⊧ φ) ↔ (∃ V : Kripke.Valuation F, ¬(⟨F, V⟩ : Kripke.Model) ⊧ φ) := by
  simp [ValidOnFrame];

alias ⟨exists_valuation_of_not, not_of_exists_valuation⟩ := iff_not_exists_valuation

lemma iff_not_exists_valuation_world : (¬F ⊧ φ) ↔ (∃ V : Kripke.Valuation F, ∃ x : (⟨F, V⟩ : Kripke.Model).World, ¬Satisfies _ x φ) := by
  simp [ValidOnFrame, Satisfies, ValidOnModel, Semantics.Realize];

alias ⟨exists_valuation_world_of_not, not_of_exists_valuation_world⟩ := iff_not_exists_valuation_world

lemma iff_not_exists_model_world :  (¬F ⊧ φ) ↔ (∃ M : Kripke.Model, ∃ x : M.World, M.toFrame = F ∧ ¬(x ⊧ φ)) := by
  constructor;
  . intro h;
    obtain ⟨V, x, h⟩ := iff_not_exists_valuation_world.mp h;
    use ⟨F, V⟩, x;
    tauto;
  . rintro ⟨M, x, rfl, h⟩;
    exact iff_not_exists_valuation_world.mpr ⟨M.Val, x, h⟩;

alias ⟨exists_model_world_of_not, not_of_exists_model_world⟩ := iff_not_exists_model_world


protected lemma mdp (hpq : F ⊧ φ ➝ ψ) (hp : F ⊧ φ) : F ⊧ ψ := by
  intro V x;
  exact (hpq V x) (hp V x);

protected lemma nec (h : F ⊧ φ) : F ⊧ □φ := by
  intro V x y _;
  exact h V y;

protected lemma subst (h : F ⊧ φ) : F ⊧ φ⟦s⟧ := by
  by_contra hC;
  replace hC := iff_not_exists_valuation_world.mp hC;
  obtain ⟨V, ⟨x, hx⟩⟩ := hC;
  apply Satisfies.iff_subst_self s |>.not.mpr hx;
  exact h (λ w a => Satisfies ⟨F, V⟩ w (atom a⟦s⟧)) x;

protected lemma imply₁ : F ⊧ (Axioms.Imply₁ φ ψ) := by intro V; exact ValidOnModel.imply₁ (M := ⟨F, V⟩);

protected lemma imply₂ : F ⊧ (Axioms.Imply₂ φ ψ χ) := by intro V; exact ValidOnModel.imply₂ (M := ⟨F, V⟩);

protected lemma elimContra : F ⊧ (Axioms.ElimContra φ ψ) := by intro V; exact ValidOnModel.elimContra (M := ⟨F, V⟩);

protected lemma axiomK : F ⊧ (Axioms.K φ ψ) := by intro V; exact ValidOnModel.axiomK (M := ⟨F, V⟩);

end ValidOnFrame

end Formula.Kripke


namespace Kripke

section

abbrev Frame.logic (F : Frame) : Logic ℕ := { φ | F ⊧ φ }

abbrev FrameClass.logic (C : FrameClass) : Logic ℕ := { φ | C ⊧ φ }

end


section

variable {C : FrameClass} {φ ψ χ : Formula ℕ}

lemma iff_not_validOnFrameClass_exists_frame : (¬C ⊧ φ) ↔ (∃ F ∈ C, ¬F ⊧ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_frame_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_frame⟩ := iff_not_validOnFrameClass_exists_frame

lemma iff_not_validOnFrameClass_exists_model : (¬C ⊧ φ) ↔ (∃ M : Kripke.Model, M.toFrame ∈ C ∧ ¬M ⊧ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_model⟩ := iff_not_validOnFrameClass_exists_model

lemma iff_not_validOnFrameClass_exists_model_world : (¬C ⊧ φ) ↔ (∃ M : Kripke.Model, ∃ x : M.World, M.toFrame ∈ C ∧ ¬(x ⊧ φ)) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_world_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_model_world⟩ := iff_not_validOnFrameClass_exists_model_world

lemma iff_not_validOnFrameClass_exists_valuation_world : (¬C ⊧ φ) ↔ (∃ F ∈ C, ∃ V, ∃ x, ¬(Formula.Kripke.Satisfies ⟨F, V⟩ x φ)) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_valuation_world_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_valuation_world⟩ := iff_not_validOnFrameClass_exists_valuation_world

end


section

open Formula (atom)

namespace FrameClass

variable {C : FrameClass} {Γ : FormulaSet ℕ} {φ ψ χ : Formula ℕ}

lemma validates_with_AxiomK_of_validates (hV : C ⊧* Γ) : C ⊧* (insert (Axioms.K (.atom 0) (.atom 1)) Γ) := by
  constructor;
  rintro φ (rfl | hφ);
  . intro F _;
    apply Formula.Kripke.ValidOnFrame.axiomK;
  . apply hV.realize;
    assumption;

end FrameClass

end

end Kripke

end LO.Modal
