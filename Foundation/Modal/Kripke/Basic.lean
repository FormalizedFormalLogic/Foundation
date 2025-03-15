import Foundation.Vorspiel.RelItr
import Foundation.Modal.Axioms
import Foundation.Modal.Formula

namespace LO.Modal

open Entailment


namespace Kripke

structure Frame where
  World : Type
  Rel : Rel World World
  [world_nonempty : Nonempty World]
attribute [simp] Frame.world_nonempty

instance : CoeSort Frame (Type) := ⟨Frame.World⟩
instance : CoeFun Frame (λ F => F.World → F.World → Prop) := ⟨Frame.Rel⟩
instance {F : Frame} : Nonempty F.World := F.world_nonempty

namespace Frame

open Relation

variable {F : Frame} {x y : F.World}

abbrev Rel' (x y : F.World) := F.Rel x y
infix:45 " ≺ " => Frame.Rel'

abbrev RelItr' (n : ℕ) := F.Rel.iterate n
notation x:45 " ≺^[" n "] " y:46 => Frame.RelItr' n x y

@[mk_iff]
class IsFinite (F : Frame) where
  [world_finite : Finite F.World]
attribute [instance] Frame.IsFinite.world_finite


end Frame



section

abbrev whitepoint : Frame := ⟨Unit, λ _ _ => True⟩
instance : Frame.IsFinite whitepoint := ⟨⟩

abbrev blackpoint : Frame := ⟨Unit, λ _ _ => False⟩
instance : Frame.IsFinite blackpoint := ⟨⟩

end


abbrev FrameClass := Set (Frame)


abbrev Valuation (F : Frame) := F.World → ℕ → Prop

structure Model extends Frame where
  Val : Valuation toFrame
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

protected lemma imp_def₂ : x ⊧ φ ➝ ψ ↔ ¬x ⊧ φ ∨ x ⊧ ψ := by tauto;

protected lemma or_def : x ⊧ φ ⋎ ψ ↔ x ⊧ φ ∨ x ⊧ ψ := by simp [Satisfies]; tauto;

protected lemma and_def : x ⊧ φ ⋏ ψ ↔ x ⊧ φ ∧ x ⊧ ψ := by simp [Satisfies];

protected lemma not_def : x ⊧ ∼φ ↔ ¬(x ⊧ φ) := by simp [Satisfies];

protected lemma top_def : x ⊧ ⊤ := by simp [Satisfies];

@[simp] protected lemma box_def : x ⊧ □φ ↔ ∀ y, x ≺ y → y ⊧ φ := by simp [Satisfies];

@[simp] protected lemma dia_def : x ⊧ ◇φ ↔ ∃ y, x ≺ y ∧ y ⊧ φ := by simp [Satisfies];

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
    suffices x ⊧ φ ∨ x ⊧ ⋁Γ ↔ x ⊧ φ ∨ ∃ a ∈ Γ, x ⊧ a by simpa [List.disj₂_cons_nonempty hΓ];
    constructor;
    . rintro (_ | h)
      . tauto;
      . right; exact ih.mp h;
    . rintro (_ | h);
      . tauto;
      . right; exact ih.mpr h;
  | _ => simp;

lemma conj_def : x ⊧ ⋀Γ ↔ ∀ φ ∈ Γ, x ⊧ φ := by
  induction Γ using List.induction_with_singleton with
  | hcons φ Γ hΓ ih =>
    suffices (x ⊧ φ ∧ x ⊧ ⋀Γ) ↔ (x ⊧ φ ∧ ∀ φ ∈ Γ, x ⊧ φ) by simpa [List.conj₂_cons_nonempty hΓ];
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

example {Γ : List _} : (∀ φ ∈ Γ, x ⊧ □φ) → x ⊧ □⋀Γ := by
  intro h y Rxy;
  apply conj_def.mpr;
  intro φ hφ;
  exact h φ hφ y Rxy;

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


lemma intro_neg_equiv (h : x ⊧ φ ↔ x ⊧ ψ) : x ⊧ ∼φ ↔ x ⊧ ∼ψ := by
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
  induction φ using Formula.rec' generalizing x with
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

def Validates (C : FrameClass) (Γ : FormulaSet ℕ) := ∀ F ∈ C, ∀ φ ∈ Γ, F ⊧ φ

abbrev ValidatesFormula (C : FrameClass) (φ : Formula ℕ) := Validates C {φ}

variable {C C₁ C₂ : FrameClass} {Γ Γ₁ Γ₂ : FormulaSet ℕ} {φ φ₁ φ₂ : Formula ℕ}

lemma Validates.inter_of (h₁ : C₁.Validates Γ₁) (h₂ : C₂.Validates Γ₂) : (C₁ ∩ C₂).Validates (Γ₁ ∪ Γ₂) := by
  rintro F;
  rintro ⟨hF₁, hF₂⟩ φ (hφ₁ | hφ₂);
  . exact h₁ F hF₁ _ hφ₁;
  . exact h₂ F hF₂ _ hφ₂;

/-
lemma Validates.sInter_of
  (Ps : Set (FrameClass × FormulaSet ℕ))
  (hPs : ∀ P ∈ Ps, Validates P.1 P.2)
  : Validates (⋂₀ (Ps.image (·.1))) (⋃₀ (Ps.image (·.2))) := by
  rintro F hF φ hφ;
  simp only [Set.sInter_image, Set.mem_iInter, Prod.forall] at hF hφ;
  simp at hPs;
  sorry;
-/

lemma ValidatesFormula.inter_of (h₁ : C₁.ValidatesFormula φ₁) (h₂ : C₂.ValidatesFormula φ₂) : (C₁ ∩ C₂).Validates {φ₁, φ₂}
  := Validates.inter_of h₁ h₂

protected abbrev all : FrameClass := Set.univ

@[simp]
lemma all.IsNonempty : FrameClass.all.Nonempty := by use whitepoint; tauto;

lemma all.validates_axiomK : FrameClass.all.ValidatesFormula (Axioms.K (.atom 0) (.atom 1)) := by
  suffices ∀ (F : Frame), Formula.Kripke.ValidOnFrame F (Axioms.K (.atom 0) (.atom 1)) by simpa [Validates];
  intro F;
  exact Formula.Kripke.ValidOnFrame.axiomK;


protected abbrev finite_all : FrameClass := { F | F.IsFinite }

@[simp]
lemma finite_all.nonempty : FrameClass.finite_all.Nonempty := by use whitepoint; tauto;

lemma finite_all.validates_axiomK : FrameClass.finite_all.ValidatesFormula (Axioms.K (.atom 0) (.atom 1)) := by
  suffices ∀ (F : Frame), F.IsFinite → Formula.Kripke.ValidOnFrame F (Axioms.K (.atom 0) (.atom 1)) by simpa [Validates];
  intro F _;
  apply FrameClass.all.validates_axiomK;
  repeat tauto;

lemma Validates.withAxiomK (hV : C.Validates Γ) : C.Validates (insert (Axioms.K (.atom 0) (.atom 1)) Γ) := by
  convert Validates.inter_of all.validates_axiomK hV;
  tauto_set;

end FrameClass

end

end Kripke

end LO.Modal
