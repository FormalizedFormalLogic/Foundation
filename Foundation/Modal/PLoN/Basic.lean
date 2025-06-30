import Foundation.Modal.Formula

universe u v

namespace LO.Modal

namespace PLoN

structure Frame where
  World : Type
  Rel : Formula ℕ → World → World → Prop
  [World_nonempty : Nonempty World]

noncomputable abbrev Frame.default {F : PLoN.Frame} : F.World := F.World_nonempty.some
scoped notation "﹫" => Frame.default


instance : CoeFun (PLoN.Frame) (λ F => Formula ℕ → F.World → F.World → Prop) := ⟨Frame.Rel⟩

abbrev Frame.Rel' {F : PLoN.Frame} (φ : Formula ℕ) (x y : F.World) := F.Rel φ x y
scoped notation:45 x:90 " ≺[" φ "] " y:90 => Frame.Rel' φ x y


structure FiniteFrame extends Frame where
  [World_finite : Finite World]

instance : Coe (FiniteFrame) (Frame) := ⟨λ F ↦ F.toFrame⟩


abbrev terminalFrame : FiniteFrame where
  World := Unit
  Rel := λ _ _ _ => True


abbrev FrameClass := Set (PLoN.Frame)


abbrev Valuation (F : PLoN.Frame) := F.World → ℕ → Prop

structure Model extends PLoN.Frame where
  Valuation : PLoN.Valuation toFrame

end PLoN



open PLoN

namespace Formula.PLoN

def Satisfies (M : PLoN.Model) (w : M.World) : Formula ℕ → Prop
  | atom a  => M.Valuation w a
  | falsum  => False
  | φ ➝ ψ => (Satisfies M w φ) → (Satisfies M w ψ)
  | □φ   => ∀ {w'}, w ≺[φ] w' → (Satisfies M w' φ)

namespace Satisfies

protected instance semantics (M : PLoN.Model) : Semantics (Formula ℕ) (M.World) := ⟨fun w ↦ Formula.PLoN.Satisfies M w⟩

variable {M : PLoN.Model} {x : M.World} {φ ψ : Formula ℕ}

@[simp] protected lemma iff_models : x ⊧ φ ↔ PLoN.Satisfies M x φ := by rfl

lemma box_def : x ⊧ □φ ↔ ∀ y, x ≺[φ] y → y ⊧ φ := by simp [PLoN.Satisfies];

protected lemma not_def : x ⊧ ∼φ ↔ ¬(x ⊧ φ) := by
  induction φ generalizing x with
  | _ => simp_all [Satisfies];

protected lemma imp_def : x ⊧ φ ➝ ψ ↔ (x ⊧ φ) → (x ⊧ ψ) := by tauto;

protected lemma or_def : x ⊧ φ ⋎ ψ ↔ x ⊧ φ ∨ x ⊧ ψ := by simp [Satisfies]; tauto;

protected lemma and_def : x ⊧ φ ⋏ ψ ↔ x ⊧ φ ∧ x ⊧ ψ := by simp [Satisfies];

protected lemma bot_def : ¬(x ⊧ ⊥) := by simp [Satisfies];

protected lemma top_def : x ⊧ ⊤ := by simp [Satisfies];

instance : Semantics.Tarski M.World where
  realize_top := λ _ => Satisfies.top_def
  realize_bot := λ _ => Satisfies.bot_def
  realize_imp := Satisfies.imp_def
  realize_not := Satisfies.not_def
  realize_and := Satisfies.and_def
  realize_or  := Satisfies.or_def

end Satisfies


def ValidOnModel (M : PLoN.Model) (φ : Formula ℕ) : Prop := ∀ w : M.World, w ⊧ φ

namespace ValidOnModel

instance : Semantics (Formula ℕ) (PLoN.Model) := ⟨fun M ↦ Formula.PLoN.ValidOnModel M⟩

@[simp]
protected lemma iff_models {M : PLoN.Model} {φ : Formula ℕ}
: M ⊧ φ ↔ Formula.PLoN.ValidOnModel M φ := by rfl

instance : Semantics.Bot (PLoN.Model) where
  realize_bot _ := by
    simp [Formula.PLoN.ValidOnModel];
    use ﹫;

variable {M : PLoN.Model}

protected lemma imply₁ : M ⊧ (Axioms.Imply₁ φ ψ) := by simp [ValidOnModel]; tauto;

protected lemma imply₂ : M ⊧ (Axioms.Imply₂ φ ψ χ) := by simp [ValidOnModel]; tauto;

protected lemma elimContra : M ⊧ (Axioms.ElimContra φ ψ) := by simp [ValidOnModel]; tauto;

end ValidOnModel


def ValidOnFrame (F : PLoN.Frame) (φ : Formula ℕ) := ∀ V, (Model.mk F V) ⊧ φ

namespace ValidOnFrame

instance : Semantics (Formula ℕ) (PLoN.Frame) := ⟨fun F ↦ Formula.PLoN.ValidOnFrame F⟩

@[simp]
protected lemma iff_models {F : PLoN.Frame} {φ : Formula ℕ}
: F ⊧ φ ↔ Formula.PLoN.ValidOnFrame F φ := by rfl

variable {F : Frame}

instance : Semantics.Bot (PLoN.Frame) where
  realize_bot _ := by simp [Formula.PLoN.ValidOnFrame];

protected lemma nec (h : F ⊧ φ) : F ⊧ □φ := by
  intro V x y _;
  exact h V y;

protected lemma mdp (hpq : F ⊧ φ ➝ ψ) (hp : F ⊧ φ) : F ⊧ ψ := by
  intro V x;
  exact (hpq V x) (hp V x);

protected lemma imply₁ : F ⊧ (Axioms.Imply₁ φ ψ) := by simp [ValidOnFrame]; tauto;

protected lemma imply₂ : F ⊧ (Axioms.Imply₂ φ ψ χ) := by simp [ValidOnFrame]; tauto;

protected lemma elimContra : F ⊧ (Axioms.ElimContra φ ψ) := by intro V; exact ValidOnModel.elimContra;

end ValidOnFrame


def ValidOnFrameClass (C : PLoN.FrameClass) (φ : Formula ℕ) := ∀ {F}, F ∈ C → F ⊧ φ

namespace ValidOnFrameClass

instance : Semantics (Formula ℕ) (PLoN.FrameClass) := ⟨fun C ↦ Formula.PLoN.ValidOnFrameClass C⟩

variable {C : FrameClass}

@[simp]
protected lemma iff_models {C : PLoN.FrameClass} {φ : Formula ℕ} : C ⊧ φ ↔ Formula.PLoN.ValidOnFrameClass C φ := by rfl

protected lemma nec (h : C ⊧ φ) : C ⊧ □φ := by
  intro _ hF;
  apply PLoN.ValidOnFrame.nec;
  exact h hF;

protected lemma mdp (hpq : C ⊧ φ ➝ ψ) (hp : C ⊧ φ) : C ⊧ ψ := by
  intro _ hF;
  exact PLoN.ValidOnFrame.mdp (hpq hF) (hp hF)

protected lemma imply₁ : C ⊧ (Axioms.Imply₁ φ ψ) := by intro _ _; exact PLoN.ValidOnFrame.imply₁;

protected lemma imply₂ : C ⊧ (Axioms.Imply₂ φ ψ χ) := by intro _ _; exact PLoN.ValidOnFrame.imply₂;

protected lemma elimContra : C ⊧ (Axioms.ElimContra φ ψ) := by intro _ _; exact PLoN.ValidOnFrame.elimContra;


lemma iff_not_exists_frame : (¬C ⊧ φ) ↔ (∃ F ∈ C, ¬F ⊧ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;

alias ⟨exists_frame_of_not, not_of_exists_frame⟩ := iff_not_exists_frame


lemma iff_not_exists_model : (¬C ⊧ φ) ↔ (∃ M : PLoN.Model, M.toFrame ∈ C ∧ ¬M ⊧ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;

alias ⟨exists_model_of_not, not_of_exists_model⟩ := iff_not_exists_model


end ValidOnFrameClass

end Formula.PLoN


namespace PLoN.FrameClass

class DefinedBy (C : PLoN.FrameClass) (Γ : Set (Formula ℕ)) where
  defines : ∀ F, F ∈ C ↔ (∀ φ ∈ Γ, F ⊧ φ)

class IsNonempty (C : PLoN.FrameClass) : Prop where
  nonempty : Nonempty C

end PLoN.FrameClass

/-
namespace PLoN

abbrev AllFrameClass (α) : FrameClass α := Set.univ

lemma AllFrameClass.nonempty : (AllFrameClass.{_, 0} α).Nonempty := by
  use terminalFrame α
  trivial;

open Formula

lemma N_defines : (Hilbert.N).DefinesPLoNFrameClass (AllFrameClass α) := by
  intro F;
  simp [Hilbert.theorems, Entailment.theory, PLoN.ValidOnFrame, PLoN.ValidOnModel];
  intro φ hp;
  induction hp using Hilbert.Deduction.inducition_with_necOnly! with
  | hMaxm h => simp at h;
  | hMdp ihpq ihp =>
    intro V w;
    exact (ihpq V w) (ihp V w)
  | hNec ihp =>
    intro V w w' _;
    exact ihp V w';
  | _ =>
    simp_all [PLoN.Satisfies];
    try tauto;

end PLoN
-/

end LO.Modal
