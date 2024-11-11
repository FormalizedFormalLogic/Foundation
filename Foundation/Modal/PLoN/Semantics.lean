import Foundation.Modal.Hilbert

universe u v

namespace LO.Modal

namespace PLoN

structure Frame (α) where
  World : Type*
  [World_nonempty : Nonempty World]
  Rel : Formula α → World → World → Prop

noncomputable abbrev Frame.default {F : PLoN.Frame α} : F.World := F.World_nonempty.some
scoped notation "﹫" => Frame.default


instance : CoeFun (PLoN.Frame α) (λ F => Formula α → F.World → F.World → Prop) := ⟨Frame.Rel⟩

abbrev Frame.Rel' {F : PLoN.Frame α} (φ : Formula α) (x y : F.World) := F.Rel φ x y
scoped notation:45 x:90 " ≺[" φ "] " y:90 => Frame.Rel' φ x y


structure FiniteFrame (α) extends Frame α where
  [World_finite : Finite World]

instance : Coe (FiniteFrame α) (Frame α) := ⟨λ F ↦ F.toFrame⟩


abbrev terminalFrame (α) : FiniteFrame α where
  World := Unit
  Rel := λ _ _ _ => True


abbrev FrameClass (α : Type*) := Set (PLoN.Frame α)


abbrev Valuation (F : PLoN.Frame α) (α : Type*) := F.World → α → Prop

structure Model (α) where
  Frame : PLoN.Frame α
  Valuation : PLoN.Valuation Frame α

abbrev Model.World (M : PLoN.Model) := M.Frame.World
instance : CoeSort (PLoN.Model) (Type _) := ⟨Model.World⟩

end PLoN

variable {α : Type*}

open PLoN

def Formula.PLoN.Satisfies (M : PLoN.Model) (w : M.World) : Formula α → Prop
  | atom a  => M.Valuation w a
  | falsum  => False
  | φ ➝ ψ => (PLoN.Satisfies M w φ) → (PLoN.Satisfies M w ψ)
  | □φ   => ∀ {w'}, w ≺[φ] w' → (PLoN.Satisfies M w' φ)


namespace Formula.PLoN.Satisfies

protected instance semantics (M : PLoN.Model) : Semantics (Formula α) (M.World) := ⟨fun w ↦ Formula.PLoN.Satisfies M w⟩

variable {M : PLoN.Model} {x : M.World} {φ ψ : Formula α}

@[simp] protected lemma iff_models : x ⊧ φ ↔ PLoN.Satisfies M x φ := by rfl

lemma box_def : x ⊧ □φ ↔ ∀ y, x ≺[φ] y → y ⊧ φ := by simp [PLoN.Satisfies];

lemma not_def : x ⊧ ∼φ ↔ ¬(x ⊧ φ) := by
  induction φ using Formula.rec' generalizing x with
  | _ => simp_all [Satisfies];
instance : Semantics.Not (M.World) := ⟨not_def⟩

lemma imp_def : x ⊧ φ ➝ ψ ↔ (x ⊧ φ) → (x ⊧ ψ) := by tauto;
instance : Semantics.Imp (M.World) := ⟨imp_def⟩

lemma or_def : x ⊧ φ ⋎ ψ ↔ x ⊧ φ ∨ x ⊧ ψ := by simp [Satisfies]; tauto;
instance : Semantics.Or (M.World) := ⟨or_def⟩

lemma and_def : x ⊧ φ ⋏ ψ ↔ x ⊧ φ ∧ x ⊧ ψ := by simp [Satisfies];
instance : Semantics.And (M.World) := ⟨and_def⟩

instance : Semantics.Tarski M.World where
  realize_top := by simp [PLoN.Satisfies];
  realize_bot := by simp [PLoN.Satisfies];

end Formula.PLoN.Satisfies


def Formula.PLoN.ValidOnModel (M : PLoN.Model) (φ : Formula α) : Prop := ∀ w : M.World, w ⊧ φ

namespace Formula.PLoN.ValidOnModel

instance : Semantics (Formula α) (PLoN.Model) := ⟨fun M ↦ Formula.PLoN.ValidOnModel M⟩

@[simp]
protected lemma iff_models {M : PLoN.Model} {φ : Formula α}
: M ⊧ φ ↔ Formula.PLoN.ValidOnModel M φ := by rfl

instance : Semantics.Bot (PLoN.Model) where
  realize_bot _ := by
    simp [Formula.PLoN.ValidOnModel];
    use ﹫;

variable {M : PLoN.Model}

protected lemma imply₁ : M ⊧ (Axioms.Imply₁ φ ψ) := by simp [ValidOnModel]; tauto;

protected lemma imply₂ : M ⊧ (Axioms.Imply₂ φ ψ χ) := by simp [ValidOnModel]; tauto;

protected lemma elim_contra : M ⊧ (Axioms.ElimContra φ ψ) := by simp [ValidOnModel]; tauto;

end Formula.PLoN.ValidOnModel


def Formula.PLoN.ValidOnFrame (F : PLoN.Frame α) (φ : Formula α) := ∀ V, (Model.mk F V) ⊧ φ

namespace Formula.PLoN.ValidOnFrame

instance : Semantics (Formula α) (PLoN.Frame α) := ⟨fun F ↦ Formula.PLoN.ValidOnFrame F⟩

@[simp]
protected lemma iff_models {F : PLoN.Frame α} {φ : Formula α}
: F ⊧ φ ↔ Formula.PLoN.ValidOnFrame F φ := by rfl

variable {F : Frame α}

instance : Semantics.Bot (PLoN.Frame α) where
  realize_bot _ := by simp [Formula.PLoN.ValidOnFrame];

protected lemma nec (h : F ⊧ φ) : F ⊧ □φ := by
  intro V x y _;
  exact h V y;

protected lemma mdp (hpq : F ⊧ φ ➝ ψ) (hp : F ⊧ φ) : F ⊧ ψ := by
  intro V x;
  exact (hpq V x) (hp V x);

protected lemma imply₁ : F ⊧ (Axioms.Imply₁ φ ψ) := by simp [ValidOnFrame]; tauto;

protected lemma imply₂ : F ⊧ (Axioms.Imply₂ φ ψ χ) := by simp [ValidOnFrame]; tauto;

protected lemma elim_contra : F ⊧ (Axioms.ElimContra φ ψ) := by intro V; exact ValidOnModel.elim_contra;

end Formula.PLoN.ValidOnFrame


def Formula.PLoN.ValidOnFrameClass (𝔽 : PLoN.FrameClass α) (φ : Formula α) := ∀ {F}, F ∈ 𝔽 → F ⊧ φ

namespace Formula.PLoN.ValidOnFrameClass

instance : Semantics (Formula α) (PLoN.FrameClass α) := ⟨fun 𝔽 ↦ Formula.PLoN.ValidOnFrameClass 𝔽⟩

variable {𝔽 : FrameClass α}

@[simp]
protected lemma iff_models {𝔽 : PLoN.FrameClass α} {φ : Formula α} : 𝔽 ⊧ φ ↔ Formula.PLoN.ValidOnFrameClass 𝔽 φ := by rfl

protected lemma nec (h : 𝔽 ⊧ φ) : 𝔽 ⊧ □φ := by
  intro _ hF;
  apply PLoN.ValidOnFrame.nec;
  exact h hF;

protected lemma mdp (hpq : 𝔽 ⊧ φ ➝ ψ) (hp : 𝔽 ⊧ φ) : 𝔽 ⊧ ψ := by
  intro _ hF;
  exact PLoN.ValidOnFrame.mdp (hpq hF) (hp hF)

protected lemma imply₁ : 𝔽 ⊧ (Axioms.Imply₁ φ ψ) := by intro _ _; exact PLoN.ValidOnFrame.imply₁;

protected lemma imply₂ : 𝔽 ⊧ (Axioms.Imply₂ φ ψ χ) := by intro _ _; exact PLoN.ValidOnFrame.imply₂;

protected lemma elim_contra : 𝔽 ⊧ (Axioms.ElimContra φ ψ) := by intro _ _; exact PLoN.ValidOnFrame.elim_contra;

end Formula.PLoN.ValidOnFrameClass


def Hilbert.DefinesPLoNFrameClass (H : Hilbert α) (𝔽 : PLoN.FrameClass α) := ∀ {F : Frame α}, F ⊧* H.theorems ↔ F ∈ 𝔽

namespace PLoN


abbrev AllFrameClass (α) : FrameClass α := Set.univ

lemma AllFrameClass.nonempty : (AllFrameClass.{_, 0} α).Nonempty := by
  use terminalFrame α
  trivial;

open Formula

lemma N_defines : (Hilbert.N α).DefinesPLoNFrameClass (AllFrameClass α) := by
  intro F;
  simp [Hilbert.theorems, System.theory, PLoN.ValidOnFrame, PLoN.ValidOnModel];
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

end LO.Modal
