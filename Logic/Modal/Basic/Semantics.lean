import Logic.Logic.System
import Logic.Modal.Basic.Formula
import Mathlib.Init.Set

namespace LO

namespace Modal

variable {α β : Type u}

abbrev Context (β : Type u) := Finset (Formula β)

namespace Context

variable (Γ : Context β)

def Maximal := ∀ p, p ∈ Γ ∨ ¬p ∈ Γ

end Context

structure Frame (α : Type*) where
  nonempty : Nonempty α
  rel : α → α → Prop

namespace Frame

variable (α : Type u) (f : Frame α)

class Finite extends Frame α where
  finite : Finite α

local infix:50 " ≺ " => f.rel

@[simp] def Reflexive := _root_.Reflexive f.rel

@[simp] def Transitive := _root_.Transitive f.rel

@[simp] def Symmetric := _root_.Symmetric f.rel

@[simp] def Euclidean := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ → w₁ ≺ w₃ → (w₂ ≺ w₃)

@[simp] def Serial := ∀w₁, ∃w₂, w₁ ≺ w₂

@[simp] def Confluency := ∀ ⦃w₁ w₂ w₃⦄, ((w₁ ≺ w₂ ∧ w₂ ≺ w₃) → ∃ w₄, w₂ ≺ w₄ ∧ w₃ ≺ w₄)

@[simp] def InfiniteAscent := ∃ (f : ℕ → α), ∀ n, f n ≺ f (n+1)

@[simp] def Density := ∀ ⦃w₁ w₂⦄, w₁ ≺ w₂ → ∃w₃, w₁ ≺ w₃ ∧ w₃ ≺ w₂

@[simp] def Functionality := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ ∧ w₁ ≺ w₃ → w₂ = w₃

@[simp] def RightConvergence := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ ∧ w₁ ≺ w₃ → w₂ ≺ w₃ ∨ w₃ ≺ w₂ ∨ w₂ = w₃

end Frame


abbrev FrameClass (α : Type*) := Set (Frame α)

namespace FrameClass

variable (α : Type*)

def Trivial : FrameClass α := Set.univ

@[simp] def Reflexive : FrameClass α := Frame.Reflexive α

@[simp] def Transitive : FrameClass α := Frame.Transitive α

@[simp] def Symmetric : FrameClass α := Frame.Symmetric α

@[simp] def Euclidean : FrameClass α := Frame.Euclidean α

@[simp] def Serial : FrameClass α := Frame.Serial α

@[simp] def Confluency : FrameClass α := Frame.Confluency α

@[simp] def InfiniteAscent : FrameClass α := Frame.InfiniteAscent α

@[simp] def Transitive_and_NotInfiniteAscent : FrameClass α := λ f => f ∈ Transitive α ∧ f ∉ InfiniteAscent α

@[simp] def Density : FrameClass α := Frame.Density α

@[simp] def Functionality : FrameClass α := Frame.Functionality α

@[simp] def RightConvergence : FrameClass α := Frame.RightConvergence α

end FrameClass


structure Model (α β : Type u) extends Frame α where
  val : α → Set β

def trivialVal (α β : Type u) : α → β → Prop := λ _ _ => True


namespace Formula

def satisfies (m : Model α β) (w : α) : Formula β → Prop
  | atom  a => a ∈ m.val w
  | ⊥       => False
  | p ⟶ q  => (p.satisfies m w) → (q.satisfies m w)
  | □p      => ∀w', m.rel w w' → p.satisfies m w'

notation w " ⊧ˢ[" m "] " p => satisfies m w p

lemma satisfies_atom : (w ⊧ˢ[m] atom a) ↔ a ∈ m.val w := by simp [satisfies];

lemma satisfies_top : (w ⊧ˢ[m] ⊤) := by simp [satisfies];

lemma satisfies_bot : (w ⊧ˢ[m] ⊥) ↔ False := by simp [satisfies];

lemma satisfies_and : (w ⊧ˢ[m] p ⋏ q) ↔ (w ⊧ˢ[m] p) ∧ (w ⊧ˢ[m] q) := by simp [satisfies];

-- lemma satisfies_or : (w ⊧ˢ[m] p ⋎ q) ↔ (w ⊧ˢ[m] p) ∨ (w ⊧ˢ[m] q) := by simp [satisfies];

lemma satisfies_imp : (w ⊧ˢ[m] p ⟶ q) ↔ (w ⊧ˢ[m] p) → (w ⊧ˢ[m] q) := by simp [satisfies];

lemma satisfies_box : (w ⊧ˢ[m] □p) ↔ (∀w', m.rel w w' → (w' ⊧ˢ[m] p)) := by simp [satisfies];
lemma satisfies_dia : (w ⊧ˢ[m] ◇p) ↔ (∃w', m.rel w w' ∧ (w' ⊧ˢ[m] p)) := by simp [satisfies];

lemma satisfies_neg : (w ⊧ˢ[m] (neg p)) ↔ ¬(w ⊧ˢ[m] p) := by simp [satisfies];
lemma satisfies_neg' : (w ⊧ˢ[m] ~p) ↔ ¬(w ⊧ˢ[m] p) := by simp [satisfies];

@[simp]
def models (m : Model α β) (p : Formula β) := ∀w, (w ⊧ˢ[m] p)

notation "⊧ᵐ[" m "] "  p => models m p

lemma models_ModusPonens {m : Model α β} : (⊧ᵐ[m] p ⟶ q) → (⊧ᵐ[m] p) → (⊧ᵐ[m] q) := by simp_all [satisfies_imp];

lemma models_Necessitation {m : Model α β} : (⊧ᵐ[m] p) → (⊧ᵐ[m] □p) := by simp_all [satisfies];

@[simp]
def frames (f : Frame α) (p : Formula β) := ∀v, ⊧ᵐ[⟨f, v⟩] p

notation "⊧ᶠ[" f "] " p => frames f p

variable {f : Frame α}

lemma frames_ModusPonens : (⊧ᶠ[f] p ⟶ q) → (⊧ᶠ[f] p) → (⊧ᶠ[f] q) := by simp_all [satisfies_imp];

lemma frames_Necessitation : (⊧ᶠ[f] p) → (⊧ᶠ[f] □p) := by simp_all [satisfies];


@[simp]
def frameclasses (fc : FrameClass α) (p : Formula β) := ∀ f, fc f → (⊧ᶠ[f] p)

notation "⊧ᶠᶜ[" fc "] " p => frameclasses fc p

variable {fc : FrameClass α}

lemma frameclasses_ModusPonens : (⊧ᶠᶜ[fc] p ⟶ q) → (⊧ᶠᶜ[fc] p) → (⊧ᶠᶜ[fc] q) := by simp_all [satisfies_imp];

lemma frameclasses_Necessitation : (⊧ᶠᶜ[fc] p) → (⊧ᶠᶜ[fc] □p) := by simp_all [satisfies];

end Formula


namespace Context

@[simp]
def satisfies (m : Model α β) (w : α) (Γ : Context β) := ∀ p ∈ Γ, (w ⊧ˢ[m] p)

notation w " ⊧ˢ[" m "] " Γ => satisfies m w Γ


@[simp]
def models (m : Model α β) (Γ : Context β) := ∀ p ∈ Γ, (⊧ᵐ[m] p)

notation "⊧ᵐ[" m "] " Γ => models m Γ

lemma models_singleton_neg {M : Model α β} {p : Formula β} : (⊧ᵐ[M] {~p}) → (¬⊧ᵐ[M] {p}) := by
  intro hnp hp;
  have hp : ⊧ᵐ[M] p := by aesop;
  simp_all [Formula.satisfies_neg'];
  exact hp M.nonempty.some;

@[simp]
def frames (f : Frame α) (Γ : Context β) := ∀ p ∈ Γ, (⊧ᶠ[f] p)

notation "⊧ᶠ[" f "] " Γ => frames f Γ


@[simp]
def frameclasses (fc : FrameClass α) (Γ : Context β) := ∀ p ∈ Γ, (⊧ᶠᶜ[fc] p)

notation "⊧ᶠᶜ[" fc "] " Γ => frameclasses fc Γ

lemma frameclasses_model {fc : FrameClass α} {M : Model α β} {Γ : Context β} (h : ⊧ᶠᶜ[fc] Γ) : (M.toFrame ∈ fc) → (⊧ᵐ[M] Γ) := by aesop;


def frame_satisifiable (f : Frame α) (Γ : Context β) := ∃ V w, w ⊧ˢ[⟨f, V⟩] Γ

def model_satisfiable (m : Model α β) (Γ : Context β) := ∃ w, w ⊧ˢ[m] Γ

def frameclass_satisfiable (fc : FrameClass α) (Γ : Context β) := ∃ f ∈ fc, frame_satisifiable f Γ

end Context


namespace Formula

@[simp]
def model_consequences (m : Model α β) (Γ : Context β) (p : Formula β) := ∀ w, (w ⊧ˢ[m] Γ) → (w ⊧ˢ[m] p)

notation Γ " ⊨ᵐ[" m "] " p => Formula.model_consequences m Γ p

lemma models_consequences_cast {m : Model α β} {Γ Γ' : Context β} {p : Formula β} : (Γ ⊆ Γ') → (Γ ⊨ᵐ[m] p) → (Γ' ⊨ᵐ[m] p) := by aesop;


@[simp]
def frameclass_consequences (fc : FrameClass α) (Γ : Context β) (p : Formula β) := ∀ f ∈ fc, ∀ V, ∀ w, (w ⊧ˢ[⟨f, V⟩] Γ) → (w ⊧ˢ[⟨f, V⟩] p)

notation Γ " ⊨ᶠᶜ[" fc "] " p => Formula.frameclass_consequences fc Γ p

lemma frameclasses_consequences_cast {fc : FrameClass α} {Γ Γ' : Context β} {p : Formula β} : (Γ ⊆ Γ') → (Γ ⊨ᶠᶜ[fc] p) → (Γ' ⊨ᶠᶜ[fc] p) := by aesop;

end Formula


namespace Context

def model_consequences (m : Model α β) (Γ Δ : Context β) := ∀ p ∈ Δ, (Γ ⊨ᵐ[m] p)

notation Γ " ⊨ᵐ[" m "] " Δ => Context.model_consequences m Γ Δ


def frameclass_consequences (fc : FrameClass α) (Γ Δ : Context β) := ∀ p ∈ Δ, (Γ ⊨ᶠᶜ[fc] p)

notation Γ " ⊨ᶠᶜ[" fc "] " Δ => Context.frameclass_consequences fc Γ Δ

end Context


variable {f : Frame α} {p q : Formula β}

open Formula FrameClass

lemma frameclasses_AxiomK : ⊧ᶠᶜ[Trivial α] □(p ⟶ q) ⟶ □p ⟶ □q := by
  simp_all [satisfies_imp, satisfies];

lemma frameclasses_AxiomT : ⊧ᶠᶜ[Reflexive α] (□p ⟶ p) := by
  simp_all [satisfies_imp, satisfies]; aesop;

lemma frameclasses_AxiomD : ⊧ᶠᶜ[Serial α] (□p ⟶ ◇p) := by
  simp_all [satisfies_imp, satisfies];

lemma frameclasses_AxiomB : ⊧ᶠᶜ[Symmetric α] (p ⟶ □◇p) := by
  simp_all [satisfies_imp, satisfies]; aesop;

lemma frameclasses_Axiom4 : ⊧ᶠᶜ[Transitive α] (□p ⟶ □□p) := by
  simp_all [satisfies_imp, satisfies]; aesop;

lemma frameclasses_Axiom5 : ⊧ᶠᶜ[Euclidean α] (◇p ⟶ □◇p) := by
  simp_all [satisfies_imp, satisfies]; aesop;

lemma frameclasses_AxiomL : ⊧ᶠᶜ[Transitive_and_NotInfiniteAscent α] (□(□p ⟶ p) ⟶ □p) := by sorry;

lemma frameclasses_AxiomDot2 : ⊧ᶠᶜ[Confluency α] (◇□p ⟶ □◇p) := by sorry;

lemma frameclasses_AxiomDot3 : ⊧ᶠᶜ[Functionality α] ( □(□p ⟶ □q) ⋎ □(□q ⟶ □p)) := by sorry;

lemma frameclasses_AxiomCD : ⊧ᶠᶜ[Confluency α] (◇p ⟶ □p) := by sorry;

lemma frameclasses_AxiomC4 : ⊧ᶠᶜ[Density α] (□□p ⟶ □p) := by sorry;

lemma defines_T : (⊧ᶠ[f] □p ⟶ p) ↔ (f.Reflexive α) := by
  constructor;
  . sorry;
  . apply frameclasses_AxiomT;

lemma defines_D  : (⊧ᶠ[f] □p ⟶ ◇p) ↔ (f.Serial) := by
  apply Iff.intro;
  . intro h;
    by_contra hC; simp at hC;
    have ⟨w₁, r₁⟩ := hC;
    simp [satisfies_imp] at h;
    let V : α → β → Prop := λ _ _ => True;
    have : w₁ ⊧ˢ[⟨f, V⟩] □p := by simp [satisfies]; simp_all;
    have : ¬w₁ ⊧ˢ[⟨f, V⟩] ◇p := by simp [satisfies]; simp_all;
    aesop;
  . apply frameclasses_AxiomD;

lemma defines_B : (⊧ᶠ[f] p ⟶ □◇p) ↔ (f.Symmetric) := by
  constructor;
  . sorry;
  . apply frameclasses_AxiomB;

lemma defines_A4 : (⊧ᶠ[f] □p ⟶ □□p) ↔ (f.Transitive) := by
  constructor;
  . sorry;
  . apply frameclasses_Axiom4;

lemma defines_A5 : (⊧ᶠ[f] ◇p ⟶ □◇p) ↔ (f.Euclidean) := by
  constructor;
  . sorry;
  . apply frameclasses_Axiom5;

lemma defines_L : (⊧ᶠ[f] □(□p ⟶ p) ⟶ □p) ↔ (f.Transitive ∧ ¬f.InfiniteAscent) := by
  constructor;
  . sorry;
  . apply frameclasses_AxiomL;

lemma defines_Dot2 : (⊧ᶠ[f] ◇□p ⟶ □◇p) ↔ (f.Confluency) := by
  constructor;
  . sorry;
  . apply frameclasses_AxiomDot2;

end Modal

end LO
