import Logic.Logic.System
import Logic.Modal.Basic.Formula
import Mathlib.Init.Set

namespace LO

namespace Modal

variable {α β : Type u}

abbrev Context (β : Type u) := Set (Formula β)

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


abbrev Frameclass (α : Type*) := Set (Frame α)

namespace Frameclass

variable (α : Type*)

def Trivial : Frameclass α := Set.univ

@[simp] def Reflexive : Frameclass α := Frame.Reflexive α

@[simp] def Transitive : Frameclass α := Frame.Transitive α

@[simp] def Symmetric : Frameclass α := Frame.Symmetric α

@[simp] def Euclidean : Frameclass α := Frame.Euclidean α

@[simp] def Serial : Frameclass α := Frame.Serial α

@[simp] def Confluency : Frameclass α := Frame.Confluency α

@[simp] def InfiniteAscent : Frameclass α := Frame.InfiniteAscent α

@[simp] def Transitive_and_NotInfiniteAscent : Frameclass α := λ f => f ∈ Transitive α ∧ f ∉ InfiniteAscent α

@[simp] def Density : Frameclass α := Frame.Density α

@[simp] def Functionality : Frameclass α := Frame.Functionality α

@[simp] def RightConvergence : Frameclass α := Frame.RightConvergence α

instance : Nonempty (Frameclass α) := ⟨Trivial α⟩

end Frameclass

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

namespace satisfies

@[simp] lemma atom_def : (w ⊧ˢ[m] atom a) ↔ a ∈ m.val w := by simp [satisfies];

@[simp] lemma top_def : (w ⊧ˢ[m] ⊤) := by simp [satisfies];

@[simp] lemma bot_def : (w ⊧ˢ[m] ⊥) ↔ False := by simp [satisfies];

@[simp] lemma and_def : (w ⊧ˢ[m] p ⋏ q) ↔ (w ⊧ˢ[m] p) ∧ (w ⊧ˢ[m] q) := by simp [satisfies];

-- lemma satisfies_or : (w ⊧ˢ[m] p ⋎ q) ↔ (w ⊧ˢ[m] p) ∨ (w ⊧ˢ[m] q) := by simp [satisfies];

@[simp] lemma imp_def : (w ⊧ˢ[m] p ⟶ q) ↔ (w ⊧ˢ[m] p) → (w ⊧ˢ[m] q) := by simp [satisfies];

@[simp] lemma box_def : (w ⊧ˢ[m] □p) ↔ (∀w', m.rel w w' → (w' ⊧ˢ[m] p)) := by simp [satisfies];
@[simp] lemma dia_def : (w ⊧ˢ[m] ◇p) ↔ (∃w', m.rel w w' ∧ (w' ⊧ˢ[m] p)) := by simp [satisfies];

@[simp] lemma neg_def : (w ⊧ˢ[m] (neg p)) ↔ ¬(w ⊧ˢ[m] p) := by simp [satisfies];
@[simp] lemma neg_def' : (w ⊧ˢ[m] ~p) ↔ ¬(w ⊧ˢ[m] p) := by simp [satisfies];

end satisfies


def models (m : Model α β) (p : Formula β) := ∀w, (w ⊧ˢ[m] p)

notation "⊧ᵐ[" m "] "  p => models m p

namespace models

variable {m : Model α β}

lemma neg_def : (⊧ᵐ[m] (neg p)) →  ¬(⊧ᵐ[m] p) := by
  simp only [models];
  intro w; simp;
  existsi m.nonempty.some;
  apply satisfies.neg_def.mp $ w _;

lemma neg_def' : (⊧ᵐ[m] ~p) →  ¬(⊧ᵐ[m] p) := id neg_def

lemma bot_def : ¬(⊧ᵐ[m] ⊥) := by simp [models]; existsi m.nonempty.some; simp;

lemma preserveModusPonens : (⊧ᵐ[m] p ⟶ q) → (⊧ᵐ[m] p) → (⊧ᵐ[m] q) := by simp_all [models, satisfies.imp_def];

lemma preserveNecessitation : (⊧ᵐ[m] p) → (⊧ᵐ[m] □p) := by simp_all [models, satisfies];

end models


def frames (f : Frame α) (p : Formula β) := ∀v, ⊧ᵐ[⟨f, v⟩] p

notation "⊧ᶠ[" f "] " p => frames f p

namespace frames

variable {f : Frame α}

lemma bot_def : ¬(⊧ᶠ[f] (⊥ : Formula β)) := by simp [frames, models.bot_def];

lemma preserveModusPonens : (⊧ᶠ[f] p ⟶ q) → (⊧ᶠ[f] p) → (⊧ᶠ[f] q) := by simp_all [models, frames, satisfies];

lemma preserveNecessitation : (⊧ᶠ[f] p) → (⊧ᶠ[f] □p) := by simp_all [models, frames, satisfies];

end frames


def frameclasses (fc : Frameclass α) (p : Formula β) := ∀ f, fc f → (⊧ᶠ[f] p)

notation "⊧ᶠᶜ[" fc "] " p => frameclasses fc p

namespace frameclasses

variable {fc : Frameclass α}

lemma preserveModusPonens : (⊧ᶠᶜ[fc] p ⟶ q) → (⊧ᶠᶜ[fc] p) → (⊧ᶠᶜ[fc] q) := by simp_all [frameclasses, frames, models, satisfies.imp_def];

lemma preserveNecessitation : (⊧ᶠᶜ[fc] p) → (⊧ᶠᶜ[fc] □p) := by simp_all [frameclasses, frames, models, satisfies];

end frameclasses

end Formula


namespace Context

@[simp]
def satisfies (m : Model α β) (w : α) (Γ : Context β) := ∀ p ∈ Γ, (w ⊧ˢ[m] p)

notation w " ⊧ˢ[" m "] " Γ => satisfies m w Γ


def models (m : Model α β) (Γ : Context β) := ∀ p ∈ Γ, (⊧ᵐ[m] p)

notation "⊧ᵐ[" m "] " Γ => models m Γ

namespace models

lemma neg_singleton_def {M : Model α β} {p : Formula β} : (⊧ᵐ[M] {~p}) → (¬⊧ᵐ[M] {p}) := by
  intro hnp hp;
  exact Formula.models.neg_def (show  ⊧ᵐ[M] ~p by aesop) (show  ⊧ᵐ[M] p by aesop);

end models

def frames (f : Frame α) (Γ : Context β) := ∀ p ∈ Γ, (⊧ᶠ[f] p)

notation "⊧ᶠ[" f "] " Γ => frames f Γ


def frameclasses (fc : Frameclass α) (Γ : Context β) := ∀ p ∈ Γ, (⊧ᶠᶜ[fc] p)

notation "⊧ᶠᶜ[" fc "] " Γ => frameclasses fc Γ

lemma frameclasses.model {fc : Frameclass α} {M : Model α β} {Γ : Context β} (h : ⊧ᶠᶜ[fc] Γ) : (M.toFrame ∈ fc) → (⊧ᵐ[M] Γ) := by
  intro hm p hp;
  apply h; assumption; assumption;

def ModelSatisfiable (m : Model α β) (Γ : Context β) := ∃ w, w ⊧ˢ[m] Γ

def FrameSatisfiable (f : Frame α) (Γ : Context β) := ∃ V, ModelSatisfiable ⟨f, V⟩ Γ

def FrameclassSatisfiable (fc : Frameclass α) (Γ : Context β) := ∃ f ∈ fc, FrameSatisfiable f Γ

end Context


namespace Formula

@[simp]
def FrameConsequence (f : Frame α) (Γ : Context β) (p : Formula β) := ∀ V w, (w ⊧ˢ[⟨f, V⟩] Γ) → (w ⊧ˢ[⟨f, V⟩] p)

notation Γ " ⊨ᶠ[" f "] " p => FrameConsequence f Γ p

notation Γ " ⊭ᶠ[" f "] " p => ¬(Γ ⊨ᶠ[f] p)

namespace FrameConsequence

variable {f : Frame α} {Γ Γ' : Context β} {p q : Formula β}

lemma preserveAxiomK : (Γ ⊨ᶠ[f] □(p ⟶ q) ⟶ □p ⟶ □q) := by aesop;

lemma preserveWeakening : (Γ ⊆ Γ') → (Γ ⊨ᶠ[f] p) → (Γ' ⊨ᶠ[f] p) := by aesop;

lemma preserveModalPonens : (Γ ⊨ᶠ[f] p ⟶ q) → (Γ ⊨ᶠ[f] p) → (Γ ⊨ᶠ[f] q) := by
  intro h₁ h₂;
  unfold FrameConsequence;
  intro V w hΓ;
  replace h₁ := h₁ V w hΓ;
  replace h₂ := h₂ V w hΓ;
  exact satisfies.imp_def.mp h₁ h₂;

lemma preserveNecessitation : (Γ ⊨ᶠ[f] p) → (Γ ⊨ᶠ[f] □p) := by
  sorry;
  -- simp [FrameConsequence, frames.preserveNecessitation];

end FrameConsequence

@[simp]
def ModelConsequence (m : Model α β) (Γ : Context β) (p : Formula β) := Γ ⊨ᶠ[m.toFrame] p

notation Γ " ⊨ᵐ[" m "] " p => Formula.ModelConsequence m Γ p

lemma ModelConsequence.cast {m : Model α β} {Γ Γ' : Context β} {p : Formula β} : (Γ ⊆ Γ') → (Γ ⊨ᵐ[m] p) → (Γ' ⊨ᵐ[m] p) := by aesop;


@[simp]
def FrameclassConsequence (fc : Frameclass α) (Γ : Context β) (p : Formula β) := ∀ f ∈ fc, Γ ⊨ᶠ[f] p

notation Γ " ⊨ᶠᶜ[" fc "] " p => Formula.FrameclassConsequence fc Γ p

namespace FrameclassConsequence

variable {fc : Frameclass α} {Γ Γ' : Context β} {p : Formula β}

lemma cast {fc : Frameclass α} {Γ Γ' : Context β} {p : Formula β} : (Γ ⊆ Γ') → (Γ ⊨ᶠᶜ[fc] p) → (Γ' ⊨ᶠᶜ[fc] p) := by aesop;

end FrameclassConsequence

end Formula


namespace Context

def ModelConsequence (m : Model α β) (Γ Δ : Context β) := ∀ p ∈ Δ, (Γ ⊨ᵐ[m] p)

notation Γ " ⊨ᵐ[" m "] " Δ => Context.ModelConsequence m Γ Δ


def FrameclassConsequence (fc : Frameclass α) (Γ Δ : Context β) := ∀ p ∈ Δ, (Γ ⊨ᶠᶜ[fc] p)

notation Γ " ⊨ᶠᶜ[" fc "] " Δ => Context.FrameclassConsequence fc Γ Δ

end Context


variable {f : Frame α} {p q : Formula β}

open Formula Frameclass

attribute [simp] Formula.models Formula.frames Formula.frameclasses Formula.satisfies.imp_def Formula.satisfies

lemma frameclasses_AxiomK : ⊧ᶠᶜ[Trivial α] □(p ⟶ q) ⟶ □p ⟶ □q := by aesop;

lemma frameclasses_AxiomT : ⊧ᶠᶜ[Reflexive α] (□p ⟶ p) := by aesop;

lemma frameclasses_AxiomD : ⊧ᶠᶜ[Serial α] (□p ⟶ ◇p) := by aesop;

lemma frameclasses_AxiomB : ⊧ᶠᶜ[Symmetric α] (p ⟶ □◇p) := by aesop;

lemma frameclasses_Axiom4 : ⊧ᶠᶜ[Transitive α] (□p ⟶ □□p) := by aesop;

lemma frameclasses_Axiom5 : ⊧ᶠᶜ[Euclidean α] (◇p ⟶ □◇p) := by aesop;

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
    simp [satisfies.imp_def] at h;
    let V : α → β → Prop := λ _ _ => True;
    have : w₁ ⊧ˢ[⟨f, V⟩] □p := by simp [satisfies]; simp_all;
    have : ¬w₁ ⊧ˢ[⟨f, V⟩] ◇p := by simp [satisfies]; simp_all;
    sorry;
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
