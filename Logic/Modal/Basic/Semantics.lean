import Logic.Logic.System
import Logic.Modal.Basic.Formula
import Logic.Modal.Basic.Axioms

section BinaryRels

variable {α : Type u} (rel : α → α → Prop)
local infix:50 " ≺ " => rel

def _root_.Euclidean := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ → w₁ ≺ w₃ → (w₂ ≺ w₃)

def _root_.Serial := ∀w₁, ∃w₂, w₁ ≺ w₂

def _root_.Confluent := ∀ ⦃w₁ w₂ w₃⦄, ((w₁ ≺ w₂ ∧ w₂ ≺ w₃) → ∃ w₄, w₂ ≺ w₄ ∧ w₃ ≺ w₄)

def _root_.NonInfiniteAscent := ¬(∃ (f : ℕ → α), ∀ n, f n ≺ f (n + 1))

def _root_.Dense := ∀ ⦃w₁ w₂⦄, w₁ ≺ w₂ → ∃w₃, w₁ ≺ w₃ ∧ w₃ ≺ w₂

def _root_.Functional := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ ∧ w₁ ≺ w₃ → w₂ = w₃

def _root_.RightConvergent := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ ∧ w₁ ≺ w₃ → w₂ ≺ w₃ ∨ w₃ ≺ w₂ ∨ w₂ = w₃

end BinaryRels


namespace LO

namespace Modal

variable {α β : Type u}

structure Frame (α : Type*) where
  nonempty : Inhabited α
  rel : α → α → Prop

namespace Frame

variable {α : Type u} (f : Frame α)

class Finite where
  finite : Finite α

local infix:50 " ≺ " => f.rel

class Reflexive where
  reflexive := Reflexive f.rel

class Transitive where
  transitive := Transitive f.rel

class Symmetric where
  symmetric := Symmetric f.rel

class Euclidean where
  euclidean := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ → w₁ ≺ w₃ → (w₂ ≺ w₃)

class Serial where
  serial := ∀w₁, ∃w₂, w₁ ≺ w₂

class Confluency where
  confluency := ∀ ⦃w₁ w₂ w₃⦄, ((w₁ ≺ w₂ ∧ w₂ ≺ w₃) → ∃ w₄, w₂ ≺ w₄ ∧ w₃ ≺ w₄)

class NonInfiniteAscent where
  nonInfiniteAscent := ¬(∃ (f : ℕ → α), ∀ n, f n ≺ f (n + 1))

class Density where
  density := ∀ ⦃w₁ w₂⦄, w₁ ≺ w₂ → ∃w₃, w₁ ≺ w₃ ∧ w₃ ≺ w₂

class Functionality where
  functionality := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ ∧ w₁ ≺ w₃ → w₂ = w₃

class RightConvergence where
  rightConvergence := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ ∧ w₁ ≺ w₃ → w₂ ≺ w₃ ∨ w₃ ≺ w₂ ∨ w₂ = w₃

end Frame


structure Frameclass (α : Type*) where
  frames : Set (Frame α)

namespace Frameclass

variable {α : Type u} (fc : Frameclass α)

class Reflexive where
  reflexive := ∀ f ∈ fc.frames, Frame.Reflexive f

class Symmetric where
  symmetric := ∀ f ∈ fc.frames, Frame.Symmetric f

class Transitive where
  transitive := ∀ f ∈ fc.frames, Frame.Transitive f

class Euclidean where
  euclidean := ∀ f ∈ fc.frames, Frame.Euclidean f

class Serial where
  serial := ∀ f ∈ fc.frames, Frame.Serial f

class Confluency where
  confluency := ∀ f ∈ fc.frames, Frame.Confluency f

class Density where
  density := ∀ f ∈ fc.frames, Frame.Density f

class Functionality where
  functionality := ∀ f ∈ fc.frames, Frame.Functionality f

class RightConvergence where
  rightConvergence := ∀ f ∈ fc.frames, Frame.RightConvergence f

end Frameclass


structure Model (α β : Type u) extends Frame α where
  val : α → Set β

def trivialVal (α β : Type u) : α → β → Prop := λ _ _ => True

namespace Formula

def Satisfies (m : Model α β) (w : α) : Formula β → Prop
  | atom a  => a ∈ m.val w
  | falsum  => False
  | imp p q => (p.Satisfies m w) → (q.Satisfies m w)
  | box p   => ∀w', m.rel w w' → p.Satisfies m w'

notation w " ⊧ᴹˢ[" m "] " p => Satisfies m w p

namespace Satisfies

@[simp] lemma atom_def : (w ⊧ᴹˢ[m] atom a) ↔ a ∈ m.val w := by simp [Satisfies];

@[simp] lemma top_def : (w ⊧ᴹˢ[m] ⊤) := by simp [Satisfies];

@[simp] lemma bot_def : (w ⊧ᴹˢ[m] ⊥) ↔ False := by simp [Satisfies];

@[simp] lemma and_def : (w ⊧ᴹˢ[m] p ⋏ q) ↔ (w ⊧ᴹˢ[m] p) ∧ (w ⊧ᴹˢ[m] q) := by simp [Satisfies];

@[simp] lemma or_def : (w ⊧ᴹˢ[m] p ⋎ q) ↔ (w ⊧ᴹˢ[m] p) ∨ (w ⊧ᴹˢ[m] q) := by
  simp [Satisfies];
  constructor;
  . apply Classical.or_iff_not_imp_left.mpr;
  . intros; simp_all [false_or];

@[simp] lemma imp_def : (w ⊧ᴹˢ[m] p ⟶ q) ↔ (w ⊧ᴹˢ[m] p) → (w ⊧ᴹˢ[m] q) := by simp [Satisfies];

@[simp] lemma box_def : (w ⊧ᴹˢ[m] □p) ↔ (∀w', m.rel w w' → (w' ⊧ᴹˢ[m] p)) := by simp [Satisfies];
@[simp] lemma dia_def : (w ⊧ᴹˢ[m] ◇p) ↔ (∃w', m.rel w w' ∧ (w' ⊧ᴹˢ[m] p)) := by simp [Satisfies];

@[simp] lemma neg_def : (w ⊧ᴹˢ[m] (neg p)) ↔ ¬(w ⊧ᴹˢ[m] p) := by simp [Satisfies];
@[simp] lemma neg_def' : (w ⊧ᴹˢ[m] ~p) ↔ ¬(w ⊧ᴹˢ[m] p) := by simp [Satisfies];

end Satisfies


def Models (m : Model α β) (p : Formula β) := ∀w, (w ⊧ᴹˢ[m] p)

notation "⊧ᴹᵐ[" m "] "  p => Models m p

namespace Models

variable {m : Model α β}

lemma neg_def : (⊧ᴹᵐ[m] (neg p)) →  ¬(⊧ᴹᵐ[m] p) := by
  simp only [Models];
  intro w; simp;
  existsi m.nonempty.default;
  apply Satisfies.neg_def.mp $ w _;

lemma neg_def' : (⊧ᴹᵐ[m] ~p) →  ¬(⊧ᴹᵐ[m] p) := id neg_def

lemma bot_def : ¬(⊧ᴹᵐ[m] ⊥) := by simp [Models]; existsi m.nonempty.default; simp;

lemma modus_ponens : (⊧ᴹᵐ[m] p ⟶ q) → (⊧ᴹᵐ[m] p) → (⊧ᴹᵐ[m] q) := by simp_all [Models, Satisfies.imp_def];

lemma necessitation : (⊧ᴹᵐ[m] p) → (⊧ᴹᵐ[m] □p) := by simp_all [Models, Satisfies];

end Models


def Frames (f : Frame α) (p : Formula β) := ∀v, ⊧ᴹᵐ[⟨f, v⟩] p

notation "⊧ᴹᶠ[" f "] " p => Frames f p

namespace Frames

variable {f : Frame α}

lemma bot_def : ¬(⊧ᴹᶠ[f] (⊥ : Formula β)) := by simp [Frames, Models.bot_def];

lemma modus_ponens : (⊧ᴹᶠ[f] p ⟶ q) → (⊧ᴹᶠ[f] p) → (⊧ᴹᶠ[f] q) := by simp_all [Models, Frames, Satisfies];

lemma necessitation : (⊧ᴹᶠ[f] p) → (⊧ᴹᶠ[f] □p) := by simp_all [Models, Frames, Satisfies];

end Frames


def Frameclasses (fc : Frameclass α) (p : Formula β) := ∀ f ∈ fc.frames, (⊧ᴹᶠ[f] p)

notation "⊧ᴹᶠᶜ[" fc "] " p => Frameclasses fc p

namespace Frameclasses

variable {fc : Frameclass α}

lemma modus_ponens : (⊧ᴹᶠᶜ[fc] p ⟶ q) → (⊧ᴹᶠᶜ[fc] p) → (⊧ᴹᶠᶜ[fc] q) := by simp_all [Frameclasses, Frames, Models, Satisfies.imp_def];

lemma necessitation : (⊧ᴹᶠᶜ[fc] p) → (⊧ᴹᶠᶜ[fc] □p) := by simp_all [Frameclasses, Frames, Models, Satisfies];

end Frameclasses

end Formula


namespace Context

@[simp]
def Satisfies (m : Model α β) (w : α) (Γ : Context β) := ∀ p ∈ Γ, (w ⊧ᴹˢ[m] p)

notation w " ⊧ᴹˢ[" m "] " Γ => Satisfies m w Γ


def Models (m : Model α β) (Γ : Context β) := ∀ p ∈ Γ, (⊧ᴹᵐ[m] p)

notation "⊧ᴹᵐ[" m "] " Γ => Models m Γ

namespace Models

lemma neg_singleton_def {M : Model α β} {p : Formula β} : (⊧ᴹᵐ[M] {~p}) → (¬⊧ᴹᵐ[M] {p}) := by
  intro hnp hp;
  exact Formula.Models.neg_def (show  ⊧ᴹᵐ[M] ~p by aesop) (show  ⊧ᴹᵐ[M] p by aesop);

end Models

def Frames (f : Frame α) (Γ : Context β) := ∀ p ∈ Γ, (⊧ᴹᶠ[f] p)

notation "⊧ᴹᶠ[" f "] " Γ => Frames f Γ


def Frameclasses (fc : Frameclass α) (Γ : Context β) := ∀ p ∈ Γ, (⊧ᴹᶠᶜ[fc] p)

notation "⊧ᴹᶠᶜ[" fc "] " Γ => Frameclasses fc Γ

lemma Frameclasses.model {fc : Frameclass α} {M : Model α β} {Γ : Context β} (h : ⊧ᴹᶠᶜ[fc] Γ) : (M.toFrame ∈ fc.frames) → (⊧ᴹᵐ[M] Γ) := by
  intro hm p hp;
  apply h; assumption; assumption;

def defines (P : Frameclass α → Type*) (Γ : Context β) := ∀ fc, P fc → (∀ f, (f ∈ fc.frames) ↔ (⊧ᴹᶠ[f] Γ))

def Defines (fc : Frameclass α) (Γ : Context β) := ∀ f, (f ∈ fc.frames) ↔ (⊧ᴹᶠ[f] Γ)

def ModelSatisfiable (m : Model α β) (Γ : Context β) := ∃ w, w ⊧ᴹˢ[m] Γ

def FrameSatisfiable (f : Frame α) (Γ : Context β) := ∃ V, ModelSatisfiable ⟨f, V⟩ Γ

def FrameclassSatisfiable (fc : Frameclass α) (Γ : Context β) := ∃ f ∈ fc.frames, FrameSatisfiable f Γ

end Context


namespace Formula

@[simp]
def FrameConsequence (f : Frame α) (Γ : Context β) (p : Formula β) := ∀ V w, (w ⊧ᴹˢ[⟨f, V⟩] Γ) → (w ⊧ᴹˢ[⟨f, V⟩] p)

notation Γ " ⊨ᴹᶠ[" f "] " p => FrameConsequence f Γ p

notation Γ " ⊭ᴹᶠ[" f "] " p => ¬(Γ ⊨ᴹᶠ[f] p)

namespace FrameConsequence

variable {f : Frame α} {Γ Γ' : Context β} {p q : Formula β}

lemma def_emptyctx : (∅ ⊨ᴹᶠ[f] p) ↔ (⊧ᴹᶠ[f] p) := by aesop;

lemma axiomK : (Γ ⊨ᴹᶠ[f] AxiomK p q) := by aesop;

lemma weakening : (Γ ⊆ Γ') → (Γ ⊨ᴹᶠ[f] p) → (Γ' ⊨ᴹᶠ[f] p) := by aesop;

lemma modus_ponens : (Γ ⊨ᴹᶠ[f] p ⟶ q) → (Γ ⊨ᴹᶠ[f] p) → (Γ ⊨ᴹᶠ[f] q) := by aesop;

end FrameConsequence

@[simp]
def ModelConsequence (m : Model α β) (Γ : Context β) (p : Formula β) := Γ ⊨ᴹᶠ[m.toFrame] p

notation Γ " ⊨ᴹᵐ[" m "] " p => Formula.ModelConsequence m Γ p

lemma ModelConsequence.weakening {m : Model α β} {Γ Γ' : Context β} {p : Formula β} : (Γ ⊆ Γ') → (Γ ⊨ᴹᵐ[m] p) → (Γ' ⊨ᴹᵐ[m] p) := by aesop;

@[simp]
def FrameclassConsequence (fc : Frameclass α) (Γ : Context β) (p : Formula β) := ∀ f ∈ fc.frames, Γ ⊨ᴹᶠ[f] p

notation Γ " ⊨ᴹᶠᶜ[" fc "] " p => Formula.FrameclassConsequence fc Γ p

notation Γ " ⊭ᴹᶠᶜ[" fc "] " p => ¬(Γ ⊨ᴹᶠᶜ[fc] p)

namespace FrameclassConsequence

variable {fc : Frameclass α} {Γ Γ' : Context β} {p : Formula β}

lemma weakening {fc : Frameclass α} {Γ Γ' : Context β} {p : Formula β} : (Γ ⊆ Γ') → (Γ ⊨ᴹᶠᶜ[fc] p) → (Γ' ⊨ᴹᶠᶜ[fc] p) := by aesop;

end FrameclassConsequence

end Formula


namespace Context

def ModelConsequence (m : Model α β) (Γ Δ : Context β) := ∀ p ∈ Δ, (Γ ⊨ᴹᵐ[m] p)

notation Γ " ⊨ᴹᵐ[" m "] " Δ => Context.ModelConsequence m Γ Δ


def FrameclassConsequence (fc : Frameclass α) (Γ Δ : Context β) := ∀ p ∈ Δ, (Γ ⊨ᴹᶠᶜ[fc] p)

notation Γ " ⊨ᴹᶠᶜ[" fc "] " Δ => Context.FrameclassConsequence fc Γ Δ

end Context


section Defines

attribute [simp] Formula.Frames Formula.Models Context.Models Context.Frames

variable {f : Frame α} {p q q₁ q₂ : Formula β}

lemma AxiomT.ctx.defines : (Reflexive f.rel) ↔ (⊧ᴹᶠ[f] (𝐓 : Context β)) := by
  simp [ctx];
  constructor;
  . aesop;
  . sorry;

lemma AxiomD.ctx.defines : (Serial f.rel) ↔ (⊧ᴹᶠ[f] (𝐃 : Context β)) := by
  simp [ctx];
  constructor;
  . intro hf p V w h; sorry;
  . sorry;
    /-
    intro h;
    by_contra hC; simp at hC;
    have ⟨w₁, r₁⟩ := hC;
    simp [Satisfies.imp_def] at h;
    let V : α → β → Prop := λ _ _ => True;
    have : w₁ ⊧ᴹˢ[⟨f, V⟩] □p := by simp [Satisfies]; simp_all;
    have : ¬w₁ ⊧ᴹˢ[⟨f, V⟩] ◇p := by simp [Satisfies]; simp_all;
    sorry;
    -/

lemma AxiomB.ctx.defines : (Symmetric f.rel) ↔ (⊧ᴹᶠ[f] (𝐁 : Context β)) := by
  simp [ctx];
  constructor;
  . aesop;
  . sorry;

lemma Axiom4.ctx.defines : (Transitive f.rel) ↔ (⊧ᴹᶠ[f] (𝟒 : Context β)) := by
  simp [ctx];
  constructor;
  . aesop;
  . sorry;

lemma Axiom5.ctx.defines : (Euclidean f.rel) ↔ (⊧ᴹᶠ[f] (𝟓 : Context β)) := by
  simp [ctx];
  constructor;
  . aesop;
  . sorry;

lemma AxiomDot2.ctx.defines : (Confluent f.rel) ↔ (⊧ᴹᶠ[f] (.𝟐 : Context β)) := by
  simp [ctx];
  constructor;
  . sorry;
  . sorry;

lemma AxiomDot3.ctx.defines : (Functional f.rel) ↔ (⊧ᴹᶠ[f] (.𝟑 : Context β)) := by
  simp [ctx];
  constructor;
  . sorry;
  . sorry;

lemma AxiomCD.ctx.defines : (RightConvergent f.rel) ↔ (⊧ᴹᶠ[f] (𝐂𝐃 : Context β)) := by
  simp [ctx];
  constructor;
  . sorry;
  . sorry;

lemma AxiomC4.ctx.defines : (Dense f.rel) ↔ (⊧ᴹᶠ[f] (𝐂𝟒 : Context β)) := by
  simp [ctx];
  constructor;
  . sorry;
  . sorry;

end Defines

end Modal

end LO
