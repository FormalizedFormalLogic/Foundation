import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Axioms
import Logic.Modal.Normal.Logics

namespace LO.Modal.Normal

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
  euclidean := Euclidean f.rel

class Serial where
  serial := Serial f.rel

class Confluent where
  confluent := Confluent f.rel

class NonInfiniteAscent where
  nonInfiniteAscent := NonInfiniteAscent f.rel

class Dense where
  dense := Dense f.rel

class Functional where
  functional := Functional f.rel

class RightConvergent where
  rightConvergent := RightConvergent f.rel

end Frame


structure Frameclass (α : Type*) where
  frames : Set (Frame α)

namespace Frameclass

def Trivial (α) : Frameclass α where
  frames := Set.univ

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
  confluency := ∀ f ∈ fc.frames, Frame.Confluent f

class Density where
  density := ∀ f ∈ fc.frames, Frame.Dense f

class Functionality where
  functionality := ∀ f ∈ fc.frames, Frame.Functional f

class RightConvergence where
  rightConvergence := ∀ f ∈ fc.frames, Frame.RightConvergent f

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

lemma models_neg_singleton {M : Model α β} {p : Formula β} : (⊧ᴹᵐ[M] {~p}) → (¬⊧ᴹᵐ[M] {p}) := by
  intro hnp hp;
  exact Formula.Models.neg_def (show  ⊧ᴹᵐ[M] ~p by aesop) (show  ⊧ᴹᵐ[M] p by aesop);

lemma models_union {M : Model α β} {Γ Δ : Context β} : (⊧ᴹᵐ[M] Γ ∪ Δ) ↔ (⊧ᴹᵐ[M] Γ) ∧ (⊧ᴹᵐ[M] Δ) := by
  constructor;
  . intro h; simp_all [Context.Models];
  . intros h p hp;
    cases hp with
    | inl hp => exact h.left p hp;
    | inr hp => exact h.right p hp;


def Frames (f : Frame α) (Γ : Context β) := ∀ p ∈ Γ, (⊧ᴹᶠ[f] p)

notation "⊧ᴹᶠ[" f "] " Γ => Frames f Γ

lemma frames_union {f : Frame α} {Γ Δ : Context β} : (⊧ᴹᶠ[f] Γ ∪ Δ) ↔ (⊧ᴹᶠ[f] Γ) ∧ (⊧ᴹᶠ[f] Δ) := by
  constructor;
  . intro h; simp_all [Context.Frames];
  . intros h p hp;
    cases hp with
    | inl hp => exact h.left p hp;
    | inr hp => exact h.right p hp;

def Frameclasses (fc : Frameclass α) (Γ : Context β) := ∀ p ∈ Γ, (⊧ᴹᶠᶜ[fc] p)

notation "⊧ᴹᶠᶜ[" fc "] " Γ => Frameclasses fc Γ

lemma Frameclasses.model {fc : Frameclass α} {M : Model α β} {Γ : Context β} (h : ⊧ᴹᶠᶜ[fc] Γ) : (M.toFrame ∈ fc.frames) → (⊧ᴹᵐ[M] Γ) := by
  intro hm p hp;
  apply h; assumption; assumption;

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


section Definabilities

attribute [simp] Formula.Frames Formula.Models Context.Models Context.Frames
attribute [simp] Reflexive Serial Symmetric Transitive Euclidean Confluent NonInfiniteAscent Dense Functional RightConvergent
attribute [simp] AxiomK.ctx AxiomT.ctx AxiomD.ctx AxiomB.ctx Axiom4.ctx Axiom5.ctx

section AxiomDefinabilities

variable (β)

@[simp]
lemma AxiomK.defines : ∀ (f : Frame α), (⊧ᴹᶠ[f] (𝐊 : Context β)) := by aesop;

lemma AxiomT.defines : ∀ (f : Frame α), (Reflexive f.rel) ↔ (⊧ᴹᶠ[f] (𝐓 : Context β)) := by
  intro f;
  constructor;
  . aesop;
  . sorry;

lemma AxiomD.defines  : ∀ (f : Frame α), (Serial f.rel) ↔ (⊧ᴹᶠ[f] (𝐃 : Context β)) := by
  intro f;
  constructor;
  . intro hd p hp V w;
    have ⟨w', hw'⟩ := hd w;
    aesop;
  . intro h; simp only [Context.Frames] at h;
    by_contra hC; simp at hC;
    have ⟨w, hw⟩ := hC; clear hC;
    let V : α → β → Prop := λ _ _ => True;
    have : ∀ (p : Formula β), w ⊧ᴹˢ[⟨f, V⟩] □p ⟶ ◇p := by intros; exact h _ (by simp) V w;
    have : ∀ (p : Formula β), w ⊧ᴹˢ[⟨f, V⟩] □p := by simp_all;
    have : ∀ (p : Formula β), ¬w ⊧ᴹˢ[⟨f, V⟩] ◇p := by simp_all;
    aesop;

lemma AxiomB.defines : ∀ (f : Frame α), (Symmetric f.rel) ↔ (⊧ᴹᶠ[f] (𝐁 : Context β)) := by
  intro f;
  constructor;
  . aesop;
  . sorry;

lemma Axiom4.defines : ∀ (f : Frame α), (Transitive f.rel) ↔ (⊧ᴹᶠ[f] (𝟒 : Context β)) := by
  intro f;
  constructor;
  . aesop;
  . sorry;

lemma Axiom5.defines : ∀ (f : Frame α), (Euclidean f.rel) ↔ (⊧ᴹᶠ[f] (𝟓 : Context β)) := by
  intro f;
  constructor;
  . aesop;
  . sorry;

lemma AxiomDot2.defines : ∀ (f : Frame α), (Confluent f.rel) ↔ (⊧ᴹᶠ[f] (.𝟐 : Context β)) := by
  intro f;
  constructor;
  . sorry;
  . sorry;

lemma AxiomDot3.defines : ∀ (f : Frame α), (Functional f.rel) ↔ (⊧ᴹᶠ[f] (.𝟑 : Context β)) := by
  intro f;
  constructor;
  . sorry;
  . sorry;

lemma AxiomCD.defines : ∀ (f : Frame α), (RightConvergent f.rel) ↔ (⊧ᴹᶠ[f] (𝐂𝐃 : Context β)) := by
  intro f;
  constructor;
  . sorry;
  . sorry;

lemma AxiomC4.defines : ∀ (f : Frame α), (Dense f.rel) ↔ (⊧ᴹᶠ[f] (𝐂𝟒 : Context β)) := by
  intro f;
  constructor;
  . sorry;
  . sorry;

lemma AxiomL.defines : ∀ (f : Frame α), (NonInfiniteAscent f.rel) ↔ (⊧ᴹᶠ[f] (𝐋 : Context β)) := by
  intro f;
  constructor;
  . sorry;
  . sorry;

end AxiomDefinabilities

section LogicDefinabilities

variable (α β) [hα : Inhabited α]

class LogicDefines (Λ : Logic (Formula β)) where
  definability (rel : α → α → Prop) : Prop
  defines : ∀ (f : Frame α), (definability f.rel) ↔ (⊧ᴹᶠ[f] Λ)
  trivial_frame : ∃ (f : Frame α), definability f.rel

attribute [simp] LogicK LogicKD LogicKT4

@[simp, instance]
def LogicK.defines : LogicDefines α β (𝐊 : Logic (Formula β)) where
  definability _ := True
  defines := by intros; aesop;
  trivial_frame := by existsi (⟨hα, (λ _ _ => True)⟩ : Frame α); simp;

lemma LogicDefines_union_K {f : Frame α} (Λ : Logic (Formula β)) {P : (α → α → Prop) → Prop} :
  ((P f.rel ↔ ⊧ᴹᶠ[f] Λ)) → ((P f.rel) ↔ (⊧ᴹᶠ[f] 𝐊 ∪ Λ)) := by
  intro h;
  constructor;
  . intros;
    apply Context.frames_union.mpr;
    aesop;
  . intro hf;
    have := Context.frames_union.mp hf;
    aesop;

@[simp, instance]
def LogicKD.defines : LogicDefines α β (𝐊𝐃 : Logic (Formula β)) where
  definability := Serial
  defines := by
    intro f;
    apply LogicDefines_union_K α β 𝐃;
    exact AxiomD.defines _ f;
  trivial_frame := by existsi (⟨hα, (λ _ _ => True)⟩ : Frame α); simp;

@[simp, instance]
def LogicS4.defines : LogicDefines α β (𝐒𝟒 : Logic (Formula β)) where
  definability f := Symmetric f ∧ Transitive f
  defines := by
    simp only [LogicS4, LogicKT4];
    sorry;
  trivial_frame := by existsi (⟨hα, (λ _ _ => True)⟩ : Frame α); simp;

end LogicDefinabilities

end Definabilities

end LO.Modal.Normal
