import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Axioms


namespace LO.Modal.Normal

open Formula

variable {α β : Type u} [Inhabited α]

abbrev Frame (α : Type u) := α → α → Prop
abbrev Valuation (α β : Type u) := α → Set β

structure Model (α β : Type u) where
  frame : Frame α
  val : Valuation α β

def trivialVal (α β : Type u) : Valuation α β := λ _ _ => True

namespace Formula

def Satisfies (m : Model α β) (w : α) : Formula β → Prop
  | atom a  => a ∈ m.val w
  | falsum  => False
  | imp p q => (p.Satisfies m w) → (q.Satisfies m w)
  | box p   => ∀w', m.frame w w' → p.Satisfies m w'

notation w " ⊧ᴹˢ[" m "] " p => Satisfies m w p

namespace Satisfies

variable {m : Model α β}

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

@[simp] lemma box_def : (w ⊧ᴹˢ[m] □p) ↔ (∀w', m.frame w w' → (w' ⊧ᴹˢ[m] p)) := by simp [Satisfies];
@[simp] lemma dia_def : (w ⊧ᴹˢ[m] ◇p) ↔ (∃w', m.frame w w' ∧ (w' ⊧ᴹˢ[m] p)) := by simp [Satisfies];

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
  existsi Inhabited.default;
  apply Satisfies.neg_def.mp $ w _;

lemma neg_def' : (⊧ᴹᵐ[m] ~p) →  ¬(⊧ᴹᵐ[m] p) := id neg_def

lemma bot_def : ¬(⊧ᴹᵐ[m] ⊥) := by simp [Models];

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

def ModelSatisfiable (Γ : Context β) := ∃ (M : Model α β), ⊧ᴹᵐ[M] Γ

def Frames (f : Frame α) (Γ : Context β) := ∀ p ∈ Γ, (⊧ᴹᶠ[f] p)

notation "⊧ᴹᶠ[" f "] " Γ => Frames f Γ

lemma frames_union {f : Frame α} {Γ Δ : Context β} : (⊧ᴹᶠ[f] Γ ∪ Δ) ↔ (⊧ᴹᶠ[f] Γ) ∧ (⊧ᴹᶠ[f] Δ) := by
  constructor;
  . intro h; simp_all [Context.Frames];
  . intros h p hp;
    cases hp with
    | inl hp => exact h.left p hp;
    | inr hp => exact h.right p hp;

def FrameSatisfiable (Γ : Context β) := ∃ (f : Frame α), ⊧ᴹᶠ[f] Γ

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
def ModelConsequence (m : Model α β) (Γ : Context β) (p : Formula β) := Γ ⊨ᴹᶠ[m.frame] p

notation Γ " ⊨ᴹᵐ[" m "] " p => Formula.ModelConsequence m Γ p

lemma ModelConsequence.weakening {m : Model α β} {Γ Γ' : Context β} {p : Formula β} : (Γ ⊆ Γ') → (Γ ⊨ᴹᵐ[m] p) → (Γ' ⊨ᴹᵐ[m] p) := by aesop;

end Formula


namespace Context

def ModelConsequence (m : Model α β) (Γ Δ : Context β) := ∀ p ∈ Δ, (Γ ⊨ᴹᵐ[m] p)

notation Γ " ⊨ᴹᵐ[" m "] " Δ => Context.ModelConsequence m Γ Δ


end Context


section Definabilities

attribute [simp] Formula.Frames Formula.Models Context.Models Context.Frames
attribute [simp] AxiomK.ctx AxiomT.ctx AxiomD.ctx AxiomB.ctx Axiom4.ctx Axiom5.ctx

section AxiomDefinabilities

variable (β) {p q : Formula β}

@[simp]
lemma AxiomK.defines : ∀ (f : Frame α), (⊧ᴹᶠ[f] (𝐊 : Context β)) := by aesop;

lemma AxiomT.defines : ∀ (f : Frame α), (Reflexive f) ↔ (⊧ᴹᶠ[f] (𝐓 : Context β)) := by
  intro f;
  constructor;
  . aesop;
  . sorry;

lemma AxiomD.defines  : ∀ (f : Frame α), (Serial f) ↔ (⊧ᴹᶠ[f] (𝐃 : Context β)) := by
  intro f;
  constructor;
  . intro hd p hp V w;
    have ⟨w', hw'⟩ := hd w;
    aesop;
  . intro h; simp only [Context.Frames] at h;
    by_contra hC; simp [Serial] at hC;
    have ⟨w, hw⟩ := hC; clear hC;
    let V : α → β → Prop := λ _ _ => True;
    have : ∀ (p : Formula β), w ⊧ᴹˢ[⟨f, V⟩] □p ⟶ ◇p := by intros; exact h _ (by simp) V w;
    have : ∀ (p : Formula β), w ⊧ᴹˢ[⟨f, V⟩] □p := by simp_all;
    have : ∀ (p : Formula β), ¬w ⊧ᴹˢ[⟨f, V⟩] ◇p := by simp_all;
    aesop;

lemma AxiomB.defines : ∀ (f : Frame α), (Symmetric f) ↔ (⊧ᴹᶠ[f] (𝐁 : Context β)) := by
  intro f;
  constructor;
  . aesop;
  . sorry;

lemma Axiom4.defines : ∀ (f : Frame α), (Transitive f) ↔ (⊧ᴹᶠ[f] (𝟒 : Context β)) := by
  intro f;
  constructor;
  . aesop;
  . sorry;

lemma Axiom5.defines : ∀ (f : Frame α), (Euclidean f) ↔ (⊧ᴹᶠ[f] (𝟓 : Context β)) := by
  intro f;
  constructor;
  . aesop;
  . sorry;

lemma AxiomDot2.defines : ∀ (f : Frame α), (Confluent f) ↔ (⊧ᴹᶠ[f] (.𝟐 : Context β)) := by
  intro f;
  constructor;
  . sorry;
  . sorry;

lemma AxiomDot3.defines : ∀ (f : Frame α), (Functional f) ↔ (⊧ᴹᶠ[f] (.𝟑 : Context β)) := by
  intro f;
  constructor;
  . sorry;
  . sorry;

lemma AxiomCD.defines : ∀ (f : Frame α), (RightConvergent f) ↔ (⊧ᴹᶠ[f] (𝐂𝐃 : Context β)) := by
  intro f;
  constructor;
  . sorry;
  . sorry;

lemma AxiomC4.defines : ∀ (f : Frame α), (Dense f) ↔ (⊧ᴹᶠ[f] (𝐂𝟒 : Context β)) := by
  intro f;
  constructor;
  . sorry;
  . sorry;

lemma AxiomL.defines : ∀ (f : Frame α), (NonInfiniteAscent f) ↔ (⊧ᴹᶠ[f] (𝐋 : Context β)) := by
  intro f;
  constructor;
  . sorry;
  . sorry;

end AxiomDefinabilities

section LogicDefinabilities

attribute [simp] LogicKD LogicKT4

@[simp]
def FrameClass (α β) (Λ : Logic β) : Set (Frame α) := { f : Frame α | ⊧ᴹᶠ[f] Λ }

lemma FrameClass.union (Λ₁ Λ₂ : Logic β) : FrameClass α β (Λ₁ ∪ Λ₂) = FrameClass α β Λ₁ ∩ FrameClass α β Λ₂ := by aesop;

lemma LogicK.def_FrameClass : ∀ f, f ∈ FrameClass α β (𝐊 : Logic β) := by aesop;

lemma LogicKD.def_FrameClass : ∀ f, (Serial f) ↔ (f ∈ FrameClass α β 𝐊𝐃) := by
  intro f;
  constructor;
  . intro hSerial p hp;
    have : ⊧ᴹᶠ[f] (𝐊 : Context β) := (AxiomK.defines β f);
    have : ⊧ᴹᶠ[f] (𝐃 : Context β) := (AxiomD.defines β f).mp hSerial;
    aesop;
  . intro hp; rw [LogicKD, (FrameClass.union 𝐊 𝐃)] at hp;
    apply (AxiomD.defines β f).mpr;
    rcases hp; aesop;

/-
lemma LogicS4.def_FrameClass : ∀ f, (Reflexive f ∧ Transitive f) ↔ (f ∈ FrameClass α β 𝐒𝟒) := by
  intro f;
  constructor;
  . rintro ⟨hRefl, hTrans⟩ p hp;
    have : ⊧ᴹᶠ[f] (𝐊 : Context β) := (AxiomK.defines β f);
    have : ⊧ᴹᶠ[f] (𝐓 : Context β) := (AxiomT.defines β f).mp hRefl;
    have : ⊧ᴹᶠ[f] (𝟒 : Context β) := (Axiom4.defines β f).mp hTrans;
    aesop;
  . intro hp;
    sorry;
-/

end LogicDefinabilities

end Definabilities

end LO.Modal.Normal
