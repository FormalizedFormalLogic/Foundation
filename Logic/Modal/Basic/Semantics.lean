import Logic.Logic.System
import Logic.Modal.Basic.Formula

namespace LO

namespace Modal

variable {α β : Type u}

structure Frame (α : Type*) where
  nonempty : Inhabited α
  rel : α → α → Prop

namespace Frame

variable {α : Type u} (f : Frame α)

class Finite extends Frame α where
  finite : Finite α

local infix:50 " ≺ " => f.rel

class Reflexive extends Frame α where
  reflexive := Reflexive f.rel

class Transitive extends Frame α where
  transitive := Transitive f.rel

class Symmetric extends Frame α where
  symmetric := Symmetric f.rel

class Euclidean extends Frame α where
  euclidean := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ → w₁ ≺ w₃ → (w₂ ≺ w₃)

class Serial extends Frame α where
  serial := ∀w₁, ∃w₂, w₁ ≺ w₂

class Confluency extends Frame α where
  confluency := ∀ ⦃w₁ w₂ w₃⦄, ((w₁ ≺ w₂ ∧ w₂ ≺ w₃) → ∃ w₄, w₂ ≺ w₄ ∧ w₃ ≺ w₄)

class NonInfiniteAscent extends Frame α where
  nonInfiniteAscent := ¬(∃ (f : ℕ → α), ∀ n, f n ≺ f (n + 1))

class Density extends Frame α where
  density := ∀ ⦃w₁ w₂⦄, w₁ ≺ w₂ → ∃w₃, w₁ ≺ w₃ ∧ w₃ ≺ w₂

class Functionality extends Frame α where
  functionality := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ ∧ w₁ ≺ w₃ → w₂ = w₃

class RightConvergence extends Frame α where
  rightConvergence := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ ∧ w₁ ≺ w₃ → w₂ ≺ w₃ ∨ w₃ ≺ w₂ ∨ w₂ = w₃

end Frame


structure Frameclass (α : Type*) where
  frames : Set (Frame α)

namespace Frameclass

variable {α : Type u} (fc : Frameclass α)

class Reflexive extends Frameclass α where
  reflexive := ∀ f ∈ fc.frames, Frame.Reflexive f

class Symmetric extends Frameclass α where
  symmetric := ∀ f ∈ fc.frames, Frame.Symmetric f

class Transitive extends Frameclass α where
  transitive := ∀ f ∈ fc.frames, Frame.Transitive f

class Euclidean extends Frameclass α where
  euclidean := ∀ f ∈ fc.frames, Frame.Euclidean f

class Serial extends Frameclass α where
  serial := ∀ f ∈ fc.frames, Frame.Serial f

class Confluency extends Frameclass α where
  confluency := ∀ f ∈ fc.frames, Frame.Confluency f

class Density extends Frameclass α where
  density := ∀ f ∈ fc.frames, Frame.Density f

class Functionality extends Frameclass α where
  functionality := ∀ f ∈ fc.frames, Frame.Functionality f

class RightConvergence extends Frameclass α where
  rightConvergence := ∀ f ∈ fc.frames, Frame.RightConvergence f

end Frameclass


structure Model (α β : Type u) extends Frame α where
  val : α → Set β

def trivialVal (α β : Type u) : α → β → Prop := λ _ _ => True

namespace Formula

def satisfies (m : Model α β) (w : α) : Formula β → Prop
  | atom a  => a ∈ m.val w
  | falsum  => False
  | imp p q => (p.satisfies m w) → (q.satisfies m w)
  | box p   => ∀w', m.rel w w' → p.satisfies m w'

notation w " ⊧ˢ[" m "] " p => satisfies m w p

namespace satisfies

@[simp] lemma atom_def : (w ⊧ˢ[m] atom a) ↔ a ∈ m.val w := by simp [satisfies];

@[simp] lemma top_def : (w ⊧ˢ[m] ⊤) := by simp [satisfies];

@[simp] lemma bot_def : (w ⊧ˢ[m] ⊥) ↔ False := by simp [satisfies];

@[simp] lemma and_def : (w ⊧ˢ[m] p ⋏ q) ↔ (w ⊧ˢ[m] p) ∧ (w ⊧ˢ[m] q) := by simp [satisfies];

@[simp] lemma or_def : (w ⊧ˢ[m] p ⋎ q) ↔ (w ⊧ˢ[m] p) ∨ (w ⊧ˢ[m] q) := by
  simp [satisfies];
  constructor;
  . apply Classical.or_iff_not_imp_left.mpr;
  . intros; simp_all [false_or];

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
  existsi m.nonempty.default;
  apply satisfies.neg_def.mp $ w _;

lemma neg_def' : (⊧ᵐ[m] ~p) →  ¬(⊧ᵐ[m] p) := id neg_def

lemma bot_def : ¬(⊧ᵐ[m] ⊥) := by simp [models]; existsi m.nonempty.default; simp;

lemma preserve_ModusPonens : (⊧ᵐ[m] p ⟶ q) → (⊧ᵐ[m] p) → (⊧ᵐ[m] q) := by simp_all [models, satisfies.imp_def];

lemma preserve_Necessitation : (⊧ᵐ[m] p) → (⊧ᵐ[m] □p) := by simp_all [models, satisfies];

end models


def frames (f : Frame α) (p : Formula β) := ∀v, ⊧ᵐ[⟨f, v⟩] p

notation "⊧ᶠ[" f "] " p => frames f p

namespace frames

variable {f : Frame α}

lemma bot_def : ¬(⊧ᶠ[f] (⊥ : Formula β)) := by simp [frames, models.bot_def];

lemma preserve_ModusPonens : (⊧ᶠ[f] p ⟶ q) → (⊧ᶠ[f] p) → (⊧ᶠ[f] q) := by simp_all [models, frames, satisfies];

lemma preserve_Necessitation : (⊧ᶠ[f] p) → (⊧ᶠ[f] □p) := by simp_all [models, frames, satisfies];

end frames


def frameclasses (fc : Frameclass α) (p : Formula β) := ∀ f ∈ fc.frames, (⊧ᶠ[f] p)

notation "⊧ᶠᶜ[" fc "] " p => frameclasses fc p

namespace frameclasses

variable {fc : Frameclass α}

lemma preserve_ModusPonens : (⊧ᶠᶜ[fc] p ⟶ q) → (⊧ᶠᶜ[fc] p) → (⊧ᶠᶜ[fc] q) := by simp_all [frameclasses, frames, models, satisfies.imp_def];

lemma preserve_Necessitation : (⊧ᶠᶜ[fc] p) → (⊧ᶠᶜ[fc] □p) := by simp_all [frameclasses, frames, models, satisfies];

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

lemma frameclasses.model {fc : Frameclass α} {M : Model α β} {Γ : Context β} (h : ⊧ᶠᶜ[fc] Γ) : (M.toFrame ∈ fc.frames) → (⊧ᵐ[M] Γ) := by
  intro hm p hp;
  apply h; assumption; assumption;

def defines (P : Frameclass α → Type*) (Γ : Context β) := ∀ fc, P fc → (∀ f, (f ∈ fc.frames) ↔ (⊧ᶠ[f] Γ))

def ModelSatisfiable (m : Model α β) (Γ : Context β) := ∃ w, w ⊧ˢ[m] Γ

def FrameSatisfiable (f : Frame α) (Γ : Context β) := ∃ V, ModelSatisfiable ⟨f, V⟩ Γ

def FrameclassSatisfiable (fc : Frameclass α) (Γ : Context β) := ∃ f ∈ fc.frames, FrameSatisfiable f Γ

end Context


namespace Formula

@[simp]
def FrameConsequence (f : Frame α) (Γ : Context β) (p : Formula β) := ∀ V w, (w ⊧ˢ[⟨f, V⟩] Γ) → (w ⊧ˢ[⟨f, V⟩] p)

notation Γ " ⊨ᶠ[" f "] " p => FrameConsequence f Γ p

notation Γ " ⊭ᶠ[" f "] " p => ¬(Γ ⊨ᶠ[f] p)

namespace FrameConsequence

variable {f : Frame α} {Γ Γ' : Context β} {p q : Formula β}

lemma def_emptyctx : (∅ ⊨ᶠ[f] p) ↔ (⊧ᶠ[f] p) := by aesop;

lemma preserve_AxiomK : (Γ ⊨ᶠ[f] □(p ⟶ q) ⟶ □p ⟶ □q) := by aesop;

lemma preserve_Weakening : (Γ ⊆ Γ') → (Γ ⊨ᶠ[f] p) → (Γ' ⊨ᶠ[f] p) := by aesop;

lemma preserve_ModusPonens : (Γ ⊨ᶠ[f] p ⟶ q) → (Γ ⊨ᶠ[f] p) → (Γ ⊨ᶠ[f] q) := by aesop;

end FrameConsequence

@[simp]
def ModelConsequence (m : Model α β) (Γ : Context β) (p : Formula β) := Γ ⊨ᶠ[m.toFrame] p

notation Γ " ⊨ᵐ[" m "] " p => Formula.ModelConsequence m Γ p

lemma ModelConsequence.cast {m : Model α β} {Γ Γ' : Context β} {p : Formula β} : (Γ ⊆ Γ') → (Γ ⊨ᵐ[m] p) → (Γ' ⊨ᵐ[m] p) := by aesop;

@[simp]
def FrameclassConsequence (fc : Frameclass α) (Γ : Context β) (p : Formula β) := ∀ f ∈ fc.frames, Γ ⊨ᶠ[f] p

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


variable {f : Frame α} {p q q₁ q₂ : Formula β}

open Formula Frameclass

attribute [simp] Formula.models Formula.frames Formula.frameclasses Formula.satisfies.imp_def Formula.satisfies
attribute [simp] Context.defines Context.frames

lemma axiomT.defines : (𝐓 : Context β).defines (@Reflexive α) := by
  intro fc hfc f;
  constructor;
  . sorry;
  . sorry;

lemma axiomD.defines : (𝐃 : Context β).defines (@Serial α) := by
  intro fc hfc f;
  constructor;
  . sorry;
    /-
    intro h;
    by_contra hC; simp at hC;
    have ⟨w₁, r₁⟩ := hC;
    simp [satisfies.imp_def] at h;
    let V : α → β → Prop := λ _ _ => True;
    have : w₁ ⊧ˢ[⟨f, V⟩] □p := by simp [satisfies]; simp_all;
    have : ¬w₁ ⊧ˢ[⟨f, V⟩] ◇p := by simp [satisfies]; simp_all;
    sorry;
    -/
  . sorry;

lemma axiomB.defines : (𝐁 : Context β).defines (@Symmetric α) := by
  intro fc hfc f;
  constructor;
  . sorry;
  . sorry;

lemma axiom4.defines : (𝟒 : Context β).defines (@Transitive α) := by
  intro fc hfc f;
  constructor;
  . sorry;
  . sorry;

lemma axiom5.defines : (𝟓 : Context β).defines (@Euclidean α) := by
  intro fc hfc f;
  constructor;
  . sorry;
  . sorry;

lemma axiomDot2.defines : (.𝟐 : Context β).defines (@Confluency α) := by
  intro fc hfc f;
  constructor;
  . sorry;
  . sorry;

lemma axiomDot3.defines : (.𝟑 : Context β).defines (@Functionality α) := by
  intro fc hfc f;
  constructor;
  . sorry;
  . sorry;

lemma axiomCD.defines : (𝐂𝐃 : Context β).defines (@Confluency α) := by
  intro fc hfc f;
  constructor;
  . sorry;
  . sorry;

lemma axiomC4.defines : (𝐂𝟒 : Context β).defines (@Density α) := by
  intro fc hfc f;
  constructor;
  . sorry;
  . sorry;

end Modal

end LO
