import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Axioms

namespace LO.Modal.Normal

open Formula

variable {α β : Type u} [Inhabited α]

abbrev Frame (α : Type u) := α → α → Prop
abbrev Valuation (α β : Type u) := α → β → Prop

structure Model (α β : Type u) where
  frame : Frame α
  val : Valuation α β

namespace Formula

def Satisfies (M : Model α β) (w : α) : Formula β → Prop
  | atom a  => M.val w a
  | falsum  => False
  | and p q => (p.Satisfies M w) ∧ (q.Satisfies M w)
  | or p q  => (p.Satisfies M w) ∨ (q.Satisfies M w)
  | imp p q => ¬(p.Satisfies M w) ∨ (q.Satisfies M w)
  | box p   => ∀w', M.frame w w' → p.Satisfies M w'

notation w " ⊩ᴹ[" M "] " p => Satisfies M w p

@[simp] abbrev Unsatisfies (M : Model α β) (w : α) (p : Formula β) := ¬(w ⊩ᴹ[M] p)
notation w " ⊮ᴹ[" M "] " p => Unsatisfies M w p

namespace Satisfies

variable {M : Model α β}

@[simp] lemma atom_def : (w ⊩ᴹ[M] atom a) ↔ M.val w a := by simp [Satisfies];

@[simp] lemma top_def : (w ⊩ᴹ[M] ⊤) := by simp [Satisfies];

@[simp] lemma bot_def : (w ⊩ᴹ[M] ⊥) ↔ False := by simp [Satisfies];

@[simp] lemma and_def : (w ⊩ᴹ[M] p ⋏ q) ↔ (w ⊩ᴹ[M] p) ∧ (w ⊩ᴹ[M] q) := by simp [Satisfies];

@[simp] lemma or_def : (w ⊩ᴹ[M] p ⋎ q) ↔ (w ⊩ᴹ[M] p) ∨ (w ⊩ᴹ[M] q) := by simp [Satisfies];

lemma imp_def : (w ⊩ᴹ[M] p ⟶ q) ↔ (w ⊮ᴹ[M] p) ∨ (w ⊩ᴹ[M] q) := by simp [Satisfies];
@[simp] lemma imp_def' : (w ⊩ᴹ[M] p ⟶ q) ↔ (w ⊩ᴹ[M] p) → (w ⊩ᴹ[M] q) := by simp [Satisfies, imp_iff_not_or];

@[simp] lemma box_def : (w ⊩ᴹ[M] □p) ↔ (∀w', M.frame w w' → (w' ⊩ᴹ[M] p)) := by simp [Satisfies];
@[simp] lemma dia_def : (w ⊩ᴹ[M] ◇p) ↔ (∃w', M.frame w w' ∧ (w' ⊩ᴹ[M] p)) := by simp [Satisfies];

@[simp] lemma neg_def : (w ⊩ᴹ[M] (neg p)) ↔ (w ⊮ᴹ[M] p) := by simp [Satisfies];
@[simp] lemma neg_def' : (w ⊩ᴹ[M] ~p) ↔ (w ⊮ᴹ[M] p) := by simp [Satisfies];

lemma modus_ponens (m₁ : w ⊩ᴹ[M] p ⟶ q) : (w ⊩ᴹ[M] p) → (w ⊩ᴹ[M] q) := by simpa [imp_def'] using m₁;

end Satisfies

def Models (M : Model α β) (p : Formula β) := ∀w, (w ⊩ᴹ[M] p)
notation "⊧ᴹ[" M "] "  p => Models M p

namespace Models

variable {M : Model α β}

@[simp] lemma neg_def : (⊧ᴹ[M] (~p)) → ¬(⊧ᴹ[M] p) := by
  simp [Models];
  intro h;
  existsi default;
  exact h default;

@[simp] lemma bot_def : ¬(⊧ᴹ[M] ⊥) := by simp [Models];

lemma modus_ponens : (⊧ᴹ[M] p ⟶ q) → (⊧ᴹ[M] p) → (⊧ᴹ[M] q) := by simp_all [Models];

lemma necessitation : (⊧ᴹ[M] p) → (⊧ᴹ[M] □p) := by simp_all [Models, Satisfies];

lemma imply₁ : ⊧ᴹ[M] p ⟶ q ⟶ p := by simp_all [Models];

lemma imply₂ : ⊧ᴹ[M] (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r := by simp_all [Models];

lemma conj₁ : ⊧ᴹ[M] p ⋏ q ⟶ p := by simp_all [Models];

lemma conj₂ : ⊧ᴹ[M] p ⋏ q ⟶ q := by simp_all [Models];

lemma conj₃ : ⊧ᴹ[M] p ⟶ q ⟶ p ⋏ q := by simp_all [Models];

lemma disj₁ : ⊧ᴹ[M] p ⟶ p ⋎ q := by simp_all [Models];

lemma disj₂ : ⊧ᴹ[M] q ⟶ p ⋎ q := by simp_all [Models];

lemma disj₃ : ⊧ᴹ[M] (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r := by simp_all [Models]; aesop;

lemma dne : ⊧ᴹ[M] ~~p ⟶ p := by simp_all [Models];

lemma verum : ⊧ᴹ[M] ⊤ := by simp [Models];

end Models


def Frames (F: Frame α) (p : Formula β) := ∀ V, ⊧ᴹ[⟨F, V⟩] p

notation "⊧ᴹ[" f "] " p => Frames f p

namespace Frames

variable {F: Frame α}

@[simp] lemma bot_def : ¬(⊧ᴹ[F] (⊥ : Formula β)) := by simp [Frames];

lemma modus_ponens : (⊧ᴹ[F] p ⟶ q) → (⊧ᴹ[F] p) → (⊧ᴹ[F] q) := by
  intro h₁ h₂ V;
  exact Models.modus_ponens (h₁ V) (h₂ V);

lemma necessitation : (⊧ᴹ[F] p) → (⊧ᴹ[F] □p) := by
  intro h V;
  exact Models.necessitation (h V);

lemma verum : ⊧ᴹ[F] (⊤ : Formula β) := by simp only [Frames, Models.verum, forall_const];

lemma imply₁ : ⊧ᴹ[F] p ⟶ q ⟶ p := by simp only [Frames, Models.imply₁, forall_const];

lemma imply₂ : ⊧ᴹ[F] (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r := by simp only [Frames, Models.imply₂, forall_const];

lemma conj₁ : ⊧ᴹ[F] p ⋏ q ⟶ p := by simp only [Frames, Models.conj₁, forall_const];

lemma conj₂ : ⊧ᴹ[F] p ⋏ q ⟶ q := by simp only [Frames, Models.conj₂, forall_const];

lemma conj₃ : ⊧ᴹ[F] p ⟶ q ⟶ p ⋏ q := by simp only [Frames, Models.conj₃, forall_const];

lemma disj₁ : ⊧ᴹ[F] p ⟶ p ⋎ q := by simp only [Frames, Models.disj₁, forall_const];

lemma disj₂ : ⊧ᴹ[F] q ⟶ p ⋎ q := by simp only [Frames, Models.disj₂, forall_const];

lemma disj₃ : ⊧ᴹ[F] (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r := by simp only [Frames, Models.disj₃, forall_const];

lemma dne : ⊧ᴹ[F] ~~p ⟶ p := by simp only [Frames, Models.dne, forall_const];

end Frames

lemma not_Frames : (∃ V w, (w ⊮ᴹ[⟨F, V⟩] p)) → ¬(⊧ᴹ[F] p) := by
  simp;
  intro V w hw hf;
  exact hw $ hf V w;

end Formula


@[simp] def Theory.Satisfies (M : Model α β) (w : α) (Γ : Theory β) := ∀ p ∈ Γ, w ⊩ᴹ[M] p
notation w "⊩ᴹ[" M "] " Γ => Theory.Satisfies M w Γ

@[simp] abbrev Theory.Unsatisfies (M : Model α β) (w : α) (Γ : Theory β) := ¬(w ⊩ᴹ[M] Γ)
notation w "⊮ᴹ[" M "] " Γ => Theory.Unsatisfies M w Γ

variable [DecidableEq β]

@[simp]
def Theory.Models (M : Model α β) (Γ : Theory β) := ∀ p ∈ Γ, ⊧ᴹ[M] p
notation "⊧ᴹ[" M "] " Γ => Theory.Models M Γ

@[simp]
def Theory.Frames (F : Frame α) (Γ : Theory β) := ∀ p ∈ Γ, ⊧ᴹ[F] p
notation "⊧ᴹ[" F "] " Γ => Theory.Frames F Γ

abbrev FrameClass (α : Type u) := Set (Frame α)

def Formula.FrameClasses (𝔽 : FrameClass α) (p : Formula β) := ∀ F ∈ 𝔽, ⊧ᴹ[F] p
notation "⊧ᴹ[" 𝔽 "] " p => Formula.FrameClasses 𝔽 p

namespace Formula.FrameClasses

variable {𝔽 : FrameClass α} {p q : Formula β}

lemma modus_ponens : (⊧ᴹ[𝔽] p ⟶ q) → (⊧ᴹ[𝔽] p) → (⊧ᴹ[𝔽] q) := by
  intro h₁ h₂ F hF;
  exact Frames.modus_ponens (h₁ F hF) (h₂ F hF);

lemma necessitation : (⊧ᴹ[𝔽] p) → (⊧ᴹ[𝔽] □p) := by
  intro h F hF;
  exact Frames.necessitation (h F hF);

lemma verum : ⊧ᴹ[𝔽] (⊤ : Formula β) := by simp [FrameClasses, Frames.verum];

lemma imply₁ : ⊧ᴹ[𝔽] p ⟶ q ⟶ p := by simp [FrameClasses, Frames.imply₁];

lemma imply₂ : ⊧ᴹ[𝔽] (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r := by simp [FrameClasses, Frames.imply₂];

lemma conj₁ : ⊧ᴹ[𝔽] p ⋏ q ⟶ p := by simp [FrameClasses, Frames.conj₁];

lemma conj₂ : ⊧ᴹ[𝔽] p ⋏ q ⟶ q := by simp [FrameClasses, Frames.conj₂];

lemma conj₃ : ⊧ᴹ[𝔽] p ⟶ q ⟶ p ⋏ q := by simp [FrameClasses, Frames.conj₃];

lemma disj₁ : ⊧ᴹ[𝔽] p ⟶ p ⋎ q := by simp [FrameClasses, Frames.disj₁];

lemma disj₂ : ⊧ᴹ[𝔽] q ⟶ p ⋎ q := by simp [FrameClasses, Frames.disj₂];

lemma disj₃ : ⊧ᴹ[𝔽] (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r := by simp [FrameClasses, Frames.disj₃];

lemma dne : ⊧ᴹ[𝔽] ~~p ⟶ p := by simp only [FrameClasses, Frames.dne, implies_true, forall_const];

end Formula.FrameClasses

@[simp]
def Theory.FrameClasses (𝔽 : FrameClass α) (Γ : Theory β) := ∀ p ∈ Γ, ⊧ᴹ[𝔽] p
notation "⊧ᴹ[" 𝔽 "] " Γ => Theory.FrameClasses 𝔽 Γ

@[simp]
def AxiomSetFrameClass (Λ : AxiomSet β) : FrameClass α := { F | ⊧ᴹ[F] Λ }
notation "𝔽(" Λ ")" => AxiomSetFrameClass Λ

namespace AxiomSetFrameClass

lemma union (Λ₁ Λ₂ : AxiomSet β) : (𝔽(Λ₁ ∪ Λ₂) : FrameClass α) = 𝔽(Λ₁) ∩ 𝔽(Λ₂) := by aesop;

lemma triunion (Λ₁ Λ₂ Λ₃ : AxiomSet β) : (𝔽(Λ₁ ∪ Λ₂ ∪ Λ₃) : FrameClass α) = 𝔽(Λ₁) ∩ 𝔽(Λ₂) ∩ 𝔽(Λ₃) := by aesop;

lemma tetraunion (Λ₁ Λ₂ Λ₃ Λ₄ : AxiomSet β) : (𝔽(Λ₁ ∪ Λ₂ ∪ Λ₃ ∪ Λ₄) : FrameClass α) = 𝔽(Λ₁) ∩ 𝔽(Λ₂) ∩ 𝔽(Λ₃) ∩ 𝔽(Λ₄) := by aesop;

lemma pentaunion (Λ₁ Λ₂ Λ₃ Λ₄ Λ₅ : AxiomSet β) : (𝔽(Λ₁ ∪ Λ₂ ∪ Λ₃ ∪ Λ₄ ∪ Λ₅) : FrameClass α) = 𝔽(Λ₁) ∩ 𝔽(Λ₂) ∩ 𝔽(Λ₃) ∩ 𝔽(Λ₄) ∩ 𝔽(Λ₅) := by aesop;

end AxiomSetFrameClass

namespace Theory

lemma models_neg_singleton {M : Model α β} {p : Formula β} : (⊧ᴹ[M] {~p}) → (¬⊧ᴹ[M] {p}) := by
  intro hnp hp;
  exact Formula.Models.neg_def (hnp (~p) (by simp)) (hp p (by simp));

lemma models_union {M : Model α β} {Γ₁ Γ₂ : Theory β} : (⊧ᴹ[M] Γ₁ ∪ Γ₂) ↔ (⊧ᴹ[M] Γ₁) ∧ (⊧ᴹ[M] Γ₂) := by
  constructor;
  . intro h; simp_all [Theory.Models];
  . intros h p hp;
    rcases hp with (_ | _);
    . exact h.left p (by assumption);
    . exact h.right p (by assumption);

lemma frames_union {F: Frame α} {Γ₁ Γ₂ : Theory β} : (⊧ᴹ[F] Γ₁ ∪ Γ₂) ↔ (⊧ᴹ[F] Γ₁) ∧ (⊧ᴹ[F] Γ₂) := by
  constructor;
  . intro h; simp_all [Theory.Frames];
  . intros h p hp;
    rcases hp with (_ | _);
    . exact h.left p (by assumption);
    . exact h.right p (by assumption);

lemma frames_triunion {F: Frame α} {Γ₁ Γ₂ Γ₃ : Theory β} : (⊧ᴹ[F] Γ₁ ∪ Γ₂ ∪ Γ₃) ↔ (⊧ᴹ[F] Γ₁) ∧ (⊧ᴹ[F] Γ₂) ∧ (⊧ᴹ[F] Γ₃) := by
  constructor;
  . intro h; simp_all [Theory.Frames];
  . intros h p hp;
    rcases hp with (_ | _) | _;
    . exact h.left p (by assumption);
    . exact h.right.left p (by assumption);
    . exact h.right.right p (by assumption);

lemma not_Frames {F: Frame α} {Γ : Theory β} : (∃ V w, (w ⊮ᴹ[⟨F, V⟩] Γ)) → ¬(⊧ᴹ[F] Γ) := by
  simp [Frames, Satisfies, Formula.Frames, Formula.Models];
  intros V w p hp h;
  existsi p, hp, V, w;
  assumption;

end Theory

def Formula.FrameConsequence (F : Frame α) (Γ : Theory β) (p : Formula β) := ∀ V w, (w ⊩ᴹ[⟨F, V⟩] Γ) → (w ⊩ᴹ[⟨F, V⟩] p)
notation Γ " ⊨ᴹ[" F "] " p => Formula.FrameConsequence F Γ p
notation Γ " ⊭ᴹ[" F "] " p => ¬(Γ ⊨ᴹ[F] p)

namespace Formula.FrameConsequence

lemma modus_ponens' {F : Frame α} {Γ : Theory β} {p : Formula β} : (Γ ⊨ᴹ[F] p ⟶ q) → (Γ ⊨ᴹ[F] p) → (Γ ⊨ᴹ[F] q) := by
  intro hpq hp V w h;
  have hpq := by simpa using hpq V w h;
  have hp := by simpa using hp V w h;
  exact hpq hp;

end Formula.FrameConsequence

def Formula.FrameClassConsequence (𝔽 : FrameClass α) (Γ : Theory β) (p : Formula β) := ∀ F ∈ 𝔽, Γ ⊨ᴹ[F] p
notation Γ " ⊨ᴹ[" 𝔽 "] " p => Formula.FrameClassConsequence 𝔽 Γ p
notation Γ " ⊭ᴹ[" 𝔽 "] " p => ¬(Γ ⊨ᴹ[𝔽] p)

namespace Formula.FrameClassConsequence

lemma modus_ponens' {𝔽 : FrameClass α} {Γ : Theory β} {p : Formula β} : (Γ ⊨ᴹ[𝔽] p ⟶ q) → (Γ ⊨ᴹ[𝔽] p) → (Γ ⊨ᴹ[𝔽] q) := by
  simp [Formula.FrameClassConsequence];
  intro hpq hp F hF;
  exact (hpq F hF).modus_ponens' (hp F hF);

end Formula.FrameClassConsequence

def Theory.FrameSatisfiable (F : Frame α) (Γ : Theory β) := ∃ V w, w ⊩ᴹ[⟨F, V⟩] Γ

def Theory.FrameClassSatisfiable (𝔽 : FrameClass α) (Γ : Theory β) := ∃ F ∈ 𝔽, Γ.FrameSatisfiable F

section Definabilities

section AxiomDefinabilities

variable (β) [Inhabited β] (F: Frame α)

@[simp]
lemma AxiomK.defines : (⊧ᴹ[F] (𝐊 : AxiomSet β)) := by
  simp [AxiomK.set, AxiomK, Frames, Models];
  aesop;

lemma AxiomT.defines : (Reflexive F) ↔ (⊧ᴹ[F] (𝐓 : AxiomSet β)) := by
  simp [Reflexive];
  constructor;
  . simp [AxiomT, AxiomT.set, Frames, Models];
    aesop;
  . contrapose;
    intro hRefl; simp [Reflexive] at hRefl;
    have ⟨w, hw⟩ := hRefl;
    apply Theory.not_Frames;
    simp [AxiomT, AxiomT.set, Theory.Satisfies];
    existsi (λ w' a' => (w = w') → (a' ≠ default)), w, (atom default);
    constructor;
    . intro w';
      by_cases w = w';
      . simp_all;
      . simp_all;
    . simp;

lemma AxiomD.defines : (Serial F) ↔ (⊧ᴹ[F] (𝐃 : AxiomSet β)) := by
  constructor;
  . simp [AxiomD, AxiomD.set, Frames, Models];
    rintro hSerial p _ w h;
    have ⟨w', hw'⟩ := hSerial w;
    existsi w', hw';
    exact h w' hw';
  . contrapose;
    intro hSerial; simp [Serial] at hSerial;
    have ⟨w, hw⟩ := hSerial;
    apply Theory.not_Frames;
    existsi (λ _ _ => True), w;
    simp [AxiomD, AxiomD.set];
    aesop;

lemma AxiomB.defines : (Symmetric F) ↔ (⊧ᴹ[F] (𝐁 : AxiomSet β)) := by
  constructor;
  . simp [AxiomB, AxiomB.set, Frames, Models]; aesop;
  . contrapose;
    intro hSymm; simp [Symmetric] at hSymm;
    have ⟨w₁, w₂, hw₁w₂, hw₂w₁⟩ := hSymm;
    apply Theory.not_Frames;
    simp [AxiomB, AxiomB.set];
    existsi (λ w' _ => w' = w₁), w₁, (atom default);
    constructor;
    . simp;
    . existsi w₂, (by assumption);
      intro w';
      by_cases w' = w₁;
      . aesop;
      . simp_all;

lemma Axiom4.defines : (Transitive F) ↔ (⊧ᴹ[F] (𝟒 : AxiomSet β)) := by
  constructor;
  . simp [Axiom4, Axiom4.set, Frames, Models]; aesop;
  . contrapose;
    intro hTrans; simp [Transitive] at hTrans;
    have ⟨w₁, w₂, w₃, _, _, _⟩ := hTrans;
    apply Theory.not_Frames;
    simp [Axiom4, Axiom4.set];
    existsi (λ w' a' => w' = w₃ → a' ≠ default), w₁, (atom default);
    constructor;
    . intro w';
      by_cases w' = w₃;
      . aesop;
      . simp_all;
    . existsi w₂, (by assumption), w₃, (by assumption); aesop;

lemma Axiom5.defines : (Euclidean F) ↔ (⊧ᴹ[F] (𝟓 : AxiomSet β)) := by
  constructor;
  . simp [Axiom5, Axiom5.set, Frames, Models]; aesop;
  . contrapose;
    intro hEucl; simp [Euclidean] at hEucl;
    have ⟨w₁, w₂, w₃, _, _, _⟩ := hEucl;
    apply Theory.not_Frames;
    simp [Axiom5, Axiom5.set];
    existsi (λ w' _ => ¬F w₂ w'), w₁, (atom default), w₃;
    constructor;
    . simp_all;
    . existsi (by assumption), w₂, (by assumption);
      intros; simp; aesop;

lemma AxiomDot2.defines : (Confluent F) ↔ (⊧ᴹ[F] (.𝟐 : AxiomSet β)) := by sorry

lemma AxiomDot3.defines : (Functional F) ↔ (⊧ᴹ[F] (.𝟑 : AxiomSet β)) := by sorry

lemma AxiomCD.defines : (RightConvergent F) ↔ (⊧ᴹ[F] (𝐂𝐃 : AxiomSet β)) := by sorry

lemma AxiomC4.defines : (Dense F) ↔ (⊧ᴹ[F] (𝐂𝟒 : AxiomSet β)) := by sorry

lemma AxiomL.implies_transitive  : (⊧ᴹ[F] (𝐋 : AxiomSet β)) → Transitive F := by
  contrapose;
  intro hT; simp [Transitive] at hT;
  obtain ⟨w₁, w₂, w₃, r₂₃, r₁₂, nr₁₃⟩ := hT;
  apply Theory.not_Frames;
  simp [AxiomL, AxiomL.set];
  existsi (λ w' _ => (w' ≠ w₂ ∧ w' ≠ w₃)), w₁, (atom default);
  constructor;
  . intro x hx h;
    by_cases hx₂ : x = w₂;
    . simp_all [hx₂]; simpa using h w₃ r₂₃;
    . by_cases hx₃ : x = w₃ <;> simp_all [hx₃];
  . existsi w₂;
    aesop;

lemma AxiomL.implies_cwf  : (⊧ᴹ[F] (𝐋 : AxiomSet β)) → ConverseWellFounded F := by
  contrapose;
  intro hCF;
  obtain ⟨X, hX₁, hX₂⟩ := by simpa using WellFounded.wellFounded_iff_has_min.not.mp hCF;
  let V : Valuation α β := λ w _ => w ∉ X;
  let w := hX₁.some;
  let a : Formula β := atom default;
  apply Theory.not_Frames;
  simp [Theory.Satisfies, AxiomL.set, AxiomL, -Satisfies.box_def];
  existsi V, w, a;
  constructor;
  . simp only [Formula.Satisfies.box_def];
    intro x _;
    by_cases hxs : x ∈ X
    . obtain ⟨y, hy₁, hy₂⟩ := hX₂ x hxs;
      simp only [Formula.Satisfies.imp_def];
      left;
      simp;
      existsi y;
      constructor;
      . simpa [flip] using hy₂;
      . simpa;
    . aesop;
  . obtain ⟨w', hw'₁, hw'₂⟩ := hX₂ w (by apply Set.Nonempty.some_mem);
    simp;
    existsi w';
    constructor;
    . simpa [flip] using hw'₂;
    . simp_all;

lemma AxiomL.implied_by_transitive_cwf : (Transitive F ∧ ConverseWellFounded F) → (⊧ᴹ[F] (𝐋 : AxiomSet β)) := by
  rintro ⟨hTrans, hWF⟩;
  simp [AxiomL, AxiomL.set];
  intro p V w;
  simp only [Formula.Satisfies.imp_def'];
  suffices (¬⊧ᴹ[⟨F, V⟩,w] □p) → (¬⊧ᴹ[⟨F, V⟩,w] □(□p ⟶ p)) by exact not_imp_not.mp this;

  intro h; simp at h;
  obtain ⟨z, rwz, hz⟩ := h;
  obtain ⟨xm, ⟨hxm₁, hxm₂⟩⟩ := hWF.has_min ({ x | (F w x) ∧ (¬⊧ᴹ[⟨F, V⟩, x] p) }) (by existsi z; simp [rwz, hz])

  have h₁ : (⊧ᴹ[⟨F, V⟩, xm] □p) := by
    simp only [Satisfies.box_def];
    intro y hy;
    have : F w y := hTrans (by simp_all) hy;
    by_contra hC;
    have := hxm₂ y ⟨(hTrans (by simp_all) hy), hC⟩;
    contradiction;
  have h₂ : (¬⊧ᴹ[⟨F, V⟩, xm] (□p ⟶ p)) := by
    simp only [Formula.Satisfies.imp_def', not_imp];
    constructor;
    . exact h₁
    . simp_all;
  have h₃ : ¬(⊧ᴹ[⟨F, V⟩, w] □(□p ⟶ p)) := by
    simp [Satisfies.box_def, -Satisfies.imp_def'];
    existsi xm;
    constructor;
    . simp_all;
    . exact h₂;
  exact h₃;

lemma AxiomL.defines : (Transitive F ∧ ConverseWellFounded F) ↔ (⊧ᴹ[F] (𝐋 : AxiomSet β)) := ⟨
    by apply implied_by_transitive_cwf,
    by intro h; exact ⟨AxiomL.implies_transitive β F h, AxiomL.implies_cwf β F h⟩
  ⟩

end AxiomDefinabilities

section LogicDefinabilities

variable [Inhabited α] [Inhabited β] {F: Frame α}

def FrameClassDefinability (Λ : AxiomSet β) (P : Frame α → Prop) := ∀ {F : Frame α}, (P F) ↔ (F ∈ 𝔽(Λ))

instance LogicK.FrameClassDefinability : @FrameClassDefinability α β 𝐊 (λ _ => True) := by
  intro F;
  constructor;
  . intros; apply AxiomK.defines;
  . simp;

instance : Nonempty (𝔽((𝐊 : AxiomSet β)) : FrameClass α) := by
  existsi (λ _ _ => True);
  apply LogicK.FrameClassDefinability.mp;
  trivial;

instance LogicKD.FrameClassDefinability : @FrameClassDefinability α β 𝐊𝐃 Serial := by
  intro F;
  simp [LogicKD, AxiomSetFrameClass.union, -AxiomSetFrameClass];
  constructor;
  . intro hSerial;
    have := (AxiomK.defines β F);
    have := (AxiomD.defines β F).mp hSerial;
    simp_all;
  . intros;
    apply (AxiomD.defines β F).mpr;
    simp_all;

instance : Nonempty (𝔽((𝐊𝐃 : AxiomSet β)) : FrameClass α) := by
  existsi (λ _ _ => True);
  apply LogicKD.FrameClassDefinability.mp;
  simp [Serial];

instance LogicS4.FrameClassDefinability : @FrameClassDefinability α β 𝐒𝟒 (λ F => (Reflexive F ∧ Transitive F)) := by
  intro F;
  simp [LogicKT4, AxiomSetFrameClass.triunion, -AxiomSetFrameClass];
  constructor;
  . rintro ⟨hRefl, hTrans⟩;
    have := (AxiomK.defines β F);
    have := (AxiomT.defines β F).mp hRefl;
    have := (Axiom4.defines β F).mp hTrans;
    simp_all;
  . intros;
    constructor;
    . apply (AxiomT.defines β F).mpr; simp_all;
    . apply (Axiom4.defines β F).mpr; simp_all;

instance : Nonempty (𝔽((𝐒𝟒 : AxiomSet β)) : FrameClass α) := by
  existsi (λ _ _ => True);
  apply LogicS4.FrameClassDefinability.mp;
  simp [Reflexive, Transitive];

instance LogicS5.FrameClassDefinability : @FrameClassDefinability α β 𝐒𝟓 (λ F => (Reflexive F ∧ Euclidean F)) := by
  intro F;
  simp [LogicKT5, AxiomSetFrameClass.triunion, -AxiomSetFrameClass];
  constructor;
  . rintro ⟨hRefl, hEucl⟩;
    have := (AxiomK.defines β F);
    have := (AxiomT.defines β F).mp hRefl;
    have := (Axiom5.defines β F).mp hEucl;
    simp_all;
  . intros;
    constructor;
    . apply (AxiomT.defines β F).mpr; simp_all;
    . apply (Axiom5.defines β F).mpr; simp_all;

instance : Nonempty (𝔽((𝐒𝟓 : AxiomSet β)) : FrameClass α) := by
  existsi (λ _ _ => True);
  apply LogicS5.FrameClassDefinability.mp;
  simp [Reflexive, Euclidean]

instance LogicGL.FrameClassDefinability : @FrameClassDefinability α β 𝐆𝐋 (λ F => (Transitive F ∧ ConverseWellFounded F)) := by
  intro F;
  simp [LogicGL, AxiomSetFrameClass.union];
  have := AxiomK.defines β F;
  have := AxiomL.defines β F;
  aesop;

/-
instance : Nonempty (𝔽((𝐆𝐋 : AxiomSet β)) : FrameClass α) := ⟨
  (λ _ _ => False),
  (by
    apply LogicGL.FrameClassDefinability.mp;
    constructor;
    . simp [Transitive];
    . simp [ConverseWellFounded];
      sorry;
  )
⟩
-/

end LogicDefinabilities

end Definabilities

end LO.Modal.Normal
