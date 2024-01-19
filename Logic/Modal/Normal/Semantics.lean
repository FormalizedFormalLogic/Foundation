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

namespace Formula

def Satisfies (M : Model α β) (w : α) : Formula β → Prop
  | atom a  => a ∈ M.val w
  | falsum  => False
  | and p q => (p.Satisfies M w) ∧ (q.Satisfies M w)
  | or p q  => (p.Satisfies M w) ∨ (q.Satisfies M w)
  | imp p q => ¬(p.Satisfies M w) ∨ (q.Satisfies M w)
  | box p   => ∀w', M.frame w w' → p.Satisfies M w'

notation "⊧ᴹ[" M "," w "] " p => Satisfies M w p

namespace Satisfies

variable {M : Model α β}

@[simp] lemma atom_def : (⊧ᴹ[M, w] atom a) ↔ a ∈ M.val w := by simp [Satisfies];

@[simp] lemma top_def : (⊧ᴹ[M, w] ⊤) := by simp [Satisfies];

@[simp] lemma bot_def : (⊧ᴹ[M, w] ⊥) ↔ False := by simp [Satisfies];

@[simp] lemma and_def : (⊧ᴹ[M, w] p ⋏ q) ↔ (⊧ᴹ[M, w] p) ∧ (⊧ᴹ[M, w] q) := by simp [Satisfies];

@[simp] lemma or_def : (⊧ᴹ[M, w] p ⋎ q) ↔ (⊧ᴹ[M, w] p) ∨ (⊧ᴹ[M, w] q) := by simp [Satisfies];

lemma imp_def : (⊧ᴹ[M, w] p ⟶ q) ↔ ¬(⊧ᴹ[M, w] p) ∨ (⊧ᴹ[M, w] q) := by simp [Satisfies];
@[simp] lemma imp_def' : (⊧ᴹ[M, w] p ⟶ q) ↔ (⊧ᴹ[M, w] p) → (⊧ᴹ[M, w] q) := by simp [Satisfies, imp_iff_not_or];

@[simp] lemma box_def : (⊧ᴹ[M, w] □p) ↔ (∀w', M.frame w w' → (⊧ᴹ[M, w'] p)) := by simp [Satisfies];
@[simp] lemma dia_def : (⊧ᴹ[M, w] ◇p) ↔ (∃w', M.frame w w' ∧ (⊧ᴹ[M, w'] p)) := by simp [Satisfies];

@[simp] lemma neg_def : (⊧ᴹ[M, w] (neg p)) ↔ ¬(⊧ᴹ[M, w] p) := by simp [Satisfies];
@[simp] lemma neg_def' : (⊧ᴹ[M, w] ~p) ↔ ¬(⊧ᴹ[M, w] p) := by simp [Satisfies];

end Satisfies


def Models (M : Model α β) (p : Formula β) := ∀w, (⊧ᴹ[M, w] p)
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

end Models


def Frames (F: Frame α) (p : Formula β) := ∀ V, ⊧ᴹ[⟨F, V⟩] p

notation "⊧ᴹ[" f "] " p => Frames f p

namespace Frames

variable {F: Frame α}

@[simp] lemma bot_def : ¬(⊧ᴹ[F] (⊥ : Formula β)) := by simp [Frames];

lemma modus_ponens : (⊧ᴹ[F] p ⟶ q) → (⊧ᴹ[F] p) → (⊧ᴹ[F] q) := by
  intro h₁ h₂ V;
  apply Models.modus_ponens (h₁ V) (h₂ V);

lemma necessitation : (⊧ᴹ[F] p) → (⊧ᴹ[F] □p) := by
  intro h V;
  apply Models.necessitation (h V);

end Frames

lemma not_Frames : (∃ V w, ¬(⊧ᴹ[⟨F, V⟩, w] p)) → ¬(⊧ᴹ[F] p) := by
  simp;
  intro V w hw hf;
  exact hw $ hf V w;

end Formula


@[simp]
def Theory.Satisfies (M : Model α β) (w : α) (Γ : Theory β) := ∀ p ∈ Γ, ⊧ᴹ[M, w] p
notation "⊧ᴹ[" M "," w "] " Γ => Theory.Satisfies M w Γ

@[simp]
def Theory.Models (M : Model α β) (Γ : Theory β) := ∀ p ∈ Γ, ⊧ᴹ[M] p
notation "⊧ᴹ[" M "] " Γ => Theory.Models M Γ

@[simp]
def Theory.Frames (F : Frame α) (Γ : Theory β) := ∀ p ∈ Γ, ⊧ᴹ[F] p
notation "⊧ᴹ[" F "] " Γ => Theory.Frames F Γ

abbrev FrameClass (α : Type u) := Set (Frame α)

def Formula.FrameClasses (𝔽 : FrameClass α) (p : Formula β) := ∀ F ∈ 𝔽, ⊧ᴹ[F] p
notation "⊧ᴹ[" 𝔽 "] " p => Formula.FrameClasses 𝔽 p

@[simp]
def Theory.FrameClasses (𝔽 : FrameClass α) (Γ : Theory β) := ∀ p ∈ Γ, ⊧ᴹ[𝔽] p
notation "⊧ᴹ[" 𝔽 "] " Γ => Theory.FrameClasses 𝔽 Γ

@[simp]
def AxiomSetFrameClass (Λ : AxiomSet β) : FrameClass α := { F | ⊧ᴹ[F] Λ }
notation "𝔽(" Λ ")" => AxiomSetFrameClass Λ

namespace Formula.FrameClasses

variable {𝔽 : FrameClass α} {p q : Formula β}

lemma modus_ponens : (⊧ᴹ[𝔽] p ⟶ q) → (⊧ᴹ[𝔽] p) → (⊧ᴹ[𝔽] q) := by
  intro h₁ h₂ F hF;
  apply Frames.modus_ponens (h₁ F hF) (h₂ F hF);

lemma necessitation : (⊧ᴹ[𝔽] p) → (⊧ᴹ[𝔽] □p) := by
  intro h F hF;
  apply Frames.necessitation (h F hF);

end Formula.FrameClasses

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

lemma not_Frames {F: Frame α} {Γ : Theory β} : (∃ V w, ¬(⊧ᴹ[⟨F, V⟩, w] Γ)) → ¬(⊧ᴹ[F] Γ) := by
  simp [Frames, Satisfies, Formula.Frames, Formula.Models];
  intros V w p hp h;
  existsi p, hp, V, w;
  assumption;

end Theory

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
      . simp_all; intros; trivial;
    . simp;
      aesop;

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
    . simp; trivial;
    . existsi w₂, (by assumption);
      intro w';
      by_cases w' = w₁;
      . aesop;
      . simp [*]; intros; aesop;

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
      . simp [*]; intros; trivial;
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
    . simp; simp[*]; trivial;
    . existsi (by assumption), w₂, (by assumption);
      intros; simp; aesop;

lemma AxiomDot2.defines : (Confluent F) ↔ (⊧ᴹ[F] (.𝟐 : AxiomSet β)) := by sorry

lemma AxiomDot3.defines : (Functional F) ↔ (⊧ᴹ[F] (.𝟑 : AxiomSet β)) := by sorry

lemma AxiomCD.defines : (RightConvergent F) ↔ (⊧ᴹ[F] (𝐂𝐃 : AxiomSet β)) := by sorry

lemma AxiomC4.defines : (Dense F) ↔ (⊧ᴹ[F] (𝐂𝟒 : AxiomSet β)) := by sorry

lemma AxiomL.defines : (Transitive F ∧ WellFounded F) ↔ (⊧ᴹ[F] (𝐋 : AxiomSet β)) := by sorry

/-
lemma AxiomL.defines [DecidableEq α] : ∀ (F: Frame α), (Transitive f ∧ WellFounded f) ↔ (⊧ᴹ[F] (𝐋 : AxiomSet β)) := by
  intro f;
  constructor;
  . rintro ⟨hTrans, hWF⟩;
    simp [AxiomL, AxiomL.set];
    intro p V w h₁;
    by_contra hC; simp at hC;
  . contrapose;
    intro h;
    cases (not_and_or.mp h) with
    | inl hnT =>
      simp [Transitive] at hnT;
      have ⟨w₁, w₂, w₃, _, _, _⟩ := hnT;
      apply Theory.not_Frames;
      simp [AxiomL, AxiomL.set];
      existsi (λ w' _ => w' ≠ w₂ ∧ w' ≠ w₃), w₁, (atom default);
      constructor;
      . intro x hx;
        by_cases x = w₂;
        . intros a; have := a w₃ (by aesop); aesop;
        . sorry;
      . existsi w₂; aesop;
    | inr hnWF => sorry;
-/

end AxiomDefinabilities

section LogicDefinabilities

variable [Inhabited α] [Inhabited β] (F: Frame α)

attribute [simp] LogicKD LogicKT4

lemma FrameClass.union (Λ₁ Λ₂ : AxiomSet β) : (𝔽(Λ₁ ∪ Λ₂) : FrameClass α) = 𝔽(Λ₁) ∩ 𝔽(Λ₂) := by aesop;

lemma FrameClass.triunion (Λ₁ Λ₂ Λ₃ : AxiomSet β) : (𝔽(Λ₁ ∪ Λ₂ ∪ Λ₃) : FrameClass α) = 𝔽(Λ₁) ∩ 𝔽(Λ₂) ∩ 𝔽(Λ₃) := by aesop;

lemma LogicK.def_FrameClass : F ∈ 𝔽((𝐊 : AxiomSet β)) := by apply AxiomK.defines;

instance : Nonempty (𝔽((𝐊 : AxiomSet β)) : FrameClass α) := ⟨(λ _ _ => True), (by apply LogicK.def_FrameClass)⟩

lemma LogicKD.def_FrameClass : (Serial F) ↔ F ∈ 𝔽((𝐊𝐃 : AxiomSet β)) := by
  simp only [LogicKD, FrameClass.union];
  constructor;
  . intro hSerial;
    have := (AxiomK.defines β F);
    have := (AxiomD.defines β F).mp hSerial;
    simp_all;
  . intros;
    apply (AxiomD.defines β F).mpr;
    simp_all;

instance : Nonempty (𝔽((𝐊𝐃 : AxiomSet β)) : FrameClass α) := ⟨
  (λ _ _ => True),
  (by apply (LogicKD.def_FrameClass _).mp; simp [Serial];)
⟩

lemma LogicS4.def_FrameClass : (Reflexive F ∧ Transitive F) ↔ (F ∈ 𝔽((𝐒𝟒 : AxiomSet β))) := by
  simp only [LogicS4, LogicKT4, FrameClass.triunion];
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

instance : Nonempty (𝔽((𝐒𝟒 : AxiomSet β)) : FrameClass α) := ⟨
  (λ _ _ => True),
  (by apply (LogicS4.def_FrameClass _).mp; simp [Reflexive, Transitive];)
⟩

lemma LogicS5.def_FrameClass : (Reflexive F ∧ Euclidean F) ↔ F ∈ 𝔽((𝐒𝟓 : AxiomSet β)) := by
  simp only [LogicS5, LogicKT5, FrameClass.triunion];
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

instance : Nonempty (𝔽((𝐒𝟓 : AxiomSet β)) : FrameClass α) := ⟨
  (λ _ _ => True),
  (by apply (LogicS5.def_FrameClass _).mp; simp [Reflexive, Euclidean];)
⟩

/-
lemma LogicGL.def_FrameClass : ∀ f, (Transitive f ∧ WellFounded f) ↔ (F ∈ FrameClass α β 𝐆𝐋) := by
  simp only [LogicGL];
  intro f;
  constructor;
  . intro hR;
    apply Theory.frames_union.mpr ⟨
      (AxiomK.defines β F),
      (AxiomL.defines β F).mp hR
    ⟩;
  . intro hp;
    apply (AxiomL.defines β F).mpr;
    aesop;

lemma LogicGL.trivialFrame : ∃ f, F ∈ FrameClass α β 𝐆𝐋 := by
  existsi (λ _ _ => True);
  apply (def_FrameClass _).mp;
  simp [Transitive];
-/

end LogicDefinabilities

end Definabilities

end LO.Modal.Normal
