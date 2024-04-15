import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Axioms

namespace LO.Modal.Normal

open Formula

variable {α : Type u} {β : Type v}

abbrev Frame (α) := α → α → Prop

@[simp]
def Multiframe (rel : Frame α) : ℕ → α → α → Prop
| 0 => (· = ·)
| n + 1 => λ x y => ∃ z, (rel x z ∧ Multiframe rel n z y)

notation:max F "[" n "]" => Multiframe F n

abbrev Valuation (α β) := α → β → Prop

structure Model (α β) where
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

@[simp]
lemma multibox_def : (w ⊩ᴹ[M] □[n]p) ↔ (∀ v, M.frame[n] w v → (v ⊩ᴹ[M] p)) := by
  induction n generalizing w with
  | zero => simp;
  | succ n ih => aesop;

@[simp]
lemma multidia_def : (w ⊩ᴹ[M] ◇[n]p) ↔ (∃ v, M.frame[n] w v ∧ (v ⊩ᴹ[M] p)) := by
  induction n generalizing w with
  | zero => simp;
  | succ n ih => aesop;

lemma modus_ponens (m₁ : w ⊩ᴹ[M] p ⟶ q) : (w ⊩ᴹ[M] p) → (w ⊩ᴹ[M] q) := by simpa [imp_def'] using m₁;

end Satisfies

def Models (M : Model α β) (p : Formula β) := ∀w, (w ⊩ᴹ[M] p)
notation "⊧ᴹ[" M "] "  p => Models M p

namespace Models

variable {M : Model α β}

@[simp]
lemma neg_def [Inhabited α] : (⊧ᴹ[M] (~p)) → ¬(⊧ᴹ[M] p) := by
  simp [Models];
  intro h;
  existsi default;
  exact h default;

@[simp] lemma bot_def [Inhabited α] : ¬(⊧ᴹ[M] ⊥) := by simp [Models];

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

@[simp] lemma bot_def [Inhabited α] : ¬(⊧ᴹ[F] (⊥ : Formula β)) := by simp [Frames];

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
notation w " ⊩ᴹ[" M "] " Γ => Theory.Satisfies M w Γ

@[simp] abbrev Theory.Unsatisfies (M : Model α β) (w : α) (Γ : Theory β) := ¬(w ⊩ᴹ[M] Γ)
notation w " ⊮ᴹ[" M "] " Γ => Theory.Unsatisfies M w Γ

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

def AxiomSetFrameClass (Λ : AxiomSet β) : FrameClass α := { F | ⊧ᴹ[F] Λ }
notation "𝔽(" Λ ")" => AxiomSetFrameClass Λ

lemma AxiomSetFrameClass.union {Λ₁ Λ₂ : AxiomSet β} : (𝔽(Λ₁ ∪ Λ₂) : FrameClass α) = 𝔽(Λ₁) ∩ 𝔽(Λ₂) := by simp [AxiomSetFrameClass]; aesop;

namespace Theory

lemma models_neg_singleton [Inhabited α] {M : Model α β} {p : Formula β} : (⊧ᴹ[M] {~p}) → (¬⊧ᴹ[M] {p}) := by
  intro hnp hp;
  exact Formula.Models.neg_def (hnp (~p) (by simp)) (hp p (by simp));

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

variable  {𝔽 : FrameClass α} {Γ Δ : Theory β} {p : Formula β}

lemma modus_ponens' : (Γ ⊨ᴹ[𝔽] p ⟶ q) → (Γ ⊨ᴹ[𝔽] p) → (Γ ⊨ᴹ[𝔽] q) := by
  simp [Formula.FrameClassConsequence];
  intro hpq hp F hF;
  exact (hpq F hF).modus_ponens' (hp F hF);

lemma weakening (hΓΔ : Γ ⊆ Δ) : (Γ ⊨ᴹ[𝔽] p) → (Δ ⊨ᴹ[𝔽] p) := by
  intro h F hF V w hΔ;
  apply h F hF V w;
  intro p hp;
  exact hΔ p (hΓΔ hp);

lemma necessitation (Γ : Theory β) : (∅ ⊨ᴹ[𝔽] p) → (Γ ⊨ᴹ[𝔽] □p) := by
  intro h F hF V w _;
  have := h F hF V w (by simp);
  aesop;

end Formula.FrameClassConsequence

def Theory.FrameSatisfiable (F : Frame α) (Γ : Theory β) := ∃ V w, w ⊩ᴹ[⟨F, V⟩] Γ

def Theory.FrameClassSatisfiable (𝔽 : FrameClass α) (Γ : Theory β) := ∃ F ∈ 𝔽, Γ.FrameSatisfiable F

def AxiomSetDefinability (α β) (Λ : AxiomSet β)  (P : Frame α → Prop) := ∀ {F : Frame α}, P F ↔ ⊧ᴹ[F] Λ

def AxiomSetDefinability.toFrameClass (h : AxiomSetDefinability α β Λ P) : ∀ {F : Frame α}, P F ↔ F ∈ 𝔽(Λ) := by
  intro F;
  exact h;

lemma AxiomSetDefinability.union
  (h₁ : AxiomSetDefinability α β Λ₁ P₁)
  (h₂ : AxiomSetDefinability α β Λ₂ P₂) : AxiomSetDefinability α β (Λ₁ ∪ Λ₂) (λ F => P₁ F ∧ P₂ F) := by
  simp_all [AxiomSetDefinability, AxiomSetFrameClass.union];
  aesop;

lemma AxiomSet.K.defines : AxiomSetDefinability α β (𝐊 : AxiomSet β) (λ _ => True) := by
  simp_all [AxiomSetDefinability, Frames, Models];
  aesop;

lemma AxiomSetDefinability.union_with_K (h : AxiomSetDefinability α β Λ P) : AxiomSetDefinability α β (𝐊 ∪ Λ) P := by simpa using @AxiomSetDefinability.union α β 𝐊 (λ _ => True) Λ P AxiomSet.K.defines h

instance : Nonempty (𝔽((𝐊 : AxiomSet β)) : FrameClass α) := by
  existsi (λ _ _ => True);
  apply AxiomSet.K.defines.mp;
  trivial;

-- TODO: move
lemma AxiomSet.Dot3.defines : AxiomSetDefinability α β .𝟑 (Functional) := by sorry


end LO.Modal.Normal
