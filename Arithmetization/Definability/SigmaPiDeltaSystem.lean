import Arithmetization.Vorspiel.Lemmata
import Logic.FirstOrder.Arith.StrictHierarchy

/-!

# Arithmetical Formula Sorted by Arithmetical Hierarchy

This file defines the $\Sigma_n / \Pi_n / \Delta_n$ formulas of arithmetic of first-order logic.

- `𝚺-[m].Semiformula ξ n` is a `Semiformula ℒₒᵣ ξ n` which is `𝚺-[m]`.
- `𝚷-[m].Semiformula ξ n` is a `Semiformula ℒₒᵣ ξ n` which is `𝚷-[m]`.
- `𝚫-[m].Semiformula ξ n` is a pair of `𝚺-[m].Semiformula ξ n` and `𝚷-[m].Semiformula ξ n`.
- `ProperOn` : `p.ProperOn M` iff `p`'s two element `p.sigma` and `p.pi` are equivalent on model `M`.

-/

namespace LO

class SigmaPiDeltaLike (Ω : Type*) [SigmaSymbol Ω] [PiSymbol Ω] [DeltaSymbol Ω] where
  alt : Ω → Ω

variable {V : Type*}

class SigmaPiDeltaSystem (V : Type*) where
  VecPr : SigmaPiDelta → {k : ℕ} → ((Fin k → V) → Prop) → Prop
  vecPr_delta_iff_sigma_and_pi {k} {P : (Fin k → V) → Prop} : VecPr 𝚫 P ↔ VecPr 𝚺 P ∧ VecPr 𝚷 P
  verum' (Γ k) : VecPr Γ fun _ : Fin k → V ↦ ⊤
  and' {k} {P Q : (Fin k → V) → Prop} : VecPr Γ P → VecPr Γ Q → VecPr Γ fun x ↦ P x ∧ Q x
  not' {k} {P : (Fin k → V) → Prop} : VecPr Γ.alt P → VecPr Γ fun x ↦ ¬P x
  all' {k} {P : (Fin k → V) → V → Prop} : VecPr 𝚷 (fun x ↦ P (x ·.succ) (x 0)) → VecPr 𝚷 fun x ↦ ∀ z, P x z
  retraction' {k l} {P : (Fin k → V) → Prop} (hP : VecPr Γ P) (f : Fin k → Fin l) : VecPr Γ fun v ↦ P fun i ↦ v (f i)
  equal' (Γ) : VecPr Γ fun v : Fin 2 → V ↦ v 0 = v 1

abbrev SigmaPiDeltaSystem.VecFunc (𝔖 : SigmaPiDeltaSystem V)
  (Γ : SigmaPiDelta) (f : (Fin k → V) → V) : Prop := 𝔖.VecPr Γ fun v ↦ v 0 = f (v ·.succ)

namespace SigmaPiDeltaSystem

variable {𝔖 : SigmaPiDeltaSystem V} {Γ : SigmaPiDelta} {k} {P Q : (Fin k → V) → Prop}

namespace VecPr

alias verum := verum'

alias and := and'

alias not := not'

alias all := all'

alias retraction := retraction'

alias equal := equal'

lemma of_iff (hP : 𝔖.VecPr Γ P) (h : ∀ x, P x ↔ Q x) : 𝔖.VecPr Γ Q := by
  have : P = Q := funext <| by simpa
  rcases this
  exact hP

lemma of_sigma_of_pi (hσ : 𝔖.VecPr 𝚺 P) (hπ : 𝔖.VecPr 𝚷 P) : 𝔖.VecPr Γ P :=
  match Γ with
  | 𝚺 => hσ
  | 𝚷 => hπ
  | 𝚫 => vecPr_delta_iff_sigma_and_pi.mpr ⟨hσ, hπ⟩

lemma of_delta (h : 𝔖.VecPr 𝚫 P) {Γ} : 𝔖.VecPr Γ P :=
  of_sigma_of_pi
    (vecPr_delta_iff_sigma_and_pi.mp h |>.1)
    (vecPr_delta_iff_sigma_and_pi.mp h |>.2)

lemma not' (h : 𝔖.VecPr Γ P) : 𝔖.VecPr Γ.alt fun x ↦ ¬P x := not (by simpa)

lemma of_not (h : 𝔖.VecPr Γ.alt (fun x ↦ ¬P x)) : 𝔖.VecPr Γ P := by simpa using not' h

lemma falsum (Γ : SigmaPiDelta) (k : ℕ) : 𝔖.VecPr Γ fun _ : Fin k → V ↦ ⊥ :=
  of_sigma_of_pi (by simpa using not' (verum 𝚷 k)) (by simpa using not' (verum 𝚺 k))

@[simp] lemma constant (Γ : SigmaPiDelta) (k : ℕ) (P : Prop) : 𝔖.VecPr Γ fun _ : Fin k → V ↦ P := by
  by_cases h : P <;> simp [h]
  · apply verum
  · apply falsum

lemma or (hP : 𝔖.VecPr Γ P) (hQ : 𝔖.VecPr Γ Q) : 𝔖.VecPr Γ fun x : Fin k → V ↦ P x ∨ Q x :=
  of_not <| by
    simp only [not_or]; apply and
    · apply not' hP
    · apply not' hQ

lemma imply (hP : 𝔖.VecPr Γ.alt P) (hQ : 𝔖.VecPr Γ Q) : 𝔖.VecPr Γ fun x : Fin k → V ↦ P x → Q x := by
  simp [imp_iff_not_or]; apply or
  · apply not hP
  · exact hQ

lemma ex {k} {P : (Fin k → V) → V → Prop} (h : 𝔖.VecPr 𝚺 fun x ↦ P (x ·.succ) (x 0)) : 𝔖.VecPr 𝚺 fun x ↦ ∃ z, P x z := of_not <| by
  simpa using all (by apply not' h)

lemma iff (hP : 𝔖.VecPr 𝚫 P) (hQ : 𝔖.VecPr 𝚫 Q) : 𝔖.VecPr Γ fun x : Fin k → V ↦ P x ↔ Q x := of_delta <| by
  simp only [iff_iff_implies_and_implies]
  apply and
  · exact imply hP hQ
  · exact imply hQ hP

lemma equal' (Γ) (i j : Fin k) : 𝔖.VecPr Γ fun v ↦ v i = v j := by
  simpa using retraction (equal Γ) ![i, j]

lemma VecFunc.of_sigma {f : (Fin k → V) → V} (h : 𝔖.VecFunc 𝚺 f) {Γ} : 𝔖.VecFunc Γ f := by
  apply of_sigma_of_pi
  · exact h
  · have : 𝔖.VecPr 𝚷 fun v ↦ ∀ y, y = f (v ·.succ) → v 0 = y := all <| imply
      (by simpa using retraction h (0 :> (·.succ.succ)))
      (by simpa using equal' 𝚷 1 0)
    exact of_iff this (fun v ↦ by simp)

lemma conj {k l} {P : Fin l → (Fin k → V) → Prop}
    (h : ∀ i, 𝔖.VecPr Γ fun w : Fin k → V ↦ P i w) :
    𝔖.VecPr Γ fun v : Fin k → V ↦ ∀ i, P i v := by
  induction l
  case zero => simp
  case succ l ih =>
    suffices 𝔖.VecPr Γ fun v : Fin k → V ↦ P 0 v ∧ ∀ i : Fin l, P i.succ v by
      apply of_iff this; intro x
      constructor
      · rintro ⟨h0, hs⟩
        intro i; cases' i using Fin.cases with i
        · exact h0
        · exact hs i
      · intro h
        exact ⟨h 0, fun i ↦ h i.succ⟩
    apply and (h 0); apply ih
    intro i; exact h i.succ

lemma exVec {k l} {P : (Fin k → V) → (Fin l → V) → Prop}
    (h : 𝔖.VecPr 𝚺 fun w : Fin (k + l) → V ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    𝔖.VecPr 𝚺 fun v : Fin k → V ↦ ∃ ys : Fin l → V, P v ys := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l ih =>
    suffices 𝔖.VecPr 𝚺 fun v : Fin k → V ↦ ∃ y, ∃ ys : Fin l → V, P v (y :> ys) by
      apply of_iff this; intro x
      constructor
      · rintro ⟨y, ys, h⟩; exact ⟨_, h⟩
      · rintro ⟨ys, h⟩; exact ⟨ys 0, (ys ·.succ), by simpa using h⟩
    apply ex; apply ih
    let g : Fin (k + (l + 1)) → Fin (k + 1 + l) := Matrix.vecAppend rfl (fun x ↦ x.succ.castAdd l) (Fin.castAdd l 0 :> fun j ↦ j.natAdd (k + 1))
    exact of_iff (retraction h g) (by
      intro v; simp [g]
      apply iff_of_eq; congr
      · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
      · ext i
        cases' i using Fin.cases with i
        · congr 1; ext; simp [Matrix.vecAppend_eq_ite]
        · congr 1; ext; simp [Matrix.vecAppend_eq_ite])

lemma allVec {k l} {P : (Fin k → V) → (Fin l → V) → Prop}
    (h : 𝔖.VecPr 𝚷 fun w : Fin (k + l) → V ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    𝔖.VecPr 𝚷 fun v : Fin k → V ↦ ∀ ys : Fin l → V, P v ys := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l ih =>
    suffices 𝔖.VecPr 𝚷 fun v : Fin k → V ↦ ∀ y, ∀ ys : Fin l → V, P v (y :> ys) by
      apply of_iff this; intro x
      constructor
      · intro h ys; simpa using h (ys 0) (ys ·.succ)
      · intro h y ys; apply h
    apply all; apply ih
    let g : Fin (k + (l + 1)) → Fin (k + 1 + l) := Matrix.vecAppend rfl (fun x ↦ x.succ.castAdd l) (Fin.castAdd l 0 :> fun j ↦ j.natAdd (k + 1))
    exact of_iff (retraction h g) (by
      intro v; simp [g]
      apply iff_of_eq; congr
      · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
      · ext i
        cases' i using Fin.cases with i
        · congr 1; ext; simp [Matrix.vecAppend_eq_ite]
        · congr 1; ext; simp [Matrix.vecAppend_eq_ite])

private lemma substitution_sigma {f : Fin k → (Fin l → V) → V} (hP : 𝔖.VecPr 𝚺 P) (hf : ∀ i, 𝔖.VecFunc 𝚺 (f i)) :
    𝔖.VecPr 𝚺 fun z ↦ P (fun i ↦ f i z) := by
  have : 𝔖.VecPr 𝚺 fun z ↦ ∃ ys : Fin k → V, (∀ i, ys i = f i z) ∧ P ys := by
    apply exVec; apply and
    · apply conj; intro i
      simpa using retraction (VecFunc.of_sigma (hf i)) (i.natAdd l :> fun i ↦ i.castAdd k)
    · exact retraction hP (Fin.natAdd l)
  exact of_iff this <| by
    intro v
    constructor
    · rintro ⟨ys, hys, hP⟩
      have : ys = fun i ↦ f i v := funext hys
      rcases this; exact hP
    · intro hP
      exact ⟨(f · v), by simp, hP⟩

private lemma substitution_pi {f : Fin k → (Fin l → V) → V} (hP : 𝔖.VecPr 𝚷 P) (hf : ∀ i, 𝔖.VecFunc 𝚺 (f i)) :
    𝔖.VecPr 𝚷 fun z ↦ P (fun i ↦ f i z) := by
  have : 𝔖.VecPr 𝚷 fun z ↦ ∀ ys : Fin k → V, (∀ i, ys i = f i z) → P ys := by
    apply allVec; apply imply
    · apply conj; intro i
      simpa using retraction (VecFunc.of_sigma (hf i)) (i.natAdd l :> fun i ↦ i.castAdd k)
    · exact retraction hP (Fin.natAdd l)
  exact of_iff this <| by
    intro v
    constructor
    · intro h; apply h _ (by simp)
    · intro h ys e
      have : ys = (f · v) := funext e
      rcases this; exact h

lemma substitution {f : Fin k → (Fin l → V) → V} (hP : 𝔖.VecPr Γ P) (hf : ∀ i, 𝔖.VecFunc 𝚺 (f i)) : 𝔖.VecPr Γ fun z ↦ P (fun i ↦ f i z) :=
  match Γ with
  | 𝚺 => substitution_sigma hP hf
  | 𝚷 => substitution_pi hP hf
  | 𝚫 => of_sigma_of_pi (substitution_sigma (of_delta hP) hf) (substitution_pi (of_delta hP) hf)

end VecPr

namespace VecFunc

variable {F : (Fin k → V) → V}

open VecPr

lemma nth (Γ) (i : Fin k) : 𝔖.VecFunc Γ fun w ↦ w i := VecPr.equal' Γ 0 i.succ

lemma substitution {f : Fin k → (Fin l → V) → V} (hF : 𝔖.VecFunc Γ F) (hf : ∀ i, 𝔖.VecFunc 𝚺 (f i)) :
    𝔖.VecFunc Γ fun z ↦ F (fun i ↦ f i z) := by
  simp only [VecFunc, Nat.succ_eq_add_one]
  simpa using VecPr.substitution (f := (· 0) :> fun i w ↦ f i (w ·.succ)) hF
    (by intro i
        cases' i using Fin.cases with i
        · simpa using nth 𝚺 0
        · simpa using retraction (hf i) (0 :> (·.succ.succ)))

end VecFunc

end SigmaPiDeltaSystem

/-
class EmbeddingType (V : outParam Type*) (β : Type*) where
  embedding : β ↪ V

namespace EmbeddingType

instance : EmbeddingType V V := ⟨Function.Embedding.refl V⟩

instance (p : V → Prop) : EmbeddingType V (Subtype p) := ⟨Function.Embedding.subtype p⟩

end EmbeddingType

namespace SigmaPiDeltaSystem

class Class {V : Type*} (𝔖 : SigmaPiDeltaSystem V) (α : Type*) [EmbeddingType V α] where
  delta : 𝔖.VecPr 𝚫 fun x : Fin 1 → V ↦ x 0 ∈ Set.range (EmbeddingType.embedding : α ↪ V)

section Class

instance (𝔖 : SigmaPiDeltaSystem V) : 𝔖.Class V where
  delta := VecPr.of_iff (𝔖.verum' 𝚫 1) <| by intro v; simp; exact ⟨v 0, by rfl⟩

variable {𝔖 : SigmaPiDeltaSystem V}

variable {α β γ δ ε ζ : Type*}
  [EmbeddingType V α] [EmbeddingType V β] [EmbeddingType V γ] [EmbeddingType V δ] [EmbeddingType V ε] [EmbeddingType V ζ]
  [𝔖.Class α] [𝔖.Class β] [𝔖.Class γ] [𝔖.Class δ] [𝔖.Class ε] [𝔖.Class ζ]

def Pr₁ (𝔖 : SigmaPiDeltaSystem V) (Γ : SigmaPiDelta) (P : α → Prop) : Prop := 𝔖.VecPr Γ fun x : Fin 1 → V ↦ ∃ a : α, x 0 = EmbeddingType.embedding a ∧ P a
def Pr₂ (𝔖 : SigmaPiDeltaSystem V) (Γ : SigmaPiDelta) (P : α → β → Prop) : Prop :=
  𝔖.VecPr Γ fun x : Fin 2 → V ↦ ∃ (a : α) (b : β), x 0 = EmbeddingType.embedding a ∧ x 1 = EmbeddingType.embedding b ∧ P a b
def Pr₃ (𝔖 : SigmaPiDeltaSystem V) (Γ : SigmaPiDelta) (P : α → β → γ → Prop) : Prop :=
  𝔖.VecPr Γ fun x : Fin 3 → V ↦ ∃ (a : α) (b : β) (c : γ),
    x 0 = EmbeddingType.embedding a ∧ x 1 = EmbeddingType.embedding b ∧ x 2 = EmbeddingType.embedding c ∧ P a b c
def Pr₄ (𝔖 : SigmaPiDeltaSystem V) (Γ : SigmaPiDelta) (P : α → β → γ → δ → Prop) : Prop :=
  𝔖.VecPr Γ fun x : Fin 4 → V ↦ ∃ (a : α) (b : β) (c : γ) (d : δ),
    x 0 = EmbeddingType.embedding a ∧ x 1 = EmbeddingType.embedding b ∧ x 2 = EmbeddingType.embedding c ∧ P a b c d


end Class

end SigmaPiDeltaSystem

-/

end LO
