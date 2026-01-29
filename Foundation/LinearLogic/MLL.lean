module
public import Foundation.Logic.Entailment

/-!
# Multiplicative linear logic
-/

@[expose] public section

namespace LO.LinearLogic.MLL

inductive Formula where
  | atom : ℕ → Formula
  | natom : ℕ → Formula
  | one : Formula
  | bot : Formula
  | tensor : Formula → Formula → Formula
  | par : Formula → Formula → Formula

namespace Formula

instance : One Formula := ⟨one⟩

instance : Bot Formula := ⟨bot⟩

instance : HasTensor Formula := ⟨tensor⟩

instance : HasPar Formula := ⟨par⟩

variable {α : Type*}

def neg : Formula → Formula
  |  atom a => natom a
  | natom a => atom a
  |       1 => ⊥
  |       ⊥ => 1
  |   φ ⨂ ψ => neg φ ⅋ neg ψ
  |   φ ⅋ ψ => neg φ ⨂ neg ψ

instance : Tilde Formula := ⟨neg⟩

@[simp] lemma neg_atom (p : ℕ) : ∼atom p = natom p := rfl

@[simp] lemma neg_natom (p : ℕ) : ∼natom p = atom p := rfl

@[simp] lemma neg_one : ∼(1 : Formula) = ⊥ := rfl

@[simp] lemma neg_bot : ∼(⊥ : Formula) = 1 := rfl

@[simp] lemma neg_tensor (φ ψ : Formula) : ∼(φ ⨂ ψ) = ∼φ ⅋ ∼ψ := rfl

@[simp] lemma neg_par (φ ψ : Formula) : ∼(φ ⅋ ψ) = ∼φ ⨂ ∼ψ := rfl

@[simp] lemma neg_neg (φ : Formula) : ∼∼φ = φ := by
  match φ with
  |  atom a => rfl
  | natom a => rfl
  |       1 => rfl
  |       ⊥ => rfl
  |   φ ⅋ ψ => simp [neg_neg φ, neg_neg ψ]
  |   φ ⨂ ψ => simp [neg_neg φ, neg_neg ψ]

instance : HasLolli Formula := ⟨fun φ ψ ↦ ∼φ ⅋ ψ⟩

lemma lolli_def (φ ψ : Formula) : φ ⊸ ψ = ∼φ ⅋ ψ := rfl

end Formula

variable {α : Type*}

abbrev Sequent := List Formula

inductive Derivation : Sequent → Type _
  | identity (p : ℕ) : Derivation [.atom p, .natom p]
  | cut : Derivation (φ :: Γ) → Derivation (∼φ :: Δ) → Derivation (Γ ++ Δ)
  | exchange : Derivation Γ → Γ.Perm Δ → Derivation Δ
  | one : Derivation [1]
  | false : Derivation Γ → Derivation (⊥ :: Γ)
  | tensor : Derivation (φ :: Γ) → Derivation (ψ :: Δ) → Derivation (φ ⨂ ψ :: (Γ ++ Δ))
  | par : Derivation (φ :: ψ :: Γ) → Derivation (φ ⅋ ψ :: Γ)

abbrev Proof (φ : Formula) : Type _ := Derivation [φ]

inductive Symbol where
  | mll

notation "𝐌𝐋𝐋" => Symbol.mll

instance : Entailment Symbol Formula := ⟨fun _ ↦ Proof⟩

scoped prefix:45 "⊢! " => Derivation

abbrev Derivable (Γ : Sequent) : Prop := Nonempty (Derivation Γ)

scoped prefix:45 "⊢ " => Derivable

namespace Derivation

def cast (d : ⊢! Γ) (e : Γ = Δ) : ⊢! Δ := e ▸ d

def rotate (d : ⊢! φ :: Γ) : ⊢! Γ ++ [φ] :=
  d.exchange (by grind only [List.perm_comm, List.perm_append_singleton])

def em : (φ : Formula) → ⊢! [φ, ∼φ]
  |  .atom a => identity a
  | .natom a => (identity a).rotate
  |        1 => (false one).rotate
  |        ⊥ => false one
  |    φ ⨂ ψ => ((em φ).tensor (em ψ)).rotate.par.rotate
  |    φ ⅋ ψ => ((em φ).rotate.tensor (em ψ).rotate).rotate.par

end Derivation

namespace Proof

open Derivation

def identity : 𝐌𝐋𝐋 ⊢! φ ⊸ φ := (em φ).rotate.par

def modusPonens (d₁ : 𝐌𝐋𝐋 ⊢! φ ⊸ ψ) (d₂ : 𝐌𝐋𝐋 ⊢! φ) : 𝐌𝐋𝐋 ⊢! ψ :=
  have d₁ : ⊢! [∼(φ ⨂ ∼ψ)] := d₁.cast <| by simp [Formula.lolli_def]
  have b : ⊢! [φ ⨂ ∼ψ, ∼φ, ψ] := (em φ).tensor (em ψ).rotate
  cut d₂ (cut b d₁)

end Proof

example : 𝐌𝐋𝐋 ⊢ φ ⅋ ∼φ := ⟨Derivation.par (Derivation.em _)⟩

end LO.LinearLogic.MLL

end
