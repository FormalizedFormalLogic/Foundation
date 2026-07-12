module

public import Foundation.Logic.Entailment
public import Foundation.LinearLogic.LogicSymbol

/-!
# Multiplicative exponential linear logic without neutrals
-/

@[expose] public section

namespace LO.Propositional.LinearLogic.MultiplicativeExponential

inductive Formula where
  | atom : ℕ → Formula
  | natom : ℕ → Formula
  | tensor : Formula → Formula → Formula
  | par : Formula → Formula → Formula
  | bang : Formula → Formula
  | quest : Formula → Formula

namespace Formula

instance : MultiplicativeConnective Formula where
  tensor := tensor
  par := par
  tensor_injective _ _ _ _ := by simp [tensor.injEq]
  par_injective _ _ _ _ := by simp [par.injEq]

instance : ExponentialConnective Formula where
  bang := bang
  quest := quest
  bang_injective _ _ := by simp [bang.injEq]
  quest_injective _ _ := by simp [quest.injEq]

variable {α : Type*}

def neg : Formula → Formula
  |  atom a => natom a
  | natom a => atom a
  |   φ ⨂ ψ => neg φ ⅋ neg ψ
  |   φ ⅋ ψ => neg φ ⨂ neg ψ
  |     ！φ => ？φ.neg
  |     ？φ => ！φ.neg

instance : Tilde Formula := ⟨neg⟩

@[simp] lemma neg_atom (p : ℕ) : ∼atom p = natom p := rfl

@[simp] lemma neg_natom (p : ℕ) : ∼natom p = atom p := rfl

instance : MultiplicativeConnective.DeMorgan Formula where
  tensor _ _ := rfl
  par _ _ := rfl

instance : ExponentialConnective.DeMorgan Formula where
  bang _ := rfl
  quest _ := rfl

@[simp] lemma neg_neg (φ : Formula) : ∼∼φ = φ := by
  match φ with
  |  atom a => rfl
  | natom a => rfl
  |   φ ⅋ ψ => simp [neg_neg φ, neg_neg ψ]
  |   φ ⨂ ψ => simp [neg_neg φ, neg_neg ψ]
  |     ！φ => simp [neg_neg φ]
  |     ？φ => simp [neg_neg φ]

instance : TildeInvolutive Formula where
  neg_involutive := neg_neg

lemma lolli_def (φ ψ : Formula) : φ ⊸ ψ = ∼φ ⅋ ψ := rfl

inductive IsQuest : Formula → Prop
  | intro : IsQuest (？φ)

@[simp] lemma IsQuest.not_atom (p : ℕ) : ¬IsQuest (atom p) := by intro h; cases h
@[simp] lemma IsQuest.not_natom (p : ℕ) : ¬IsQuest (natom p) := by intro h; cases h
@[simp] lemma IsQuest.not_tensor (φ ψ : Formula) : ¬IsQuest (φ ⨂ ψ) := by intro h; cases h
@[simp] lemma IsQuest.not_par (φ ψ : Formula) : ¬IsQuest (φ ⅋ ψ) := by intro h; cases h
@[simp] lemma IsQuest.not_bang (φ : Formula) : ¬IsQuest (！φ) := by intro h; cases h
@[simp] lemma IsQuest.quest (φ : Formula) : IsQuest (？φ) := by constructor

end Formula

variable {α : Type*}

abbrev Sequent := List Formula

namespace Sequent

def IsQuest (Γ : Sequent) : Prop := ∀ φ ∈ Γ, Formula.IsQuest φ

@[simp] lemma IsQuest.nil : IsQuest [] := by simp [IsQuest]

@[simp] lemma IsQuest.cons {φ : Formula} {Γ : Sequent} :
    IsQuest (φ :: Γ) ↔ Formula.IsQuest φ ∧ IsQuest Γ := by
  simp [IsQuest]

end Sequent

inductive Derivation : Sequent → Type _
  | protected id (p : ℕ) : Derivation [.atom p, .natom p]
  | cut : Derivation (φ :: Γ) → Derivation (∼φ :: Δ) → Derivation (Γ ++ Δ)
  | exchange : Derivation Γ → Γ.Perm Δ → Derivation Δ
  | tensor : Derivation (φ :: Γ) → Derivation (ψ :: Δ) → Derivation (φ ⨂ ψ :: (Γ ++ Δ))
  | par : Derivation (φ :: ψ :: Γ) → Derivation (φ ⅋ ψ :: Γ)
  | bang : Derivation (φ :: Γ) → Sequent.IsQuest Γ → Derivation (！φ :: Γ)
  | dereliction : Derivation (φ :: Γ) → Derivation (？φ :: Γ)

abbrev Proof (φ : Formula) : Type _ := Derivation [φ]

inductive Symbol where
  | mell

notation "𝐌𝐄𝐋𝐋" => Symbol.mell

instance : Entailment Symbol Formula := ⟨fun _ ↦ Proof⟩

scoped prefix:45 "⊢! " => Derivation

abbrev Derivable (Γ : Sequent) : Prop := Nonempty (Derivation Γ)

scoped prefix:45 "⊢ " => Derivable

namespace Derivation

def cast (d : ⊢! Γ) (e : Γ = Δ) : ⊢! Δ := e ▸ d

def rotate (d : ⊢! φ :: Γ) : ⊢! Γ ++ [φ] :=
  d.exchange (by grind only [List.perm_comm, List.perm_append_singleton])

def eta : (φ : Formula) → ⊢! [φ, ∼φ]
  |  .atom a => .id a
  | .natom a => (Derivation.id a).rotate
  |    φ ⨂ ψ => ((eta φ).tensor (eta ψ)).rotate.par.rotate
  |    φ ⅋ ψ => ((eta φ).rotate.tensor (eta ψ).rotate).rotate.par
  |      ！φ => (eta φ).rotate.dereliction.rotate.bang (by simp)
  |      ？φ => (eta φ).dereliction.rotate.bang (by simp) |>.rotate

end Derivation

namespace Proof

open Derivation

def identity' : 𝐌𝐄𝐋𝐋 ⊢! φ ⊸ φ := (eta φ).rotate.par

def modusPonens (d₁ : 𝐌𝐄𝐋𝐋 ⊢! φ ⊸ ψ) (d₂ : 𝐌𝐄𝐋𝐋 ⊢! φ) : 𝐌𝐄𝐋𝐋 ⊢! ψ :=
  have d₁ : ⊢! [∼(φ ⨂ ∼ψ)] := d₁.cast <| by simp [Formula.lolli_def]
  have b : ⊢! [φ ⨂ ∼ψ, ∼φ, ψ] := (eta φ).tensor (eta ψ).rotate
  cut d₂ (cut b d₁)

end Proof

end LO.Propositional.LinearLogic.MultiplicativeExponential

end
