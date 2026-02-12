module

public import Foundation.Logic.LogicSymbol

@[expose] public section

namespace LO

@[notation_class] class SigmaSymbol (α : Type*) where
  sigma : α

@[notation_class] class PiSymbol (α : Type*) where
  pi : α

@[notation_class] class DeltaSymbol (α : Type*) where
  delta : α

notation "𝚺" => SigmaSymbol.sigma

notation "𝚷" => PiSymbol.pi

notation "𝚫" => DeltaSymbol.delta

attribute [match_pattern] SigmaSymbol.sigma PiSymbol.pi DeltaSymbol.delta

inductive Polarity where | sigma | pi

namespace Polarity

instance : SigmaSymbol Polarity := ⟨sigma⟩

instance : PiSymbol Polarity := ⟨pi⟩

def alt : Polarity → Polarity
  | 𝚺 => 𝚷
  | 𝚷 => 𝚺

@[simp] lemma eq_sigma : sigma = 𝚺 := rfl

@[simp] lemma eq_pi : pi = 𝚷 := rfl

@[simp] lemma alt_sigma : alt 𝚺 = 𝚷 := rfl

@[simp] lemma alt_pi : alt 𝚷 = 𝚺 := rfl

@[simp] lemma alt_alt (Γ : Polarity) : Γ.alt.alt = Γ := by rcases Γ <;> simp

section symbol

variable {α : Type*} [SigmaSymbol α] [PiSymbol α]

protected def coe : Polarity → α
 | 𝚺 => 𝚺
 | 𝚷 => 𝚷

instance : Coe Polarity α := ⟨Polarity.coe⟩

@[simp] lemma coe_sigma : ((𝚺 : Polarity) : α) = 𝚺 := rfl

@[simp] lemma coe_pi : ((𝚷 : Polarity) : α) = 𝚷 := rfl

end symbol

end Polarity

inductive SigmaPiDelta where | sigma | pi | delta

namespace SigmaPiDelta

instance : SigmaSymbol SigmaPiDelta := ⟨sigma⟩

instance : PiSymbol SigmaPiDelta := ⟨pi⟩

instance : DeltaSymbol SigmaPiDelta := ⟨delta⟩

def alt : SigmaPiDelta → SigmaPiDelta
  | 𝚺 => 𝚷
  | 𝚷 => 𝚺
  | 𝚫 => 𝚫

@[simp] lemma eq_sigma : sigma = 𝚺 := rfl

@[simp] lemma eq_pi : pi = 𝚷 := rfl

@[simp] lemma eq_delta : delta = 𝚫 := rfl

@[simp] lemma alt_sigma : alt 𝚺 = 𝚷 := rfl

@[simp] lemma alt_pi : alt 𝚷 = 𝚺 := rfl

@[simp] lemma alt_delta : alt 𝚫 = 𝚫 := rfl

@[simp] lemma alt_alt (Γ : SigmaPiDelta) : Γ.alt.alt = Γ := by rcases Γ <;> simp

@[simp] lemma alt_coe (Γ : Polarity) : SigmaPiDelta.alt Γ = (Γ.alt : SigmaPiDelta) := by cases Γ <;> simp

end SigmaPiDelta

@[notation_class] class UnivQuantifier (α : ℕ → Type*) where
  univ : ∀ {n}, α (n + 1) → α n

@[notation_class] class ExQuantifier (α : ℕ → Type*) where
  ex : ∀ {n}, α (n + 1) → α n

prefix:64 "∀' " => UnivQuantifier.univ

prefix:64 "∃' " => ExQuantifier.ex

attribute [match_pattern]
  UnivQuantifier.univ
  ExQuantifier.ex

class Quantifier (α : ℕ → Type*) extends UnivQuantifier α, ExQuantifier α

/-- Logical Connectives with Quantifiers. -/
class LCWQ (α : ℕ → Type*) extends Quantifier α where
  connectives : (n : ℕ) → LogicalConnective (α n)

instance (α : ℕ → Type*) [LCWQ α] (n : ℕ) : LogicalConnective (α n) := LCWQ.connectives n

instance (α : ℕ → Type*) [Quantifier α] [(n : ℕ) → LogicalConnective (α n)] : LCWQ α where
  connectives := inferInstance

section

variable {α : ℕ → Type*} [UnivQuantifier α] [ExQuantifier α]

def quant : Polarity → α (n + 1) → α n
  | 𝚺, φ => ∃' φ
  | 𝚷, φ => ∀' φ

@[simp] lemma quant_sigma (φ : α (n + 1)) : quant 𝚺 φ = ∃' φ := rfl

@[simp] lemma quant_pi (φ : α (n + 1)) : quant 𝚷 φ = ∀' φ := rfl

end

section UnivQuantifier

variable {α : ℕ → Type*} [UnivQuantifier α]

def univClosure : {n : ℕ} → α n → α 0
  | 0,     a => a
  | _ + 1, a => univClosure (∀' a)

prefix:64 "∀* " => univClosure

@[simp] lemma univClosure_zero (a : α 0) : ∀* a = a := rfl

lemma univClosure_succ {n} (a : α (n + 1)) : ∀* a = ∀* ∀' a := rfl

def univItr : (k : ℕ) → α (n + k) → α n
  | 0,     a => a
  | k + 1, a => univItr k (∀' a)

notation "∀^[" k "] " φ:64 => univItr k φ

@[simp] lemma univItr_zero (a : α n) : ∀^[0] a = a := rfl

@[simp] lemma univItr_one (a : α (n + 1)) : ∀^[1] a = ∀' a := rfl

lemma univItr_succ {k} (a : α (n + (k + 1))) : ∀^[k + 1] a = ∀^[k] (∀' a) := rfl

end UnivQuantifier

section ExQuantifier

variable {α : ℕ → Type*} [ExQuantifier α]

def exClosure : {n : ℕ} → α n → α 0
  | 0,     a => a
  | _ + 1, a => exClosure (∃' a)

prefix:64 "∃* " => exClosure

@[simp] lemma exClosure_zero (a : α 0) : ∃* a = a := rfl

lemma exClosure_succ {n} (a : α (n + 1)) : ∃* a = ∃* ∃' a := rfl

def exItr : (k : ℕ) → α (n + k) → α n
  | 0,     a => a
  | k + 1, a => exItr k (∃' a)

notation "∃^[" k "] " φ:64 => exItr k φ

@[simp] lemma exItr_zero (a : α n) : ∃^[0] a = a := rfl

@[simp] lemma exItr_one (a : α (n + 1)) : ∃^[1] a = ∃' a := rfl

lemma exItr_succ {k} (a : α (n + (k + 1))) : ∃^[k + 1] a = ∃^[k] (∃' a) := rfl

end ExQuantifier

section quantifier

variable {α : ℕ → Type*}

def ball [UnivQuantifier α] [Arrow (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) : α n := ∀' (φ ➝ ψ)

def bex [ExQuantifier α] [Wedge (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) : α n := ∃' (φ ⋏ ψ)

notation:64 "∀[" φ "] " ψ => ball φ ψ

notation:64 "∃[" φ "] " ψ => bex φ ψ

end quantifier

end LO
end
