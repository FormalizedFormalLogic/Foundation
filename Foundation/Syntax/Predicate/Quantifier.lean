module

public import Foundation.Logic.LogicSymbol

@[expose] public section

namespace LO

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

/-! ## First-order quantifiers -/

namespace FirstOrder

class UnivQuantifier (α : ℕ → Type*) where
  all : α (n + 1) → α n

prefix:64 "∀⁰ " => UnivQuantifier.all

class ExsQuantifier (α : ℕ → Type*) where
  exs : α (n + 1) → α n

prefix:64 "∃⁰ " => ExsQuantifier.exs

attribute [match_pattern] UnivQuantifier.all ExsQuantifier.exs

class Quantifier (α : ℕ → Type*) extends UnivQuantifier α, ExsQuantifier α

/-- Logical Connectives with Quantifiers. -/
class LCWQ (α : ℕ → Type*) extends Quantifier α where
  connectives : (n : ℕ) → LogicalConnective (α n)

instance (α : ℕ → Type*) [LCWQ α] (n : ℕ) : LogicalConnective (α n) := LCWQ.connectives n

instance (α : ℕ → Type*) [Quantifier α] [(n : ℕ) → LogicalConnective (α n)] : LCWQ α where
  connectives := inferInstance

section UnivQuantifier

variable {α : ℕ → Type*} [UnivQuantifier α]

def allClosure : {n : ℕ} → α n → α 0
  |     0, a => a
  | _ + 1, a => allClosure (∀⁰ a)

/--
The universal closure of a formula.
-/
prefix:64 "∀⁰* " => allClosure

@[simp] lemma allClosure_zero (a : α 0) : ∀⁰* a = a := rfl

lemma allClosure_succ {n} (a : α (n + 1)) : ∀⁰* a = ∀⁰* ∀⁰ a := rfl

def allItr : (k : ℕ) → α (n + k) → α n
  |     0, a => a
  | k + 1, a => allItr k (∀⁰ a)

notation "∀⁰^[" k "] " φ:64 => allItr k φ

@[simp] lemma allItr_zero (a : α n) : ∀⁰^[0] a = a := rfl

@[simp] lemma allItr_one (a : α (n + 1)) : ∀⁰^[1] a = ∀⁰ a := rfl

lemma allItr_succ {k} (a : α (n + (k + 1))) : ∀⁰^[k + 1] a = ∀⁰^[k] (∀⁰ a) := rfl

end UnivQuantifier

section ExsQuantifier

variable {α : ℕ → Type*} [ExsQuantifier α]

def exsClosure : {n : ℕ} → α n → α 0
  |     0, a => a
  | _ + 1, a => exsClosure (∃⁰ a)

/--
The existential closure of a formula.
-/
prefix:64 "∃⁰* " => exsClosure

@[simp] lemma exsClosure_zero (a : α 0) : ∃⁰* a = a := rfl

lemma exsClosure_succ {n} (a : α (n + 1)) : ∃⁰* a = ∃⁰* ∃⁰ a := rfl

def exsItr : (k : ℕ) → α (n + k) → α n
  |     0, a => a
  | k + 1, a => exsItr k (∃⁰ a)

notation "∃⁰^[" k "] " φ:64 => exsItr k φ

@[simp] lemma exsItr_zero (a : α n) : ∃⁰^[0] a = a := rfl

@[simp] lemma exsItr_one (a : α (n + 1)) : ∃⁰^[1] a = ∃⁰ a := rfl

lemma exsItr_succ {k} (a : α (n + (k + 1))) : ∃⁰^[k + 1] a = ∃⁰^[k] (∃⁰ a) := rfl

end ExsQuantifier

section quantifier

variable {α : ℕ → Type*}

def ball [UnivQuantifier α] [Arrow (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) : α n := ∀⁰ (φ 🡒 ψ)

def bexs [ExsQuantifier α] [Wedge (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) : α n := ∃⁰ (φ ⋏ ψ)

notation:64 "∀⁰[" φ "] " ψ => ball φ ψ

notation:64 "∃⁰[" φ "] " ψ => bexs φ ψ

end quantifier

end FirstOrder

/-! ## Second-order quantifiers -/

namespace SecondOrder

class UnivQuantifier (α : ℕ → ℕ → Type*) where
  all₁ : α (m + 1) n → α m n

prefix:64 "∀¹ " => UnivQuantifier.all₁

class ExsQuantifier (α : ℕ → ℕ → Type*) where
  exs₁ : α (m + 1) n → α m n

prefix:64 "∃¹ " => ExsQuantifier.exs₁

attribute [match_pattern] UnivQuantifier.all₁ ExsQuantifier.exs₁

class Quantifier (α : ℕ → ℕ → Type*) extends UnivQuantifier α, ExsQuantifier α

/-- Logical Connectives with Quantifiers. -/
class LCWQ (α : ℕ → ℕ → Type*) extends Quantifier α where
  firstOrder : (m : ℕ) → FirstOrder.LCWQ (α m)

instance (α : ℕ → ℕ → Type*) [LCWQ α] (m : ℕ) : FirstOrder.LCWQ (α m) := LCWQ.firstOrder m

instance (α : ℕ → ℕ → Type*) [Quantifier α] [(m : ℕ) → FirstOrder.LCWQ (α m)] : LCWQ α where
  firstOrder := inferInstance

section UnivQuantifier

variable {α : ℕ → ℕ → Type*} [UnivQuantifier α]

def allClosure : {m : ℕ} → α m n → α 0 n
  |     0, a => a
  | _ + 1, a => allClosure (∀¹ a)

prefix:64 "∀¹* " => allClosure

@[simp] lemma allClosure_zero (a : α 0 n) : ∀¹* a = a := rfl

lemma allClosure_succ {n} (a : α (n + 1) n) : ∀¹* a = ∀¹* ∀¹ a := rfl

def allItr : (k : ℕ) → α (m + k) n → α m n
  |     0, a => a
  | k + 1, a => allItr k (∀¹ a)

notation "∀¹^[" k "] " φ:64 => allItr k φ

@[simp] lemma allItr_zero (a : α m n) : ∀¹^[0] a = a := rfl

@[simp] lemma allItr_one (a : α (m + 1) n) : ∀¹^[1] a = ∀¹ a := rfl

lemma allItr_succ {k} (a : α (m + (k + 1)) n) : ∀¹^[k + 1] a = ∀¹^[k] (∀¹ a) := rfl

end UnivQuantifier

section ExsQuantifier

variable {α : ℕ → ℕ → Type*} [ExsQuantifier α]

def exsClosure : {m : ℕ} → α m n → α 0 n
  |     0, a => a
  | _ + 1, a => exsClosure (∃¹ a)

prefix:64 "∃¹* " => exsClosure

@[simp] lemma exsClosure_zero (a : α 0 n) : ∃¹* a = a := rfl

lemma exsClosure_succ {n} (a : α (m + 1) n) : ∃¹* a = ∃¹* ∃¹ a := rfl

def exsItr : (k : ℕ) → α (m + k) n → α m n
  |     0, a => a
  | k + 1, a => exsItr k (∃¹ a)

notation "∃¹^[" k "] " φ:64 => exsItr k φ

@[simp] lemma exsItr_zero (a : α m n) : ∃¹^[0] a = a := rfl

@[simp] lemma exsItr_one (a : α (m + 1) n) : ∃¹^[1] a = ∃¹ a := rfl

lemma exsItr_succ {k} (a : α (m + (k + 1)) n) : ∃¹^[k + 1] a = ∃¹^[k] (∃¹ a) := rfl

end ExsQuantifier

section quantifier

variable {α : ℕ → ℕ → Type*}

def ball [UnivQuantifier α] [Arrow (α (m + 1) n)] (φ : α (m + 1) n) (ψ : α (m + 1) n) : α m n := ∀¹ (φ 🡒 ψ)

def bexs [ExsQuantifier α] [Wedge (α (m + 1) n)] (φ : α (m + 1) n) (ψ : α (m + 1) n) : α m n := ∃¹ (φ ⋏ ψ)

notation:64 "∀¹[" φ "] " ψ => ball φ ψ

notation:64 "∃¹[" φ "] " ψ => bexs φ ψ

end quantifier

end SecondOrder

end LO

end
