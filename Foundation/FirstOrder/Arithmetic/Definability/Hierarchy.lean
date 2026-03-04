module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

@[expose] public section
/-!

# Arithmetical Formula Sorted by Arithmetical Hierarchy

This file defines the $\Sigma_n / \Pi_n / \Delta_n$ formulas of arithmetic of first-order logic.

- `𝚺-[m].Semiformula ξ n` is a `ArithmeticSemiformula ξ n` which is `𝚺-[m]`.
- `𝚷-[m].Semiformula ξ n` is a `ArithmeticSemiformula ξ n` which is `𝚷-[m]`.
- `𝚫-[m].Semiformula ξ n` is a pair of `𝚺-[m].Semiformula ξ n` and `𝚷-[m].Semiformula ξ n`.
- `ProperOn` : `φ.ProperOn M` iff `φ`'s two element `φ.sigma` and `φ.pi` are equivalent on model `M`.

-/

namespace LO.FirstOrder.Arithmetic

structure HierarchySymbol where
  Γ : SigmaPiDelta
  rank : ℕ

scoped notation:max Γ:max "-[" n "]" => HierarchySymbol.mk Γ n

abbrev HierarchySymbol.sigmaZero : HierarchySymbol := 𝚺-[0]

abbrev HierarchySymbol.piZero : HierarchySymbol := 𝚷-[0]

abbrev HierarchySymbol.deltaZero : HierarchySymbol := 𝚫-[0]

abbrev HierarchySymbol.sigmaOne : HierarchySymbol := 𝚺-[1]

abbrev HierarchySymbol.piOne : HierarchySymbol := 𝚷-[1]

abbrev HierarchySymbol.deltaOne : HierarchySymbol := 𝚫-[1]

notation "𝚺₀" => HierarchySymbol.sigmaZero

notation "𝚷₀" => HierarchySymbol.piZero

notation "𝚫₀" => HierarchySymbol.deltaZero

notation "𝚺₁" => HierarchySymbol.sigmaOne

notation "𝚷₁" => HierarchySymbol.piOne

notation "𝚫₁" => HierarchySymbol.deltaOne

namespace HierarchySymbol

variable (ξ : Type*) (n : ℕ)

protected inductive Semiformula : HierarchySymbol → Type _ where
  | mkSigma {m} (φ : ArithmeticSemiformula ξ n) (hφ : Hierarchy 𝚺 m φ := by simp) : 𝚺-[m].Semiformula
  | mkPi {m} (φ : ArithmeticSemiformula ξ n) (hφ : Hierarchy 𝚷 m φ := by simp) : 𝚷-[m].Semiformula
  | mkDelta {m} : 𝚺-[m].Semiformula → 𝚷-[m].Semiformula → 𝚫-[m].Semiformula

protected abbrev Semisentence (Γ : HierarchySymbol) (n : ℕ) := Γ.Semiformula Empty n

protected abbrev Sentence (Γ : HierarchySymbol) := Γ.Semiformula Empty 0

variable {Γ : HierarchySymbol}

variable {ξ n}

namespace Semiformula

@[coe] def val {Γ : HierarchySymbol} : Γ.Semiformula ξ n → ArithmeticSemiformula ξ n
  | mkSigma φ _ => φ
  | mkPi    φ _ => φ
  | mkDelta φ _ => φ.val

@[simp] lemma val_mkSigma (φ : ArithmeticSemiformula ξ n) (hp : Hierarchy 𝚺 m φ) : (mkSigma φ hp).val = φ := rfl

@[simp] lemma val_mkPi (φ : ArithmeticSemiformula ξ n) (hp : Hierarchy 𝚷 m φ) : (mkPi φ hp).val = φ := rfl

@[simp] lemma val_mkDelta (φ : 𝚺-[m].Semiformula ξ n) (ψ : 𝚷-[m].Semiformula ξ n) : (mkDelta φ ψ).val = φ.val := rfl

instance : Coe (𝚺₀.Semisentence n) (ArithmeticSemisentence n) := ⟨Semiformula.val⟩
instance : Coe (𝚷₀.Semisentence n) (ArithmeticSemisentence n) := ⟨Semiformula.val⟩
instance : Coe (𝚫₀.Semisentence n) (ArithmeticSemisentence n) := ⟨Semiformula.val⟩

instance : Coe (𝚺₁.Semisentence n) (ArithmeticSemisentence n) := ⟨Semiformula.val⟩
instance : Coe (𝚷₁.Semisentence n) (ArithmeticSemisentence n) := ⟨Semiformula.val⟩
instance : Coe (𝚫₁.Semisentence n) (ArithmeticSemisentence n) := ⟨Semiformula.val⟩

@[simp] lemma sigma_prop : (φ : 𝚺-[m].Semiformula ξ n) → Hierarchy 𝚺 m φ.val
  | mkSigma _ h => h

@[simp] lemma pi_prop : (φ : 𝚷-[m].Semiformula ξ n) → Hierarchy 𝚷 m φ.val
  | mkPi _ h => h

@[simp] lemma polarity_prop : {Γ : Polarity} → (φ : Γ-[m].Semiformula ξ n) → Hierarchy Γ m φ.val
  | 𝚺, φ => φ.sigma_prop
  | 𝚷, φ => φ.pi_prop

def sigma : 𝚫-[m].Semiformula ξ n → 𝚺-[m].Semiformula ξ n
  | mkDelta φ _ => φ

@[simp] lemma sigma_mkDelta (φ : 𝚺-[m].Semiformula ξ n) (ψ : 𝚷-[m].Semiformula ξ n) : (mkDelta φ ψ).sigma = φ := rfl

def pi : 𝚫-[m].Semiformula ξ n → 𝚷-[m].Semiformula ξ n
  | mkDelta _ φ => φ

@[simp] lemma pi_mkDelta (φ : 𝚺-[m].Semiformula ξ n) (ψ : 𝚷-[m].Semiformula ξ n) : (mkDelta φ ψ).pi = ψ := rfl

lemma val_sigma (φ : 𝚫-[m].Semiformula ξ n) : φ.sigma.val = φ.val := by rcases φ; simp

def mkPolarity (φ : ArithmeticSemiformula ξ n) : (Γ : Polarity) → Hierarchy Γ m φ → Γ-[m].Semiformula ξ n
  | 𝚺, h => mkSigma φ h
  | 𝚷, h => mkPi φ h

@[simp] lemma val_mkPolarity (φ : ArithmeticSemiformula ξ n) {Γ} (h : Hierarchy Γ m φ) : (mkPolarity φ Γ h).val = φ := by cases Γ <;> rfl

@[simp] lemma hierarchy_sigma (φ : 𝚺-[m].Semiformula ξ n) : Hierarchy 𝚺 m φ.val := φ.sigma_prop

@[simp] lemma hierarchy_pi (φ : 𝚷-[m].Semiformula ξ n) : Hierarchy 𝚷 m φ.val := φ.pi_prop

@[simp] lemma hierarchy_zero {Γ Γ' m} (φ : Γ-[0].Semiformula ξ n) : Hierarchy Γ' m φ.val := by
  cases Γ
  · exact Hierarchy.of_zero φ.sigma_prop
  · exact Hierarchy.of_zero φ.pi_prop
  · cases φ
    simpa using Hierarchy.of_zero (sigma_prop _)

variable {M : Type*} [ORingStructure M]

variable (M)

def ProperOn (φ : 𝚫-[m].Semisentence n) : Prop :=
  ∀ (e : Fin n → M), Semiformula.Evalbm M e φ.sigma.val ↔ Semiformula.Evalbm M e φ.pi.val

def ProperWithParamOn (φ : 𝚫-[m].Semiformula M n) : Prop :=
  ∀ (e : Fin n → M), Semiformula.Evalm M e id φ.sigma.val ↔ Semiformula.Evalm M e id φ.pi.val

def ProvablyProperOn (φ : 𝚫-[m].Semisentence n) (T : ArithmeticTheory) : Prop :=
  T ⊢ ∀⁰* “!φ.sigma.val ⋯ ↔ !φ.pi.val ⋯”

variable {M}

lemma ProperOn.iff {φ : 𝚫-[m].Semisentence n}
    (h : φ.ProperOn M) (e : Fin n → M) :
    Semiformula.Evalbm M e φ.sigma.val ↔ Semiformula.Evalbm M e φ.pi.val := h e

lemma ProperWithParamOn.iff {φ : 𝚫-[m].Semiformula M n}
    (h : φ.ProperWithParamOn M) (e : Fin n → M) :
    Semiformula.Evalm M e id φ.sigma.val ↔ Semiformula.Evalm (L := ℒₒᵣ) M e id φ.pi.val := h e

lemma ProperOn.iff' {φ : 𝚫-[m].Semisentence n}
    (h : φ.ProperOn M) (e : Fin n → M) :
    Semiformula.Evalbm M e φ.pi.val ↔ Semiformula.Evalbm M e φ.val := by simp [←h.iff, val_sigma]

lemma ProperWithParamOn.iff' {φ : 𝚫-[m].Semiformula M n}
    (h : φ.ProperWithParamOn M) (e : Fin n → M) :
    Semiformula.Evalm M e id φ.pi.val ↔ Semiformula.Evalm (L := ℒₒᵣ) M e id φ.val := by simp [←h.iff, val_sigma]

inductive ProvablyProperOn' (T : ArithmeticTheory) : {Γ : HierarchySymbol} → {n : ℕ} → (φ : Γ.Semisentence n) → Prop
  | sigma (φ : 𝚺-[m].Semisentence n) : φ.ProvablyProperOn' T
  | pi (φ : 𝚷-[m].Semisentence n) : φ.ProvablyProperOn' T
  | delta (φ : 𝚫-[m].Semisentence n) : φ.ProvablyProperOn T → φ.ProvablyProperOn' T

section ProvablyProperOn

variable (T : ArithmeticTheory)

lemma ProvablyProperOn.ofProperOn [𝗘𝗤 ⪯ T] {φ : 𝚫-[m].Semisentence n}
    (h : ∀ (M : Type w) [ORingStructure M] [M ⊧ₘ* T], φ.ProperOn M) : φ.ProvablyProperOn T := by
  apply FirstOrder.Arithmetic.provable_of_models.{w} T _ ?_
  intro M _ _
  simpa [models_iff] using (h M).iff

variable {T}

lemma ProvablyProperOn.properOn
    {φ : 𝚫-[m].Semisentence n} (h : φ.ProvablyProperOn T)
    (M : Type w) [ORingStructure M] [M ⊧ₘ* T] : φ.ProperOn M := by
  intro v
  have := by simpa [models_iff] using consequence_iff.mp (sound! h) M inferInstance
  exact this v

end ProvablyProperOn

def rew (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) : {Γ : HierarchySymbol} → Γ.Semiformula ξ₁ n₁ → Γ.Semiformula ξ₂ n₂
  | 𝚺-[_], mkSigma φ hp => mkSigma (ω ▹ φ) (by simpa using hp)
  | 𝚷-[_], mkPi φ hp    => mkPi (ω ▹ φ) (by simpa using hp)
  | 𝚫-[_], mkDelta φ ψ  => mkDelta (φ.rew ω) (ψ.rew ω)

@[simp] lemma val_rew (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) {Γ : HierarchySymbol} (φ : Γ.Semiformula ξ₁ n₁) : (φ.rew ω).val = ω ▹ φ.val := by
  rcases Γ with ⟨Γ, m⟩; rcases φ with (_ | _ | ⟨⟨p, _⟩, ⟨q, _⟩⟩) <;> simp [rew]

@[simp] lemma ProperOn.rew {φ : 𝚫-[m].Semisentence n₁} (h : φ.ProperOn M) (ω : Rew ℒₒᵣ Empty n₁ Empty n₂) : (φ.rew ω).ProperOn M := by
  rcases φ; simp only [ProperOn, Semiformula.rew, sigma_mkDelta, val_rew, Semiformula.eval_rew, Empty.eq_elim, pi_mkDelta]
  intro e; exact h.iff _

@[simp] lemma ProperOn.rew' {φ : 𝚫-[m].Semisentence n₁} (h : φ.ProperOn M) (ω : Rew ℒₒᵣ Empty n₁ M n₂) : (φ.rew ω).ProperWithParamOn M := by
  rcases φ; intro e; simp [Semiformula.rew, Semiformula.eval_rew, Empty.eq_elim]
  simpa using h.iff _

@[simp] lemma ProperWithParamOn.rew {φ : 𝚫-[m].Semiformula M n₁}
    (h : φ.ProperWithParamOn M) (f : Fin n₁ → ArithmeticSemiterm M n₂) : (φ.rew (Rew.subst f)).ProperWithParamOn M := by
  rcases φ; intro e;
  simp only [Semiformula.rew, sigma_mkDelta, val_rew, Semiformula.eval_rew, pi_mkDelta]
  exact h.iff _

lemma sigmaZero {Γ} (φ : Γ-[0].Semiformula ξ k) : Hierarchy 𝚺 0 φ.val :=
  match Γ with
  | 𝚺 => φ.sigma_prop
  | 𝚷 => φ.pi_prop.of_zero
  | 𝚫 => by simp

def ofZero {Γ'} (φ : Γ'-[0].Semiformula ξ k) : (Γ : HierarchySymbol) → Γ.Semiformula ξ k
  | 𝚺-[_] => mkSigma φ.val φ.sigmaZero.of_zero
  | 𝚷-[_] => mkPi φ.val φ.sigmaZero.of_zero
  | 𝚫-[_] => mkDelta (mkSigma φ.val φ.sigmaZero.of_zero) (mkPi φ.val φ.sigmaZero.of_zero)

def ofDeltaOne (φ : 𝚫₁.Semiformula ξ k) : (Γ : SigmaPiDelta) → (m : ℕ) → Γ-[m+1].Semiformula ξ k
  | 𝚺, m => mkSigma φ.sigma.val (φ.sigma.sigma_prop.mono (by simp))
  | 𝚷, m => mkPi φ.pi.val (φ.pi.pi_prop.mono (by simp))
  | 𝚫, m => mkDelta (mkSigma φ.sigma.val (φ.sigma.sigma_prop.mono (by simp))) (mkPi φ.pi.val (φ.pi.pi_prop.mono (by simp)))

@[simp] lemma ofZero_val {Γ'} (φ : Γ'-[0].Semiformula ξ n) (Γ) : (ofZero φ Γ).val = φ.val := by
  match Γ with
  | 𝚺-[_] => simp [ofZero]
  | 𝚷-[_] => simp [ofZero]
  | 𝚫-[_] => simp [ofZero]

@[simp] lemma ProperOn.of_zero (φ : Γ'-[0].Semisentence k) (m) : (ofZero φ 𝚫-[m]).ProperOn M := by
  simp [ProperOn, ofZero]

@[simp] lemma ProperWithParamOn.of_zero (φ : Γ'-[0].Semiformula M k) (m) : (ofZero φ 𝚫-[m]).ProperWithParamOn M := by
  simp [ProperWithParamOn, ofZero]

def verum : {Γ : HierarchySymbol} → Γ.Semiformula ξ n
  | 𝚺-[m] => mkSigma ⊤ (by simp)
  | 𝚷-[m] => mkPi ⊤ (by simp)
  | 𝚫-[m] => mkDelta (mkSigma ⊤ (by simp)) (mkPi ⊤ (by simp))

def falsum : {Γ : HierarchySymbol} → Γ.Semiformula ξ n
  | 𝚺-[m] => mkSigma ⊥ (by simp)
  | 𝚷-[m] => mkPi ⊥ (by simp)
  | 𝚫-[m] => mkDelta (mkSigma ⊥ (by simp)) (mkPi ⊥ (by simp))

def and : {Γ : HierarchySymbol} → Γ.Semiformula ξ n → Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | 𝚺-[m], φ, ψ => mkSigma (φ.val ⋏ ψ.val) (by simp)
  | 𝚷-[m], φ, ψ => mkPi (φ.val ⋏ ψ.val) (by simp)
  | 𝚫-[m], φ, ψ => mkDelta (mkSigma (φ.sigma.val ⋏ ψ.sigma.val) (by simp)) (mkPi (φ.pi.val ⋏ ψ.pi.val) (by simp))

def or : {Γ : HierarchySymbol} → Γ.Semiformula ξ n → Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | 𝚺-[m], φ, ψ => mkSigma (φ.val ⋎ ψ.val) (by simp)
  | 𝚷-[m], φ, ψ => mkPi (φ.val ⋎ ψ.val) (by simp)
  | 𝚫-[m], φ, ψ => mkDelta (mkSigma (φ.sigma.val ⋎ ψ.sigma.val) (by simp)) (mkPi (φ.pi.val ⋎ ψ.pi.val) (by simp))

def negSigma (φ : 𝚺-[m].Semiformula ξ n) : 𝚷-[m].Semiformula ξ n := mkPi (∼φ.val) (by simp)

def negPi (φ : 𝚷-[m].Semiformula ξ n) : 𝚺-[m].Semiformula ξ n := mkSigma (∼φ.val) (by simp)

def negDelta (φ : 𝚫-[m].Semiformula ξ n) : 𝚫-[m].Semiformula ξ n := mkDelta (φ.pi.negPi) (φ.sigma.negSigma)

def ball (t : ArithmeticSemiterm ξ n) : {Γ : HierarchySymbol} → Γ.Semiformula ξ (n + 1) → Γ.Semiformula ξ n
  | 𝚺-[m], φ => mkSigma (∀⁰[“#0 < !!(Rew.bShift t)”] φ.val) (by simp)
  | 𝚷-[m], φ => mkPi (∀⁰[“#0 < !!(Rew.bShift t)”] φ.val) (by simp)
  | 𝚫-[m], φ =>
    mkDelta (mkSigma (∀⁰[“#0 < !!(Rew.bShift t)”] φ.sigma.val) (by simp)) (mkPi (∀⁰[“#0 < !!(Rew.bShift t)”] φ.pi.val) (by simp))

def bexs (t : ArithmeticSemiterm ξ n) : {Γ : HierarchySymbol} → Γ.Semiformula ξ (n + 1) → Γ.Semiformula ξ n
  | 𝚺-[m], φ => mkSigma (∃⁰[“#0 < !!(Rew.bShift t)”] φ.val) (by simp)
  | 𝚷-[m], φ => mkPi (∃⁰[“#0 < !!(Rew.bShift t)”] φ.val) (by simp)
  | 𝚫-[m], φ =>
    mkDelta (mkSigma (∃⁰[“#0 < !!(Rew.bShift t)”] φ.sigma.val) (by simp)) (mkPi (∃⁰[“#0 < !!(Rew.bShift t)”] φ.pi.val) (by simp))

def all (φ : 𝚷-[m + 1].Semiformula ξ (n + 1)) : 𝚷-[m + 1].Semiformula ξ n := mkPi (∀⁰ φ.val) φ.pi_prop.all

def exs (φ : 𝚺-[m + 1].Semiformula ξ (n + 1)) : 𝚺-[m + 1].Semiformula ξ n := mkSigma (∃⁰ φ.val) φ.sigma_prop.exs

instance : Top (Γ.Semiformula ξ n) := ⟨verum⟩

instance : Bot (Γ.Semiformula ξ n) := ⟨falsum⟩

instance : Wedge (Γ.Semiformula ξ n) := ⟨and⟩

instance : Vee (Γ.Semiformula ξ n) := ⟨or⟩

instance : Tilde (𝚫-[m].Semiformula ξ n) := ⟨negDelta⟩

instance : LogicalConnective (𝚫-[m].Semiformula ξ n) where
  arrow φ ψ := ∼φ ⋎ ψ

instance : ExsQuantifier (𝚺-[m + 1].Semiformula ξ) := ⟨exs⟩

instance : UnivQuantifier (𝚷-[m + 1].Semiformula ξ) := ⟨all⟩

def substSigma (φ : 𝚺-[m + 1].Semiformula ξ 1) (F : 𝚺-[m + 1].Semiformula ξ (n + 1)) :
    𝚺-[m + 1].Semiformula ξ n := (F ⋏ φ.rew (Rew.subst ![#0])).exs

@[simp] lemma val_verum : (⊤ : Γ.Semiformula ξ n).val = ⊤ := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp <;> rfl

@[simp] lemma sigma_verum {m} : (⊤ : 𝚫-[m].Semiformula ξ n).sigma = ⊤ := by simp [Top.top, verum]

@[simp] lemma pi_verum {m} : (⊤ : 𝚫-[m].Semiformula ξ n).pi = ⊤ := by simp [Top.top, verum]

@[simp] lemma val_falsum : (⊥ : Γ.Semiformula ξ n).val = ⊥ := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp <;> rfl

@[simp] lemma sigma_falsum {m} : (⊥ : 𝚫-[m].Semiformula ξ n).sigma = ⊥ := by simp [Bot.bot, falsum]

@[simp] lemma pi_falsum {m} : (⊥ : 𝚫-[m].Semiformula ξ n).pi = ⊥ := by simp [Bot.bot, falsum]

@[simp] lemma val_and (φ ψ : Γ.Semiformula ξ n) : (φ ⋏ ψ).val = φ.val ⋏ ψ.val := by
  suffices (φ.and ψ).val = φ.val ⋏ ψ.val from this
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [and, val, val_sigma]

@[simp] lemma sigma_and (φ ψ : 𝚫-[m].Semiformula ξ n) : (φ ⋏ ψ).sigma = φ.sigma ⋏ ψ.sigma := by simp [Wedge.wedge, and]

@[simp] lemma pi_and (φ ψ : 𝚫-[m].Semiformula ξ n) : (φ ⋏ ψ).pi = φ.pi ⋏ ψ.pi := by simp [Wedge.wedge, and]

@[simp] lemma val_or (φ ψ : Γ.Semiformula ξ n) : (φ ⋎ ψ).val = φ.val ⋎ ψ.val := by
  suffices (φ.or ψ).val = φ.val ⋎ ψ.val from this
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [or, val, val_sigma]

@[simp] lemma sigma_or (φ ψ : 𝚫-[m].Semiformula ξ n) : (φ ⋎ ψ).sigma = φ.sigma ⋎ ψ.sigma := by simp [Vee.vee, or]

@[simp] lemma pi_or (φ ψ : 𝚫-[m].Semiformula ξ n) : (φ ⋎ ψ).pi = φ.pi ⋎ ψ.pi := by simp [Vee.vee, or]

@[simp] lemma val_negSigma {m} (φ : 𝚺-[m].Semiformula ξ n) : φ.negSigma.val = ∼φ.val := by simp [negSigma]

@[simp] lemma val_negPi {m} (φ : 𝚷-[m].Semiformula ξ n) : φ.negPi.val = ∼φ.val := by simp [negPi]

lemma val_negDelta {m} (φ : 𝚫-[m].Semiformula ξ n) : (∼φ).val = ∼φ.pi.val := by simp [Tilde.tilde, negDelta]

@[simp] lemma sigma_negDelta {m} (φ : 𝚫-[m].Semiformula ξ n) : (∼φ).sigma = φ.pi.negPi := by simp [Tilde.tilde, negDelta]

@[simp] lemma sigma_negPi {m} (φ : 𝚫-[m].Semiformula ξ n) : (∼φ).pi = φ.sigma.negSigma := by simp [Tilde.tilde, negDelta]

@[simp] lemma val_ball (t : ArithmeticSemiterm ξ n) (φ : Γ.Semiformula ξ (n + 1)) : (ball t φ).val = ∀⁰[“#0 < !!(Rew.bShift t)”] φ.val := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [ball, val, val_sigma]

@[simp] lemma val_bexs (t : ArithmeticSemiterm ξ n) (φ : Γ.Semiformula ξ (n + 1)) : (bexs t φ).val = ∃⁰[“#0 < !!(Rew.bShift t)”] φ.val := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [bexs, val, val_sigma]

@[simp] lemma val_exsSigma {m} (φ : 𝚺-[m + 1].Semiformula ξ (n + 1)) : (exs φ).val = ∃⁰ φ.val := rfl

@[simp] lemma val_allPi {m} (φ : 𝚷-[m + 1].Semiformula ξ (n + 1)) : (all φ).val = ∀⁰ φ.val := rfl

@[simp] lemma ProperOn.verum : (⊤ : 𝚫-[m].Semisentence k).ProperOn M := by intro e; simp

@[simp] lemma ProperOn.falsum : (⊥ : 𝚫-[m].Semisentence k).ProperOn M := by intro e; simp

lemma ProperOn.and {φ ψ : 𝚫-[m].Semisentence k} (hp : φ.ProperOn M) (hq : ψ.ProperOn M) : (φ ⋏ ψ).ProperOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperOn.or {φ ψ : 𝚫-[m].Semisentence k} (hp : φ.ProperOn M) (hq : ψ.ProperOn M) : (φ ⋎ ψ).ProperOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperOn.neg {φ : 𝚫-[m].Semisentence k} (hp : φ.ProperOn M) : (∼φ).ProperOn M := by
  intro e; simp [hp.iff]

lemma ProperOn.eval_neg {φ : 𝚫-[m].Semisentence k} (hp : φ.ProperOn M) (e) :
    Semiformula.Evalbm M e (∼φ).val ↔ ¬Semiformula.Evalbm M e φ.val := by
  simp [←val_sigma, hp.iff]

lemma ProperOn.ball {t} {φ : 𝚫-[m + 1].Semisentence (k + 1)} (hp : φ.ProperOn M) : (ball t φ).ProperOn M := by
  intro e; simp [Semiformula.ball, hp.iff]

lemma ProperOn.bexs {t} {φ : 𝚫-[m + 1].Semisentence (k + 1)} (hp : φ.ProperOn M) : (bexs t φ).ProperOn M := by
  intro e; simp [Semiformula.bexs, hp.iff]

@[simp] lemma ProperWithParamOn.verum : (⊤ : 𝚫-[m].Semiformula M k).ProperWithParamOn M := by intro e; simp

@[simp] lemma ProperWithParamOn.falsum : (⊥ : 𝚫-[m].Semiformula M k).ProperWithParamOn M := by intro e; simp

lemma ProperWithParamOn.and {φ ψ : 𝚫-[m].Semiformula M k}
    (hp : φ.ProperWithParamOn M) (hq : ψ.ProperWithParamOn M) : (φ ⋏ ψ).ProperWithParamOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperWithParamOn.or {φ ψ : 𝚫-[m].Semiformula M k}
    (hp : φ.ProperWithParamOn M) (hq : ψ.ProperWithParamOn M) : (φ ⋎ ψ).ProperWithParamOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperWithParamOn.neg {φ : 𝚫-[m].Semiformula M k} (hp : φ.ProperWithParamOn M) : (∼φ).ProperWithParamOn M := by
  intro e; simp [hp.iff]

lemma ProperWithParamOn.eval_neg {φ : 𝚫-[m].Semiformula M k} (hp : φ.ProperWithParamOn M) (e) :
    Semiformula.Evalm M e id (∼φ).val ↔ ¬Semiformula.Evalm M e id φ.val := by
  simp [←val_sigma, hp.iff]

lemma ProperWithParamOn.ball {t} {φ : 𝚫-[m].Semiformula M (k + 1)}
    (hp : φ.ProperWithParamOn M) : (ball t φ).ProperWithParamOn M := by
  intro e; simp [Semiformula.ball, hp.iff]

lemma ProperWithParamOn.bexs {t} {φ : 𝚫-[m].Semiformula M (k + 1)}
    (hp : φ.ProperWithParamOn M) : (bexs t φ).ProperWithParamOn M := by
  intro e; simp [Semiformula.bexs, hp.iff]

def graphDelta (φ : 𝚺-[m].Semiformula ξ (k + 1)) : 𝚫-[m].Semiformula ξ (k + 1) :=
  match m with
  | 0     => φ.ofZero _
  | m + 1 => mkDelta φ (mkPi “x. ∀ y, !φ.val y ⋯ → y = x”)

@[simp] lemma graphDelta_val (φ : 𝚺-[m].Semiformula ξ (k + 1)) : φ.graphDelta.val = φ.val := by cases m <;> simp [graphDelta]

end Semiformula

end HierarchySymbol

end LO.FirstOrder.Arithmetic
