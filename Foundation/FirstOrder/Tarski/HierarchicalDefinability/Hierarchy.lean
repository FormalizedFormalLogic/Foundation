module

public import Foundation.FirstOrder.Syntax.Classical.BoundingHierarchy
public import Foundation.FirstOrder.Tarski.Definability
public import Foundation.FirstOrder.LK.Soundness

/-!
# Formulas sorted by a bounding hierarchy

This generalizes the arithmetic hierarchy's formula wrappers to an arbitrary set of bounding
operators. Delta formulas retain separate Sigma and Pi representatives; their equivalence
is expressed by `ProperOn` or `ProperWithParamOn`.

The definitions and lemmas are technical bridges between the existing syntactic bounding
hierarchy and Tarski semantics, following the arithmetic formalization.
-/

@[expose] public section

namespace FFL.FirstOrder.Bounding

universe w

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

scoped notation "𝚺₀" => HierarchySymbol.sigmaZero

scoped notation "𝚷₀" => HierarchySymbol.piZero

scoped notation "𝚫₀" => HierarchySymbol.deltaZero

scoped notation "𝚺₁" => HierarchySymbol.sigmaOne

scoped notation "𝚷₁" => HierarchySymbol.piOne

scoped notation "𝚫₁" => HierarchySymbol.deltaOne

namespace HierarchySymbol

variable {L : Language}
variable (ℬ : FirstOrder.Bounding L)

variable (ξ : Type*) (n : ℕ)

protected inductive Semiformula : HierarchySymbol → Type _ where
  | mkSigma {m} (φ : FirstOrder.Semiformula L ξ n) (hφ : ℬ.Hierarchy 𝚺 m φ := by simp) :
    𝚺-[m].Semiformula
  | mkPi {m} (φ : FirstOrder.Semiformula L ξ n) (hφ : ℬ.Hierarchy 𝚷 m φ := by simp) :
    𝚷-[m].Semiformula
  | mkDelta {m} : 𝚺-[m].Semiformula → 𝚷-[m].Semiformula → 𝚫-[m].Semiformula

protected abbrev Semisentence (Γ : HierarchySymbol) (n : ℕ) := Γ.Semiformula ℬ Empty n

protected abbrev Sentence (Γ : HierarchySymbol) := Γ.Semiformula ℬ Empty 0

variable {Γ : HierarchySymbol}

variable {ℬ ξ n} {m k n₁ n₂ : ℕ} {ξ₁ ξ₂ : Type*} {Γ' : Polarity}

namespace Semiformula

@[coe] def val {Γ : HierarchySymbol} : Γ.Semiformula ℬ ξ n → FirstOrder.Semiformula L ξ n
  | mkSigma φ _ => φ
  | mkPi    φ _ => φ
  | mkDelta φ _ => φ.val

@[simp] lemma val_mkSigma (φ : FirstOrder.Semiformula L ξ n) (hp : ℬ.Hierarchy 𝚺 m φ) :
  (mkSigma φ hp).val = φ := rfl

@[simp] lemma val_mkPi (φ : FirstOrder.Semiformula L ξ n) (hp : ℬ.Hierarchy 𝚷 m φ) :
    (mkPi φ hp).val = φ := rfl

@[simp] lemma val_mkDelta (φ : 𝚺-[m].Semiformula ℬ ξ n) (ψ : 𝚷-[m].Semiformula ℬ ξ n) :
  (mkDelta φ ψ).val = φ.val := rfl

instance : CoeOut (𝚺₀.Semisentence ℬ n) (FirstOrder.Semisentence L n) := ⟨Semiformula.val⟩
instance : CoeOut (𝚷₀.Semisentence ℬ n) (FirstOrder.Semisentence L n) := ⟨Semiformula.val⟩
instance : CoeOut (𝚫₀.Semisentence ℬ n) (FirstOrder.Semisentence L n) := ⟨Semiformula.val⟩

instance : CoeOut (𝚺₁.Semisentence ℬ n) (FirstOrder.Semisentence L n) := ⟨Semiformula.val⟩
instance : CoeOut (𝚷₁.Semisentence ℬ n) (FirstOrder.Semisentence L n) := ⟨Semiformula.val⟩
instance : CoeOut (𝚫₁.Semisentence ℬ n) (FirstOrder.Semisentence L n) := ⟨Semiformula.val⟩

@[simp] lemma sigma_prop : (φ : 𝚺-[m].Semiformula ℬ ξ n) → ℬ.Hierarchy 𝚺 m φ.val
  | mkSigma _ h => h

@[simp] lemma pi_prop : (φ : 𝚷-[m].Semiformula ℬ ξ n) → ℬ.Hierarchy 𝚷 m φ.val
  | mkPi _ h => h

@[simp] lemma polarity_prop : {Γ : Polarity} → (φ : Γ-[m].Semiformula ℬ ξ n) → ℬ.Hierarchy Γ m φ.val
  | 𝚺, φ => φ.sigma_prop
  | 𝚷, φ => φ.pi_prop

def sigma : 𝚫-[m].Semiformula ℬ ξ n → 𝚺-[m].Semiformula ℬ ξ n
  | mkDelta φ _ => φ

@[simp] lemma sigma_mkDelta (φ : 𝚺-[m].Semiformula ℬ ξ n) (ψ : 𝚷-[m].Semiformula ℬ ξ n) :
  (mkDelta φ ψ).sigma = φ := rfl

def pi : 𝚫-[m].Semiformula ℬ ξ n → 𝚷-[m].Semiformula ℬ ξ n
  | mkDelta _ φ => φ

@[simp] lemma pi_mkDelta (φ : 𝚺-[m].Semiformula ℬ ξ n) (ψ : 𝚷-[m].Semiformula ℬ ξ n) :
  (mkDelta φ ψ).pi = ψ := rfl

lemma val_sigma (φ : 𝚫-[m].Semiformula ℬ ξ n) : φ.sigma.val = φ.val := by rcases φ; simp

def mkPolarity (φ : FirstOrder.Semiformula L ξ n) :
    (Γ : Polarity) → ℬ.Hierarchy Γ m φ → Γ-[m].Semiformula ℬ ξ n
  | 𝚺, h => mkSigma φ h
  | 𝚷, h => mkPi φ h

@[simp] lemma val_mkPolarity (φ : FirstOrder.Semiformula L ξ n) {Γ} (h : ℬ.Hierarchy Γ m φ) :
  (mkPolarity φ Γ h).val = φ := by cases Γ <;> rfl

@[simp] lemma hierarchy_sigma (φ : 𝚺-[m].Semiformula ℬ ξ n) : ℬ.Hierarchy 𝚺 m φ.val := φ.sigma_prop

@[simp] lemma hierarchy_pi (φ : 𝚷-[m].Semiformula ℬ ξ n) : ℬ.Hierarchy 𝚷 m φ.val := φ.pi_prop

@[simp] lemma hierarchy_zero {Γ Γ' m} (φ : Γ-[0].Semiformula ℬ ξ n) : ℬ.Hierarchy Γ' m φ.val := by
  cases Γ
  · exact Hierarchy.of_zero φ.sigma_prop
  · exact Hierarchy.of_zero φ.pi_prop
  · cases φ
    simpa using Hierarchy.of_zero (sigma_prop _)

lemma hierarchy_of_lt {C : HierarchySymbol} {Γ : Polarity} {s : ℕ} (φ : C.Semiformula ℬ ξ n)
    (h : C.rank < s) : ℬ.Hierarchy Γ s φ.val := by
  rcases C with ⟨_ | _ | _, m⟩
  · exact φ.sigma_prop.strict_mono _ h
  · exact φ.pi_prop.strict_mono _ h
  · exact (val_sigma φ ▸ φ.sigma.sigma_prop).strict_mono _ h

variable {M : Type*} [Tarski.Structure L M]

variable (M)

def ProperOn (φ : 𝚫-[m].Semisentence ℬ n) : Prop :=
  ∀ (e : Fin n → M), φ.sigma.val.Evalb e ↔ φ.pi.val.Evalb e

def ProperWithParamOn (φ : 𝚫-[m].Semiformula ℬ M n) : Prop :=
  ∀ (e : Fin n → M), φ.sigma.val.Eval e id ↔ φ.pi.val.Eval e id

def ProvablyProperOn (φ : 𝚫-[m].Semisentence ℬ n) (T : Theory L) : Prop :=
  T ⊢ ∀¹* “!φ.sigma.val ⋯ ↔ !φ.pi.val ⋯”

variable {M}

lemma ProperOn.iff {φ : 𝚫-[m].Semisentence ℬ n}
    (h : φ.ProperOn M) (e : Fin n → M) :
    φ.sigma.val.Evalb e ↔ φ.pi.val.Evalb e := h e

lemma ProperWithParamOn.iff {φ : 𝚫-[m].Semiformula ℬ M n}
    (h : φ.ProperWithParamOn M) (e : Fin n → M) :
    φ.sigma.val.Eval e id ↔ φ.pi.val.Eval e id := h e

lemma ProperOn.iff' {φ : 𝚫-[m].Semisentence ℬ n}
    (h : φ.ProperOn M) (e : Fin n → M) :
    φ.pi.val.Evalb e ↔ φ.val.Evalb e := by simp [←h.iff, val_sigma]

lemma ProperWithParamOn.iff' {φ : 𝚫-[m].Semiformula ℬ M n}
    (h : φ.ProperWithParamOn M) (e : Fin n → M) :
    φ.pi.val.Eval e id ↔ φ.val.Eval e id := by simp [←h.iff, val_sigma]

inductive ProvablyProperOn' (T : Theory L) : {Γ : HierarchySymbol} → {n : ℕ} →
    (φ : Γ.Semisentence ℬ n) → Prop
  | sigma (φ : 𝚺-[m].Semisentence ℬ n) : φ.ProvablyProperOn' T
  | pi (φ : 𝚷-[m].Semisentence ℬ n) : φ.ProvablyProperOn' T
  | delta (φ : 𝚫-[m].Semisentence ℬ n) : φ.ProvablyProperOn T → φ.ProvablyProperOn' T

section ProvablyProperOn

variable (T : Theory L)

variable {T}

lemma ProvablyProperOn.properOn
    {φ : 𝚫-[m].Semisentence ℬ n} (h : φ.ProvablyProperOn T)
    (M : Type w) [Nonempty M] [Tarski.Structure L M] [M↓[L] ⊧* T] : φ.ProperOn M := by
  intro v
  have := by simpa [models_iff] using consequence_iff.mp (Theory.Proof.sound h) M inferInstance
  exact this v

end ProvablyProperOn

def rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) : {Γ : HierarchySymbol} → Γ.Semiformula ℬ ξ₁ n₁ →
  Γ.Semiformula ℬ ξ₂ n₂
  | 𝚺-[_], mkSigma φ hp => mkSigma (ω ▹ φ) (hp.rew ω)
  | 𝚷-[_], mkPi φ hp    => mkPi (ω ▹ φ) (hp.rew ω)
  | 𝚫-[_], mkDelta φ ψ  => mkDelta (φ.rew ω) (ψ.rew ω)

@[simp] lemma val_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) {Γ : HierarchySymbol}
    (φ : Γ.Semiformula ℬ ξ₁ n₁) : (φ.rew ω).val = ω ▹ φ.val := by
  rcases Γ with ⟨Γ, m⟩; rcases φ with (_ | _ | ⟨⟨p, _⟩, ⟨q, _⟩⟩) <;> simp [rew]

@[simp] lemma ProperOn.rew {φ : 𝚫-[m].Semisentence ℬ n₁} (h : φ.ProperOn M)
    (ω : Rew L Empty n₁ Empty n₂) : (φ.rew ω).ProperOn M := by
  rcases φ; simp only [ProperOn, Semiformula.rew, sigma_mkDelta, val_rew, Semiformula.eval_rew,
    Empty.eq_elim, pi_mkDelta]
  intro e; exact h.iff _

@[simp] lemma ProperOn.rew' {φ : 𝚫-[m].Semisentence ℬ n₁} (h : φ.ProperOn M)
    (ω : Rew L Empty n₁ M n₂) : (φ.rew ω).ProperWithParamOn M := by
  rcases φ; intro e; simp [Semiformula.rew, Semiformula.eval_rew, Empty.eq_elim]
  simpa using h.iff _

@[simp] lemma ProperWithParamOn.rew {φ : 𝚫-[m].Semiformula ℬ M n₁}
    (h : φ.ProperWithParamOn M) (f : Fin n₁ → Semiterm L M n₂) : (φ.rew (Rew.subst
      f)).ProperWithParamOn M := by
  rcases φ; intro e
  simp only [Semiformula.rew, sigma_mkDelta, val_rew, Semiformula.eval_rew, pi_mkDelta]
  exact h.iff _

lemma sigmaZero {Γ} (φ : Γ-[0].Semiformula ℬ ξ k) : ℬ.Hierarchy 𝚺 0 φ.val :=
  match Γ with
  | 𝚺 => φ.sigma_prop
  | 𝚷 => φ.pi_prop.of_zero
  | 𝚫 => by simp

def ofZero {Γ'} (φ : Γ'-[0].Semiformula ℬ ξ k) : (Γ : HierarchySymbol) → Γ.Semiformula ℬ ξ k
  | 𝚺-[_] => mkSigma φ.val φ.sigmaZero.of_zero
  | 𝚷-[_] => mkPi φ.val φ.sigmaZero.of_zero
  | 𝚫-[_] => mkDelta (mkSigma φ.val φ.sigmaZero.of_zero) (mkPi φ.val φ.sigmaZero.of_zero)

def ofDeltaOne (φ : 𝚫₁.Semiformula ℬ ξ k) : (Γ : SigmaPiDelta) → (m : ℕ) → Γ-[m+1].Semiformula ℬ ξ k
  | 𝚺, m => mkSigma φ.sigma.val (φ.sigma.sigma_prop.mono (by simp))
  | 𝚷, m => mkPi φ.pi.val (φ.pi.pi_prop.mono (by simp))
  | 𝚫,
    m => mkDelta (mkSigma φ.sigma.val (φ.sigma.sigma_prop.mono (by simp))) (mkPi φ.pi.val
      (φ.pi.pi_prop.mono (by simp)))

@[simp] lemma ofZero_val {Γ'} (φ : Γ'-[0].Semiformula ℬ ξ n) (Γ) : (ofZero φ Γ).val = φ.val := by
  match Γ with
  | 𝚺-[_] => simp [ofZero]
  | 𝚷-[_] => simp [ofZero]
  | 𝚫-[_] => simp [ofZero]

@[simp] lemma ProperOn.of_zero (φ : Γ'-[0].Semisentence ℬ k) (m) : (ofZero φ 𝚫-[m]).ProperOn M := by
  simp [ProperOn, ofZero]

@[simp] lemma ProperWithParamOn.of_zero (φ : Γ'-[0].Semiformula ℬ M k) (m) : (ofZero φ
  𝚫-[m]).ProperWithParamOn M := by
  simp [ProperWithParamOn, ofZero]

def verum : {Γ : HierarchySymbol} → Γ.Semiformula ℬ ξ n
  | 𝚺-[m] => mkSigma ⊤ (by simp)
  | 𝚷-[m] => mkPi ⊤ (by simp)
  | 𝚫-[m] => mkDelta (mkSigma ⊤ (by simp)) (mkPi ⊤ (by simp))

def falsum : {Γ : HierarchySymbol} → Γ.Semiformula ℬ ξ n
  | 𝚺-[m] => mkSigma ⊥ (by simp)
  | 𝚷-[m] => mkPi ⊥ (by simp)
  | 𝚫-[m] => mkDelta (mkSigma ⊥ (by simp)) (mkPi ⊥ (by simp))

def and : {Γ : HierarchySymbol} → Γ.Semiformula ℬ ξ n → Γ.Semiformula ℬ ξ n → Γ.Semiformula ℬ ξ n
  | 𝚺-[m], φ, ψ => mkSigma (φ.val ⋏ ψ.val) (by simp)
  | 𝚷-[m], φ, ψ => mkPi (φ.val ⋏ ψ.val) (by simp)
  | 𝚫-[m], φ,
    ψ => mkDelta (mkSigma (φ.sigma.val ⋏ ψ.sigma.val) (by simp)) (mkPi (φ.pi.val ⋏ ψ.pi.val)
      (by simp))

def or : {Γ : HierarchySymbol} → Γ.Semiformula ℬ ξ n → Γ.Semiformula ℬ ξ n → Γ.Semiformula ℬ ξ n
  | 𝚺-[m], φ, ψ => mkSigma (φ.val ⋎ ψ.val) (by simp)
  | 𝚷-[m], φ, ψ => mkPi (φ.val ⋎ ψ.val) (by simp)
  | 𝚫-[m], φ,
    ψ => mkDelta (mkSigma (φ.sigma.val ⋎ ψ.sigma.val) (by simp)) (mkPi (φ.pi.val ⋎ ψ.pi.val)
      (by simp))

def negSigma (φ : 𝚺-[m].Semiformula ℬ ξ n) : 𝚷-[m].Semiformula ℬ ξ n := mkPi (∼φ.val) (by simp)

def negPi (φ : 𝚷-[m].Semiformula ℬ ξ n) : 𝚺-[m].Semiformula ℬ ξ n := mkSigma (∼φ.val) (by simp)

def negDelta (φ : 𝚫-[m].Semiformula ℬ ξ n) : 𝚫-[m].Semiformula ℬ ξ n := mkDelta (φ.pi.negPi)
  (φ.sigma.negSigma)

def ball {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) (t : Semiterm L ξ n) :
    {Γ : HierarchySymbol} → Γ.Semiformula ℬ ξ (n + 1) → Γ.Semiformula ℬ ξ n
  | 𝚺-[m], φ => mkSigma (∀¹[R.operator ![#0, Rew.bShift t]] φ.val) (by simp [hR])
  | 𝚷-[m], φ => mkPi (∀¹[R.operator ![#0, Rew.bShift t]] φ.val) (by simp [hR])
  | 𝚫-[m], φ =>
    mkDelta (mkSigma (∀¹[R.operator ![#0, Rew.bShift t]] φ.sigma.val) (by simp [hR]))
      (mkPi (∀¹[R.operator ![#0, Rew.bShift t]] φ.pi.val) (by simp [hR]))

def bexs {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) (t : Semiterm L ξ n) :
    {Γ : HierarchySymbol} → Γ.Semiformula ℬ ξ (n + 1) → Γ.Semiformula ℬ ξ n
  | 𝚺-[m], φ => mkSigma (∃¹[R.operator ![#0, Rew.bShift t]] φ.val) (by simp [hR])
  | 𝚷-[m], φ => mkPi (∃¹[R.operator ![#0, Rew.bShift t]] φ.val) (by simp [hR])
  | 𝚫-[m], φ =>
    mkDelta (mkSigma (∃¹[R.operator ![#0, Rew.bShift t]] φ.sigma.val) (by simp [hR]))
      (mkPi (∃¹[R.operator ![#0, Rew.bShift t]] φ.pi.val) (by simp [hR]))

def all (φ : 𝚷-[m + 1].Semiformula ℬ ξ (n + 1)) : 𝚷-[m + 1].Semiformula ℬ ξ n := mkPi (∀¹
  φ.val) φ.pi_prop.all

def exs (φ : 𝚺-[m + 1].Semiformula ℬ ξ (n + 1)) : 𝚺-[m + 1].Semiformula ℬ ξ n := mkSigma (∃¹
  φ.val) φ.sigma_prop.exs

instance : Top (Γ.Semiformula ℬ ξ n) := ⟨verum⟩

instance : Bot (Γ.Semiformula ℬ ξ n) := ⟨falsum⟩

instance : Wedge (Γ.Semiformula ℬ ξ n) := ⟨and⟩

instance : Vee (Γ.Semiformula ℬ ξ n) := ⟨or⟩

instance : Tilde (𝚫-[m].Semiformula ℬ ξ n) := ⟨negDelta⟩

instance : LogicalConnective (𝚫-[m].Semiformula ℬ ξ n) where
  arrow φ ψ := ∼φ ⋎ ψ

instance : ExsQuantifier (𝚺-[m + 1].Semiformula ℬ ξ) := ⟨exs⟩

instance : UnivQuantifier (𝚷-[m + 1].Semiformula ℬ ξ) := ⟨all⟩

def substSigma (φ : 𝚺-[m + 1].Semiformula ℬ ξ 1) (F : 𝚺-[m + 1].Semiformula ℬ ξ (n + 1)) :
    𝚺-[m + 1].Semiformula ℬ ξ n := (F ⋏ φ.rew (Rew.subst ![#0])).exs

@[simp] lemma val_verum : (⊤ : Γ.Semiformula ℬ ξ n).val = ⊤ := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp <;> rfl

@[simp] lemma sigma_verum {m} : (⊤ : 𝚫-[m].Semiformula ℬ ξ n).sigma = ⊤ := by simp [Top.top, verum]

@[simp] lemma pi_verum {m} : (⊤ : 𝚫-[m].Semiformula ℬ ξ n).pi = ⊤ := by simp [Top.top, verum]

@[simp] lemma val_falsum : (⊥ : Γ.Semiformula ℬ ξ n).val = ⊥ := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp <;> rfl

@[simp] lemma sigma_falsum {m} : (⊥ : 𝚫-[m].Semiformula ℬ ξ n).sigma = ⊥ := by simp [Bot.bot,
  falsum]

@[simp] lemma pi_falsum {m} : (⊥ : 𝚫-[m].Semiformula ℬ ξ n).pi = ⊥ := by simp [Bot.bot, falsum]

@[simp] lemma val_and (φ ψ : Γ.Semiformula ℬ ξ n) : (φ ⋏ ψ).val = φ.val ⋏ ψ.val := by
  suffices (φ.and ψ).val = φ.val ⋏ ψ.val from this
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [and, val, val_sigma]

@[simp] lemma sigma_and (φ ψ : 𝚫-[m].Semiformula ℬ ξ n) : (φ ⋏ ψ).sigma = φ.sigma ⋏ ψ.sigma := rfl

@[simp] lemma pi_and (φ ψ : 𝚫-[m].Semiformula ℬ ξ n) : (φ ⋏ ψ).pi = φ.pi ⋏ ψ.pi := rfl

@[simp] lemma val_or (φ ψ : Γ.Semiformula ℬ ξ n) : (φ ⋎ ψ).val = φ.val ⋎ ψ.val := by
  suffices (φ.or ψ).val = φ.val ⋎ ψ.val from this
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [or, val, val_sigma]

@[simp] lemma sigma_or (φ ψ : 𝚫-[m].Semiformula ℬ ξ n) : (φ ⋎ ψ).sigma = φ.sigma ⋎ ψ.sigma := rfl

@[simp] lemma pi_or (φ ψ : 𝚫-[m].Semiformula ℬ ξ n) : (φ ⋎ ψ).pi = φ.pi ⋎ ψ.pi := rfl

@[simp] lemma val_negSigma {m} (φ : 𝚺-[m].Semiformula ℬ ξ n) : φ.negSigma.val = ∼φ.val := by
  simp [negSigma]

@[simp] lemma val_negPi {m} (φ : 𝚷-[m].Semiformula ℬ ξ n) : φ.negPi.val = ∼φ.val := by simp [negPi]

lemma val_negDelta {m} (φ : 𝚫-[m].Semiformula ℬ ξ n) : (∼φ).val = ∼φ.pi.val := by simp
  [HTilde.hTilde, Tilde.tilde, negDelta]

@[simp] lemma sigma_negDelta {m} (φ : 𝚫-[m].Semiformula ℬ ξ n) : (∼φ).sigma = φ.pi.negPi :=
  by simp [HTilde.hTilde, Tilde.tilde, negDelta]

@[simp] lemma sigma_negPi {m} (φ : 𝚫-[m].Semiformula ℬ ξ n) : (∼φ).pi = φ.sigma.negSigma :=
  by simp [HTilde.hTilde, Tilde.tilde, negDelta]

@[simp] lemma val_ball {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) (t : Semiterm L ξ n)
    (φ : Γ.Semiformula ℬ ξ (n + 1)) : (ball hR t φ).val = ∀¹[R.operator ![#0,
      Rew.bShift t]] φ.val := by
  rcases Γ with ⟨Γ, m⟩
  rcases Γ <;> simp [ball, val, val_sigma]

@[simp] lemma val_bexs {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) (t : Semiterm L ξ n)
    (φ : Γ.Semiformula ℬ ξ (n + 1)) : (bexs hR t φ).val = ∃¹[R.operator ![#0,
      Rew.bShift t]] φ.val := by
  rcases Γ with ⟨Γ, m⟩
  rcases Γ <;> simp [bexs, val, val_sigma]

@[simp] lemma val_exsSigma {m} (φ : 𝚺-[m + 1].Semiformula ℬ ξ (n + 1)) : (exs φ).val = ∃¹
  φ.val := rfl

@[simp] lemma val_allPi {m} (φ : 𝚷-[m + 1].Semiformula ℬ ξ (n + 1)) : (all φ).val = ∀¹ φ.val := rfl

@[simp] lemma ProperOn.verum : (⊤ : 𝚫-[m].Semisentence ℬ k).ProperOn M := by intro e; simp

@[simp] lemma ProperOn.falsum : (⊥ : 𝚫-[m].Semisentence ℬ k).ProperOn M := by intro e; simp

lemma ProperOn.and {φ ψ : 𝚫-[m].Semisentence ℬ k} (hp : φ.ProperOn M) (hq : ψ.ProperOn M) :
  (φ ⋏ ψ).ProperOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperOn.or {φ ψ : 𝚫-[m].Semisentence ℬ k} (hp : φ.ProperOn M) (hq : ψ.ProperOn M) : (φ
  ⋎ ψ).ProperOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperOn.neg {φ : 𝚫-[m].Semisentence ℬ k} (hp : φ.ProperOn M) : (∼φ).ProperOn M := by
  intro e; simp [hp.iff]

lemma ProperOn.eval_neg {φ : 𝚫-[m].Semisentence ℬ k} (hp : φ.ProperOn M) (e : Fin k → M) :
    (∼φ).val.Evalb e ↔ ¬φ.val.Evalb e := by
  simp [←val_sigma, hp.iff]

lemma ProperOn.ball {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {t}
    {φ : 𝚫-[m + 1].Semisentence ℬ (k + 1)} (hp : φ.ProperOn M) : (ball hR t φ).ProperOn M := by
  intro e
  simp [Semiformula.ball, hp.iff]

lemma ProperOn.bexs {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {t}
    {φ : 𝚫-[m + 1].Semisentence ℬ (k + 1)} (hp : φ.ProperOn M) : (bexs hR t φ).ProperOn M := by
  intro e
  simp [Semiformula.bexs, hp.iff]

@[simp] lemma ProperWithParamOn.verum : (⊤ : 𝚫-[m].Semiformula ℬ M k).ProperWithParamOn M :=
  by intro e; simp

@[simp] lemma ProperWithParamOn.falsum : (⊥ : 𝚫-[m].Semiformula ℬ M k).ProperWithParamOn M :=
  by intro e; simp

lemma ProperWithParamOn.and {φ ψ : 𝚫-[m].Semiformula ℬ M k}
    (hp : φ.ProperWithParamOn M) (hq : ψ.ProperWithParamOn M) : (φ ⋏ ψ).ProperWithParamOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperWithParamOn.or {φ ψ : 𝚫-[m].Semiformula ℬ M k}
    (hp : φ.ProperWithParamOn M) (hq : ψ.ProperWithParamOn M) : (φ ⋎ ψ).ProperWithParamOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperWithParamOn.neg {φ : 𝚫-[m].Semiformula ℬ M k} (hp : φ.ProperWithParamOn M) :
  (∼φ).ProperWithParamOn M := by
  intro e; simp [hp.iff]

lemma ProperWithParamOn.eval_neg {φ : 𝚫-[m].Semiformula ℬ M k} (hp : φ.ProperWithParamOn M)
  (e : Fin k → M) :
    (∼φ).val.Eval e id ↔ ¬φ.val.Eval e id := by
  simp [←val_sigma, hp.iff]

lemma ProperWithParamOn.ball {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {t}
    {φ : 𝚫-[m].Semiformula ℬ M (k + 1)}
    (hp : φ.ProperWithParamOn M) : (ball hR t φ).ProperWithParamOn M := by
  intro e
  simp [Semiformula.ball, hp.iff]

lemma ProperWithParamOn.bexs {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {t}
    {φ : 𝚫-[m].Semiformula ℬ M (k + 1)}
    (hp : φ.ProperWithParamOn M) : (bexs hR t φ).ProperWithParamOn M := by
  intro e
  simp [Semiformula.bexs, hp.iff]

def graphDelta [L.Eq] (φ : 𝚺-[m].Semiformula ℬ ξ (k + 1)) : 𝚫-[m].Semiformula ℬ ξ (k + 1) :=
  match m with
  |     0 => φ.ofZero _
  | m + 1 => mkDelta φ (mkPi “x. ∀ y, !φ.val y ⋯ → y = x” (by
      apply Hierarchy.all
      apply Hierarchy.imp_iff.mpr
      exact ⟨φ.sigma_prop.rew _, by simp [FirstOrder.Semiformula.Operator.eq_def]⟩))

@[simp] lemma graphDelta_val [L.Eq] (φ : 𝚺-[m].Semiformula ℬ ξ (k + 1)) : φ.graphDelta.val =
  φ.val := by cases m <;> simp [graphDelta]

end Semiformula

end HierarchySymbol

end FFL.FirstOrder.Bounding
