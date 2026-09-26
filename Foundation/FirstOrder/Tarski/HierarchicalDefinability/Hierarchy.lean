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

structure HierarchySymbol {L : Language} (ℬ : FirstOrder.Bounding L) where
  Γ : SigmaPiDelta
  rank : ℕ

scoped notation:max Γ:max "-[" ℬ:max ", " n "]" => @HierarchySymbol.mk _ ℬ Γ n

namespace HierarchySymbol

variable {L : Language}
variable {ℬ : FirstOrder.Bounding L}

variable (ξ : Type*) (n : ℕ)

protected inductive Semiformula : HierarchySymbol ℬ → Type _ where
  | mkSigma {m} (φ : FirstOrder.Semiformula L ξ n) (hφ : ℬ.Hierarchy 𝚺 m φ := by simp) :
    𝚺-[ℬ, m].Semiformula
  | mkPi {m} (φ : FirstOrder.Semiformula L ξ n) (hφ : ℬ.Hierarchy 𝚷 m φ := by simp) :
    𝚷-[ℬ, m].Semiformula
  | mkDelta {m} : 𝚺-[ℬ, m].Semiformula → 𝚷-[ℬ, m].Semiformula → 𝚫-[ℬ, m].Semiformula

protected abbrev Semisentence (Γ : HierarchySymbol ℬ) (n : ℕ) := Γ.Semiformula Empty n

protected abbrev Sentence (Γ : HierarchySymbol ℬ) := Γ.Semiformula Empty 0

variable {Γ : HierarchySymbol ℬ}

variable {ξ n} {m k n₁ n₂ : ℕ} {ξ₁ ξ₂ : Type*} {Γ' : Polarity}

namespace Semiformula

@[coe] def val {Γ : HierarchySymbol ℬ} : Γ.Semiformula ξ n → FirstOrder.Semiformula L ξ n
  | mkSigma φ _ => φ
  | mkPi    φ _ => φ
  | mkDelta φ _ => φ.val

@[simp] lemma val_mkSigma (φ : FirstOrder.Semiformula L ξ n) (hp : ℬ.Hierarchy 𝚺 m φ) :
  (mkSigma φ hp).val = φ := rfl

@[simp] lemma val_mkPi (φ : FirstOrder.Semiformula L ξ n) (hp : ℬ.Hierarchy 𝚷 m φ) :
    (mkPi φ hp).val = φ := rfl

@[simp] lemma val_mkDelta (φ : 𝚺-[ℬ, m].Semiformula ξ n) (ψ : 𝚷-[ℬ, m].Semiformula ξ n) :
  (mkDelta φ ψ).val = φ.val := rfl

instance : CoeOut (𝚺-[ℬ, 0].Semisentence n) (FirstOrder.Semisentence L n) := ⟨Semiformula.val⟩
instance : CoeOut (𝚷-[ℬ, 0].Semisentence n) (FirstOrder.Semisentence L n) := ⟨Semiformula.val⟩
instance : CoeOut (𝚫-[ℬ, 0].Semisentence n) (FirstOrder.Semisentence L n) := ⟨Semiformula.val⟩

instance : CoeOut (𝚺-[ℬ, 1].Semisentence n) (FirstOrder.Semisentence L n) := ⟨Semiformula.val⟩
instance : CoeOut (𝚷-[ℬ, 1].Semisentence n) (FirstOrder.Semisentence L n) := ⟨Semiformula.val⟩
instance : CoeOut (𝚫-[ℬ, 1].Semisentence n) (FirstOrder.Semisentence L n) := ⟨Semiformula.val⟩

@[simp] lemma sigma_prop : (φ : 𝚺-[ℬ, m].Semiformula ξ n) → ℬ.Hierarchy 𝚺 m φ.val
  | mkSigma _ h => h

@[simp] lemma pi_prop : (φ : 𝚷-[ℬ, m].Semiformula ξ n) → ℬ.Hierarchy 𝚷 m φ.val
  | mkPi _ h => h

@[simp] lemma polarity_prop : {Γ : Polarity} → (φ : Γ-[ℬ, m].Semiformula ξ n) →
    ℬ.Hierarchy Γ m φ.val
  | 𝚺, φ => φ.sigma_prop
  | 𝚷, φ => φ.pi_prop

def sigma : 𝚫-[ℬ, m].Semiformula ξ n → 𝚺-[ℬ, m].Semiformula ξ n
  | mkDelta φ _ => φ

@[simp] lemma sigma_mkDelta (φ : 𝚺-[ℬ, m].Semiformula ξ n) (ψ : 𝚷-[ℬ, m].Semiformula ξ n) :
  (mkDelta φ ψ).sigma = φ := rfl

def pi : 𝚫-[ℬ, m].Semiformula ξ n → 𝚷-[ℬ, m].Semiformula ξ n
  | mkDelta _ φ => φ

@[simp] lemma pi_mkDelta (φ : 𝚺-[ℬ, m].Semiformula ξ n) (ψ : 𝚷-[ℬ, m].Semiformula ξ n) :
  (mkDelta φ ψ).pi = ψ := rfl

lemma val_sigma (φ : 𝚫-[ℬ, m].Semiformula ξ n) : φ.sigma.val = φ.val := by rcases φ; simp

def mkPolarity (φ : FirstOrder.Semiformula L ξ n) :
    (Γ : Polarity) → ℬ.Hierarchy Γ m φ → Γ-[ℬ, m].Semiformula ξ n
  | 𝚺, h => mkSigma φ h
  | 𝚷, h => mkPi φ h

@[simp] lemma val_mkPolarity (φ : FirstOrder.Semiformula L ξ n) {Γ} (h : ℬ.Hierarchy Γ m φ) :
  (mkPolarity φ Γ h).val = φ := by cases Γ <;> rfl

@[simp] lemma hierarchy_sigma (φ : 𝚺-[ℬ, m].Semiformula ξ n) : ℬ.Hierarchy 𝚺 m φ.val := φ.sigma_prop

@[simp] lemma hierarchy_pi (φ : 𝚷-[ℬ, m].Semiformula ξ n) : ℬ.Hierarchy 𝚷 m φ.val := φ.pi_prop

@[simp] lemma hierarchy_zero {Γ Γ' m} (φ : Γ-[ℬ, 0].Semiformula ξ n) : ℬ.Hierarchy Γ' m φ.val := by
  cases Γ
  · exact Hierarchy.of_zero φ.sigma_prop
  · exact Hierarchy.of_zero φ.pi_prop
  · cases φ
    simpa using Hierarchy.of_zero (sigma_prop _)

lemma hierarchy_of_lt {C : HierarchySymbol ℬ} {Γ : Polarity} {s : ℕ} (φ : C.Semiformula ξ n)
    (h : C.rank < s) : ℬ.Hierarchy Γ s φ.val := by
  rcases C with ⟨_ | _ | _, m⟩
  · exact φ.sigma_prop.strict_mono _ h
  · exact φ.pi_prop.strict_mono _ h
  · exact (val_sigma φ ▸ φ.sigma.sigma_prop).strict_mono _ h

variable {M : Type*} [Tarski.Structure L M]

variable (M)

def ProperOn (φ : 𝚫-[ℬ, m].Semisentence n) : Prop :=
  ∀ (e : Fin n → M), φ.sigma.val.Evalb e ↔ φ.pi.val.Evalb e

def ProperWithParamOn (φ : 𝚫-[ℬ, m].Semiformula M n) : Prop :=
  ∀ (e : Fin n → M), φ.sigma.val.Eval e id ↔ φ.pi.val.Eval e id

def ProvablyProperOn (φ : 𝚫-[ℬ, m].Semisentence n) (T : Theory L) : Prop :=
  T ⊢ ∀¹* “!φ.sigma.val ⋯ ↔ !φ.pi.val ⋯”

variable {M}

lemma ProperOn.iff {φ : 𝚫-[ℬ, m].Semisentence n}
    (h : φ.ProperOn M) (e : Fin n → M) :
    φ.sigma.val.Evalb e ↔ φ.pi.val.Evalb e := h e

lemma ProperWithParamOn.iff {φ : 𝚫-[ℬ, m].Semiformula M n}
    (h : φ.ProperWithParamOn M) (e : Fin n → M) :
    φ.sigma.val.Eval e id ↔ φ.pi.val.Eval e id := h e

lemma ProperOn.iff' {φ : 𝚫-[ℬ, m].Semisentence n}
    (h : φ.ProperOn M) (e : Fin n → M) :
    φ.pi.val.Evalb e ↔ φ.val.Evalb e := by simp [←h.iff, val_sigma]

lemma ProperWithParamOn.iff' {φ : 𝚫-[ℬ, m].Semiformula M n}
    (h : φ.ProperWithParamOn M) (e : Fin n → M) :
    φ.pi.val.Eval e id ↔ φ.val.Eval e id := by simp [←h.iff, val_sigma]

inductive ProvablyProperOn' (T : Theory L) : {Γ : HierarchySymbol ℬ} → {n : ℕ} →
    (φ : Γ.Semisentence n) → Prop
  | sigma (φ : 𝚺-[ℬ, m].Semisentence n) : φ.ProvablyProperOn' T
  | pi (φ : 𝚷-[ℬ, m].Semisentence n) : φ.ProvablyProperOn' T
  | delta (φ : 𝚫-[ℬ, m].Semisentence n) : φ.ProvablyProperOn T → φ.ProvablyProperOn' T

section ProvablyProperOn

variable (T : Theory L)

variable {T}

lemma ProvablyProperOn.properOn
    {φ : 𝚫-[ℬ, m].Semisentence n} (h : φ.ProvablyProperOn T)
    (M : Type w) [Nonempty M] [Tarski.Structure L M] [M↓[L] ⊧* T] : φ.ProperOn M := by
  intro v
  have := by simpa [models_iff] using consequence_iff.mp (Theory.Proof.sound h) M inferInstance
  exact this v

end ProvablyProperOn

def rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) : {Γ : HierarchySymbol ℬ} → Γ.Semiformula ξ₁ n₁ →
  Γ.Semiformula ξ₂ n₂
  | 𝚺-[ℬ, _], mkSigma φ hp => mkSigma (ω ▹ φ) (hp.rew ω)
  | 𝚷-[ℬ, _], mkPi φ hp    => mkPi (ω ▹ φ) (hp.rew ω)
  | 𝚫-[ℬ, _], mkDelta φ ψ  => mkDelta (φ.rew ω) (ψ.rew ω)

@[simp] lemma val_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) {Γ : HierarchySymbol ℬ}
    (φ : Γ.Semiformula ξ₁ n₁) : (φ.rew ω).val = ω ▹ φ.val := by
  rcases Γ with ⟨Γ, m⟩; rcases φ with (_ | _ | ⟨⟨p, _⟩, ⟨q, _⟩⟩) <;> simp [rew]

@[simp] lemma ProperOn.rew {φ : 𝚫-[ℬ, m].Semisentence n₁} (h : φ.ProperOn M)
    (ω : Rew L Empty n₁ Empty n₂) : (φ.rew ω).ProperOn M := by
  rcases φ; simp only [ProperOn, Semiformula.rew, sigma_mkDelta, val_rew, Semiformula.eval_rew,
    Empty.eq_elim, pi_mkDelta]
  intro e; exact h.iff _

@[simp] lemma ProperOn.rew' {φ : 𝚫-[ℬ, m].Semisentence n₁} (h : φ.ProperOn M)
    (ω : Rew L Empty n₁ M n₂) : (φ.rew ω).ProperWithParamOn M := by
  rcases φ; intro e; simp [Semiformula.rew, Semiformula.eval_rew, Empty.eq_elim]
  simpa using h.iff _

@[simp] lemma ProperWithParamOn.rew {φ : 𝚫-[ℬ, m].Semiformula M n₁}
    (h : φ.ProperWithParamOn M) (f : Fin n₁ → Semiterm L M n₂) : (φ.rew (Rew.subst
      f)).ProperWithParamOn M := by
  rcases φ; intro e
  simp only [Semiformula.rew, sigma_mkDelta, val_rew, Semiformula.eval_rew, pi_mkDelta]
  exact h.iff _

lemma sigmaZero {Γ} (φ : Γ-[ℬ, 0].Semiformula ξ k) : ℬ.Hierarchy 𝚺 0 φ.val :=
  match Γ with
  | 𝚺 => φ.sigma_prop
  | 𝚷 => φ.pi_prop.of_zero
  | 𝚫 => by simp

def ofZero {Γ'} (φ : Γ'-[ℬ, 0].Semiformula ξ k) : (Γ : HierarchySymbol ℬ) → Γ.Semiformula ξ k
  | 𝚺-[ℬ, _] => mkSigma φ.val φ.sigmaZero.of_zero
  | 𝚷-[ℬ, _] => mkPi φ.val φ.sigmaZero.of_zero
  | 𝚫-[ℬ, _] => mkDelta (mkSigma φ.val φ.sigmaZero.of_zero) (mkPi φ.val φ.sigmaZero.of_zero)

def ofDeltaOne (φ : 𝚫-[ℬ, 1].Semiformula ξ k) :
    (Γ : SigmaPiDelta) → (m : ℕ) → Γ-[ℬ, m+1].Semiformula ξ k
  | 𝚺, m => mkSigma φ.sigma.val (φ.sigma.sigma_prop.mono (by simp))
  | 𝚷, m => mkPi φ.pi.val (φ.pi.pi_prop.mono (by simp))
  | 𝚫,
    m => mkDelta (mkSigma φ.sigma.val (φ.sigma.sigma_prop.mono (by simp))) (mkPi φ.pi.val
      (φ.pi.pi_prop.mono (by simp)))

@[simp] lemma ofZero_val {Γ'} (φ : Γ'-[ℬ, 0].Semiformula ξ n) (Γ) : (ofZero φ Γ).val = φ.val := by
  match Γ with
  | 𝚺-[ℬ, _] => simp [ofZero]
  | 𝚷-[ℬ, _] => simp [ofZero]
  | 𝚫-[ℬ, _] => simp [ofZero]

@[simp] lemma ProperOn.of_zero (φ : Γ'-[ℬ, 0].Semisentence k) (m) :
    (ofZero φ 𝚫-[ℬ, m]).ProperOn M := by
  simp [ProperOn, ofZero]

@[simp] lemma ProperWithParamOn.of_zero (φ : Γ'-[ℬ, 0].Semiformula M k) (m) : (ofZero φ
  𝚫-[ℬ, m]).ProperWithParamOn M := by
  simp [ProperWithParamOn, ofZero]

def verum : {Γ : HierarchySymbol ℬ} → Γ.Semiformula ξ n
  | 𝚺-[ℬ, m] => mkSigma ⊤ (by simp)
  | 𝚷-[ℬ, m] => mkPi ⊤ (by simp)
  | 𝚫-[ℬ, m] => mkDelta (mkSigma ⊤ (by simp)) (mkPi ⊤ (by simp))

def falsum : {Γ : HierarchySymbol ℬ} → Γ.Semiformula ξ n
  | 𝚺-[ℬ, m] => mkSigma ⊥ (by simp)
  | 𝚷-[ℬ, m] => mkPi ⊥ (by simp)
  | 𝚫-[ℬ, m] => mkDelta (mkSigma ⊥ (by simp)) (mkPi ⊥ (by simp))

def and : {Γ : HierarchySymbol ℬ} → Γ.Semiformula ξ n → Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | 𝚺-[ℬ, m], φ, ψ => mkSigma (φ.val ⋏ ψ.val) (by simp)
  | 𝚷-[ℬ, m], φ, ψ => mkPi (φ.val ⋏ ψ.val) (by simp)
  | 𝚫-[ℬ, m], φ,
    ψ => mkDelta (mkSigma (φ.sigma.val ⋏ ψ.sigma.val) (by simp)) (mkPi (φ.pi.val ⋏ ψ.pi.val)
      (by simp))

def or : {Γ : HierarchySymbol ℬ} → Γ.Semiformula ξ n → Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | 𝚺-[ℬ, m], φ, ψ => mkSigma (φ.val ⋎ ψ.val) (by simp)
  | 𝚷-[ℬ, m], φ, ψ => mkPi (φ.val ⋎ ψ.val) (by simp)
  | 𝚫-[ℬ, m], φ,
    ψ => mkDelta (mkSigma (φ.sigma.val ⋎ ψ.sigma.val) (by simp)) (mkPi (φ.pi.val ⋎ ψ.pi.val)
      (by simp))

def negSigma (φ : 𝚺-[ℬ, m].Semiformula ξ n) : 𝚷-[ℬ, m].Semiformula ξ n := mkPi (∼φ.val) (by simp)

def negPi (φ : 𝚷-[ℬ, m].Semiformula ξ n) : 𝚺-[ℬ, m].Semiformula ξ n := mkSigma (∼φ.val) (by simp)

def negDelta (φ : 𝚫-[ℬ, m].Semiformula ξ n) : 𝚫-[ℬ, m].Semiformula ξ n := mkDelta (φ.pi.negPi)
  (φ.sigma.negSigma)

def ball {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) (t : Semiterm L ξ n) :
    {Γ : HierarchySymbol ℬ} → Γ.Semiformula ξ (n + 1) → Γ.Semiformula ξ n
  | 𝚺-[ℬ, m], φ => mkSigma (∀¹[R.operator ![#0, Rew.bShift t]] φ.val) (by simp [hR])
  | 𝚷-[ℬ, m], φ => mkPi (∀¹[R.operator ![#0, Rew.bShift t]] φ.val) (by simp [hR])
  | 𝚫-[ℬ, m], φ =>
    mkDelta (mkSigma (∀¹[R.operator ![#0, Rew.bShift t]] φ.sigma.val) (by simp [hR]))
      (mkPi (∀¹[R.operator ![#0, Rew.bShift t]] φ.pi.val) (by simp [hR]))

def bexs {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) (t : Semiterm L ξ n) :
    {Γ : HierarchySymbol ℬ} → Γ.Semiformula ξ (n + 1) → Γ.Semiformula ξ n
  | 𝚺-[ℬ, m], φ => mkSigma (∃¹[R.operator ![#0, Rew.bShift t]] φ.val) (by simp [hR])
  | 𝚷-[ℬ, m], φ => mkPi (∃¹[R.operator ![#0, Rew.bShift t]] φ.val) (by simp [hR])
  | 𝚫-[ℬ, m], φ =>
    mkDelta (mkSigma (∃¹[R.operator ![#0, Rew.bShift t]] φ.sigma.val) (by simp [hR]))
      (mkPi (∃¹[R.operator ![#0, Rew.bShift t]] φ.pi.val) (by simp [hR]))

def all (φ : 𝚷-[ℬ, m + 1].Semiformula ξ (n + 1)) : 𝚷-[ℬ, m + 1].Semiformula ξ n := mkPi (∀¹
  φ.val) φ.pi_prop.all

def exs (φ : 𝚺-[ℬ, m + 1].Semiformula ξ (n + 1)) : 𝚺-[ℬ, m + 1].Semiformula ξ n := mkSigma (∃¹
  φ.val) φ.sigma_prop.exs

instance : Top (Γ.Semiformula ξ n) := ⟨verum⟩

instance : Bot (Γ.Semiformula ξ n) := ⟨falsum⟩

instance : Wedge (Γ.Semiformula ξ n) := ⟨and⟩

instance : Vee (Γ.Semiformula ξ n) := ⟨or⟩

instance : Tilde (𝚫-[ℬ, m].Semiformula ξ n) := ⟨negDelta⟩

instance : LogicalConnective (𝚫-[ℬ, m].Semiformula ξ n) where
  arrow φ ψ := ∼φ ⋎ ψ

instance : ExsQuantifier (𝚺-[ℬ, m + 1].Semiformula ξ) := ⟨exs⟩

instance : UnivQuantifier (𝚷-[ℬ, m + 1].Semiformula ξ) := ⟨all⟩

def substSigma (φ : 𝚺-[ℬ, m + 1].Semiformula ξ 1) (F : 𝚺-[ℬ, m + 1].Semiformula ξ (n + 1)) :
    𝚺-[ℬ, m + 1].Semiformula ξ n := (F ⋏ φ.rew (Rew.subst ![#0])).exs

@[simp] lemma val_verum : (⊤ : Γ.Semiformula ξ n).val = ⊤ := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp <;> rfl

@[simp] lemma sigma_verum {m} : (⊤ : 𝚫-[ℬ, m].Semiformula ξ n).sigma = ⊤ := by simp [Top.top, verum]

@[simp] lemma pi_verum {m} : (⊤ : 𝚫-[ℬ, m].Semiformula ξ n).pi = ⊤ := by simp [Top.top, verum]

@[simp] lemma val_falsum : (⊥ : Γ.Semiformula ξ n).val = ⊥ := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp <;> rfl

@[simp] lemma sigma_falsum {m} : (⊥ : 𝚫-[ℬ, m].Semiformula ξ n).sigma = ⊥ := by simp [Bot.bot,
  falsum]

@[simp] lemma pi_falsum {m} : (⊥ : 𝚫-[ℬ, m].Semiformula ξ n).pi = ⊥ := by simp [Bot.bot, falsum]

@[simp] lemma val_and (φ ψ : Γ.Semiformula ξ n) : (φ ⋏ ψ).val = φ.val ⋏ ψ.val := by
  suffices (φ.and ψ).val = φ.val ⋏ ψ.val from this
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [and, val, val_sigma]

@[simp] lemma sigma_and (φ ψ : 𝚫-[ℬ, m].Semiformula ξ n) : (φ ⋏ ψ).sigma = φ.sigma ⋏ ψ.sigma := rfl

@[simp] lemma pi_and (φ ψ : 𝚫-[ℬ, m].Semiformula ξ n) : (φ ⋏ ψ).pi = φ.pi ⋏ ψ.pi := rfl

@[simp] lemma val_or (φ ψ : Γ.Semiformula ξ n) : (φ ⋎ ψ).val = φ.val ⋎ ψ.val := by
  suffices (φ.or ψ).val = φ.val ⋎ ψ.val from this
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [or, val, val_sigma]

@[simp] lemma sigma_or (φ ψ : 𝚫-[ℬ, m].Semiformula ξ n) : (φ ⋎ ψ).sigma = φ.sigma ⋎ ψ.sigma := rfl

@[simp] lemma pi_or (φ ψ : 𝚫-[ℬ, m].Semiformula ξ n) : (φ ⋎ ψ).pi = φ.pi ⋎ ψ.pi := rfl

@[simp] lemma val_negSigma {m} (φ : 𝚺-[ℬ, m].Semiformula ξ n) : φ.negSigma.val = ∼φ.val := by
  simp [negSigma]

@[simp] lemma val_negPi {m} (φ : 𝚷-[ℬ, m].Semiformula ξ n) : φ.negPi.val = ∼φ.val := by simp [negPi]

lemma val_negDelta {m} (φ : 𝚫-[ℬ, m].Semiformula ξ n) : (∼φ).val = ∼φ.pi.val := by simp
  [HTilde.hTilde, Tilde.tilde, negDelta]

@[simp] lemma sigma_negDelta {m} (φ : 𝚫-[ℬ, m].Semiformula ξ n) : (∼φ).sigma = φ.pi.negPi :=
  by simp [HTilde.hTilde, Tilde.tilde, negDelta]

@[simp] lemma sigma_negPi {m} (φ : 𝚫-[ℬ, m].Semiformula ξ n) : (∼φ).pi = φ.sigma.negSigma :=
  by simp [HTilde.hTilde, Tilde.tilde, negDelta]

@[simp] lemma val_ball {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) (t : Semiterm L ξ n)
    (φ : Γ.Semiformula ξ (n + 1)) : (ball hR t φ).val = ∀¹[R.operator ![#0,
      Rew.bShift t]] φ.val := by
  rcases Γ with ⟨Γ, m⟩
  rcases Γ <;> simp [ball, val, val_sigma]

@[simp] lemma val_bexs {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) (t : Semiterm L ξ n)
    (φ : Γ.Semiformula ξ (n + 1)) : (bexs hR t φ).val = ∃¹[R.operator ![#0,
      Rew.bShift t]] φ.val := by
  rcases Γ with ⟨Γ, m⟩
  rcases Γ <;> simp [bexs, val, val_sigma]

@[simp] lemma val_exsSigma {m} (φ : 𝚺-[ℬ, m + 1].Semiformula ξ (n + 1)) : (exs φ).val = ∃¹
  φ.val := rfl

@[simp] lemma val_allPi {m} (φ : 𝚷-[ℬ, m + 1].Semiformula ξ (n + 1)) : (all φ).val = ∀¹ φ.val := rfl

@[simp] lemma ProperOn.verum : (⊤ : 𝚫-[ℬ, m].Semisentence k).ProperOn M := by intro e; simp

@[simp] lemma ProperOn.falsum : (⊥ : 𝚫-[ℬ, m].Semisentence k).ProperOn M := by intro e; simp

lemma ProperOn.and {φ ψ : 𝚫-[ℬ, m].Semisentence k} (hp : φ.ProperOn M) (hq : ψ.ProperOn M) :
  (φ ⋏ ψ).ProperOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperOn.or {φ ψ : 𝚫-[ℬ, m].Semisentence k} (hp : φ.ProperOn M) (hq : ψ.ProperOn M) : (φ
  ⋎ ψ).ProperOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperOn.neg {φ : 𝚫-[ℬ, m].Semisentence k} (hp : φ.ProperOn M) : (∼φ).ProperOn M := by
  intro e; simp [hp.iff]

lemma ProperOn.eval_neg {φ : 𝚫-[ℬ, m].Semisentence k} (hp : φ.ProperOn M) (e : Fin k → M) :
    (∼φ).val.Evalb e ↔ ¬φ.val.Evalb e := by
  simp [←val_sigma, hp.iff]

lemma ProperOn.ball {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {t}
    {φ : 𝚫-[ℬ, m + 1].Semisentence (k + 1)} (hp : φ.ProperOn M) : (ball hR t φ).ProperOn M := by
  intro e
  simp [Semiformula.ball, hp.iff]

lemma ProperOn.bexs {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {t}
    {φ : 𝚫-[ℬ, m + 1].Semisentence (k + 1)} (hp : φ.ProperOn M) : (bexs hR t φ).ProperOn M := by
  intro e
  simp [Semiformula.bexs, hp.iff]

@[simp] lemma ProperWithParamOn.verum : (⊤ : 𝚫-[ℬ, m].Semiformula M k).ProperWithParamOn M :=
  by intro e; simp

@[simp] lemma ProperWithParamOn.falsum : (⊥ : 𝚫-[ℬ, m].Semiformula M k).ProperWithParamOn M :=
  by intro e; simp

lemma ProperWithParamOn.and {φ ψ : 𝚫-[ℬ, m].Semiformula M k}
    (hp : φ.ProperWithParamOn M) (hq : ψ.ProperWithParamOn M) : (φ ⋏ ψ).ProperWithParamOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperWithParamOn.or {φ ψ : 𝚫-[ℬ, m].Semiformula M k}
    (hp : φ.ProperWithParamOn M) (hq : ψ.ProperWithParamOn M) : (φ ⋎ ψ).ProperWithParamOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperWithParamOn.neg {φ : 𝚫-[ℬ, m].Semiformula M k} (hp : φ.ProperWithParamOn M) :
  (∼φ).ProperWithParamOn M := by
  intro e; simp [hp.iff]

lemma ProperWithParamOn.eval_neg {φ : 𝚫-[ℬ, m].Semiformula M k} (hp : φ.ProperWithParamOn M)
  (e : Fin k → M) :
    (∼φ).val.Eval e id ↔ ¬φ.val.Eval e id := by
  simp [←val_sigma, hp.iff]

lemma ProperWithParamOn.ball {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {t}
    {φ : 𝚫-[ℬ, m].Semiformula M (k + 1)}
    (hp : φ.ProperWithParamOn M) : (ball hR t φ).ProperWithParamOn M := by
  intro e
  simp [Semiformula.ball, hp.iff]

lemma ProperWithParamOn.bexs {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {t}
    {φ : 𝚫-[ℬ, m].Semiformula M (k + 1)}
    (hp : φ.ProperWithParamOn M) : (bexs hR t φ).ProperWithParamOn M := by
  intro e
  simp [Semiformula.bexs, hp.iff]

def graphDelta [L.Eq] (φ : 𝚺-[ℬ, m].Semiformula ξ (k + 1)) : 𝚫-[ℬ, m].Semiformula ξ (k + 1) :=
  match m with
  |     0 => φ.ofZero _
  | m + 1 => mkDelta φ (mkPi “x. ∀ y, !φ.val y ⋯ → y = x” (by
      apply Hierarchy.all
      apply Hierarchy.imp_iff.mpr
      exact ⟨φ.sigma_prop.rew _, by simp [FirstOrder.Semiformula.Operator.eq_def]⟩))

@[simp] lemma graphDelta_val [L.Eq] (φ : 𝚺-[ℬ, m].Semiformula ξ (k + 1)) : φ.graphDelta.val =
  φ.val := by cases m <;> simp [graphDelta]

end Semiformula

end HierarchySymbol

end FFL.FirstOrder.Bounding
