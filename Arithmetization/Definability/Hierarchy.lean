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

namespace LO.FirstOrder.Arith

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
  | mkSigma {m} : (p : Semiformula ℒₒᵣ ξ n) → Hierarchy 𝚺 m p → 𝚺-[m].Semiformula
  | mkPi {m}    : (p : Semiformula ℒₒᵣ ξ n) → Hierarchy 𝚷 m p → 𝚷-[m].Semiformula
  | mkDelta {m} : 𝚺-[m].Semiformula → 𝚷-[m].Semiformula → 𝚫-[m].Semiformula

protected abbrev Semisentence (Γ : HierarchySymbol) (n : ℕ) := Γ.Semiformula Empty n

variable {Γ : HierarchySymbol}

variable {ξ n}

namespace Semiformula

def val {Γ : HierarchySymbol} : Γ.Semiformula ξ n → Semiformula ℒₒᵣ ξ n
  | mkSigma p _ => p
  | mkPi    p _ => p
  | mkDelta p _ => p.val

@[simp] lemma val_mkSigma (p : Semiformula ℒₒᵣ ξ n) (hp : Hierarchy 𝚺 m p) : (mkSigma p hp).val = p := rfl

@[simp] lemma val_mkPi (p : Semiformula ℒₒᵣ ξ n) (hp : Hierarchy 𝚷 m p) : (mkPi p hp).val = p := rfl

@[simp] lemma val_mkDelta (p : 𝚺-[m].Semiformula ξ n) (q : 𝚷-[m].Semiformula ξ n) : (mkDelta p q).val = p.val := rfl

instance : Coe (𝚺₀.Semisentence n) (Semisentence ℒₒᵣ n) := ⟨Semiformula.val⟩
instance : Coe (𝚷₀.Semisentence n) (Semisentence ℒₒᵣ n) := ⟨Semiformula.val⟩
instance : Coe (𝚫₀.Semisentence n) (Semisentence ℒₒᵣ n) := ⟨Semiformula.val⟩

instance : Coe (𝚺₁.Semisentence n) (Semisentence ℒₒᵣ n) := ⟨Semiformula.val⟩
instance : Coe (𝚷₁.Semisentence n) (Semisentence ℒₒᵣ n) := ⟨Semiformula.val⟩
instance : Coe (𝚫₁.Semisentence n) (Semisentence ℒₒᵣ n) := ⟨Semiformula.val⟩

@[simp] lemma sigma_prop : (p : 𝚺-[m].Semiformula ξ n) → Hierarchy 𝚺 m p.val
  | mkSigma _ h => h

@[simp] lemma pi_prop : (p : 𝚷-[m].Semiformula ξ n) → Hierarchy 𝚷 m p.val
  | mkPi _ h => h

@[simp] lemma polarity_prop : {Γ : Polarity} → (p : Γ-[m].Semiformula ξ n) → Hierarchy Γ m p.val
  | 𝚺, p => p.sigma_prop
  | 𝚷, p => p.pi_prop

def sigma : 𝚫-[m].Semiformula ξ n → 𝚺-[m].Semiformula ξ n
  | mkDelta p _ => p

@[simp] lemma sigma_mkDelta (p : 𝚺-[m].Semiformula ξ n) (q : 𝚷-[m].Semiformula ξ n) : (mkDelta p q).sigma = p := rfl

def pi : 𝚫-[m].Semiformula ξ n → 𝚷-[m].Semiformula ξ n
  | mkDelta _ p => p

@[simp] lemma pi_mkDelta (p : 𝚺-[m].Semiformula ξ n) (q : 𝚷-[m].Semiformula ξ n) : (mkDelta p q).pi = q := rfl

lemma val_sigma (p : 𝚫-[m].Semiformula ξ n) : p.sigma.val = p.val := by rcases p; simp

def mkPolarity (p : Semiformula ℒₒᵣ ξ n) : (Γ : Polarity) → Hierarchy Γ m p → Γ-[m].Semiformula ξ n
  | 𝚺, h => mkSigma p h
  | 𝚷, h => mkPi p h

@[simp] lemma val_mkPolarity (p : Semiformula ℒₒᵣ ξ n) {Γ} (h : Hierarchy Γ m p) : (mkPolarity p Γ h).val = p := by cases Γ <;> rfl

@[simp] lemma hierarchy_sigma (p : 𝚺-[m].Semiformula ξ n) : Hierarchy 𝚺 m p.val := p.sigma_prop

@[simp] lemma hierarchy_pi (p : 𝚷-[m].Semiformula ξ n) : Hierarchy 𝚷 m p.val := p.pi_prop

@[simp] lemma hierarchy_zero {Γ Γ' m} (p : Γ-[0].Semiformula ξ n) : Hierarchy Γ' m p.val := by
  cases Γ
  · exact Hierarchy.of_zero p.sigma_prop
  · exact Hierarchy.of_zero p.pi_prop
  · cases p
    simp; exact Hierarchy.of_zero (sigma_prop _)

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M]

variable (M)

def ProperOn (p : 𝚫-[m].Semisentence n) : Prop :=
  ∀ (e : Fin n → M), Semiformula.Evalbm M e p.sigma.val ↔ Semiformula.Evalbm M e p.pi.val

def ProperWithParamOn (p : 𝚫-[m].Semiformula M n) : Prop :=
  ∀ (e : Fin n → M), Semiformula.Evalm M e id p.sigma.val ↔ Semiformula.Evalm M e id p.pi.val

variable {M}

lemma ProperOn.iff {p : 𝚫-[m].Semisentence n}
    (h : p.ProperOn M) (e : Fin n → M) :
    Semiformula.Evalbm M e p.sigma.val ↔ Semiformula.Evalbm M e p.pi.val := h e

lemma ProperWithParamOn.iff {p : 𝚫-[m].Semiformula M n}
    (h : p.ProperWithParamOn M) (e : Fin n → M) :
    Semiformula.Evalm M e id p.sigma.val ↔ Semiformula.Evalm (L := ℒₒᵣ) M e id p.pi.val := h e

lemma ProperOn.iff' {p : 𝚫-[m].Semisentence n}
    (h : p.ProperOn M) (e : Fin n → M) :
    Semiformula.Evalbm M e p.pi.val ↔ Semiformula.Evalbm M e p.val := by simp [←h.iff, val_sigma]

lemma ProperWithParamOn.iff' {p : 𝚫-[m].Semiformula M n}
    (h : p.ProperWithParamOn M) (e : Fin n → M) :
    Semiformula.Evalm M e id p.pi.val ↔ Semiformula.Evalm (L := ℒₒᵣ) M e id p.val := by simp [←h.iff, val_sigma]

def rew (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) : {Γ : HierarchySymbol} → Γ.Semiformula ξ₁ n₁ → Γ.Semiformula ξ₂ n₂
  | 𝚺-[_], mkSigma p hp => mkSigma (ω.hom p) (by simpa using hp)
  | 𝚷-[_], mkPi p hp    => mkPi (ω.hom p) (by simpa using hp)
  | 𝚫-[_], mkDelta p q  => mkDelta (p.rew ω) (q.rew ω)

@[simp] lemma val_rew (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) {Γ : HierarchySymbol} (p : Γ.Semiformula ξ₁ n₁) : (p.rew ω).val = ω.hom p.val := by
  rcases Γ with ⟨Γ, m⟩; rcases p with (_ | _ | ⟨⟨p, _⟩, ⟨q, _⟩⟩) <;> simp [rew]

@[simp] lemma ProperOn.rew {p : 𝚫-[m].Semisentence n₁} (h : p.ProperOn M) (ω : Rew ℒₒᵣ Empty n₁ Empty n₂) : (p.rew ω).ProperOn M := by
  rcases p; simp [ProperOn, Semiformula.rew, Semiformula.eval_rew, Function.comp, h.iff, Empty.eq_elim]
  intro e; exact h.iff _

@[simp] lemma ProperOn.rew' {p : 𝚫-[m].Semisentence n₁} (h : p.ProperOn M) (ω : Rew ℒₒᵣ Empty n₁ M n₂) : (p.rew ω).ProperWithParamOn M := by
  rcases p; intro e; simp [ProperOn, Semiformula.rew, Semiformula.eval_rew, Function.comp, h.iff, Empty.eq_elim]
  simpa using h.iff _

@[simp] lemma ProperWithParamOn.rew {p : 𝚫-[m].Semiformula M n₁}
    (h : p.ProperWithParamOn M) (f : Fin n₁ → Semiterm ℒₒᵣ M n₂) : (p.rew (Rew.substs f)).ProperWithParamOn M := by
  rcases p; intro e;
  simp [ProperOn, Semiformula.rew, Semiformula.eval_rew, Function.comp, h.iff, Empty.eq_elim]
  exact h.iff _

def emb : {Γ : HierarchySymbol} → Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | 𝚺-[_], mkSigma p hp => mkSigma (Semiformula.lMap Language.oringEmb p) (Hierarchy.oringEmb hp)
  | 𝚷-[_], mkPi p hp    => mkPi (Semiformula.lMap Language.oringEmb p) (Hierarchy.oringEmb hp)
  | 𝚫-[_], mkDelta p q  => mkDelta p.emb q.emb

@[simp] lemma val_emb {Γ : HierarchySymbol} (p : Γ.Semiformula ξ n) : p.emb.val = Semiformula.lMap Language.oringEmb p.val := by
  rcases Γ with ⟨Γ, m⟩; rcases p with (_ | _ | ⟨⟨p, _⟩, ⟨q, _⟩⟩) <;> simp [rew, val]

@[simp] lemma pi_emb (p : 𝚫-[m].Semiformula ξ n) : p.emb.pi = p.pi.emb := by cases p; rfl

@[simp] lemma sigma_emb (p : 𝚫-[m].Semiformula ξ n) : p.emb.sigma = p.sigma.emb := by cases p; rfl

@[simp] lemma emb_proper (p : 𝚫-[m].Semisentence n) : p.emb.ProperOn M ↔ p.ProperOn M := by
  rcases p; simp [ProperOn, emb]

@[simp] lemma emb_properWithParam (p : 𝚫-[m].Semiformula M n) : p.emb.ProperWithParamOn M ↔ p.ProperWithParamOn M := by
  rcases p; simp [ProperWithParamOn, emb]

def extd {Γ : HierarchySymbol} : Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | mkSigma p hp => mkSigma (Semiformula.lMap Language.oringEmb p) (Hierarchy.oringEmb hp)
  | mkPi p hp    => mkPi (Semiformula.lMap Language.oringEmb p) (Hierarchy.oringEmb hp)
  | mkDelta p q  => mkDelta p.extd q.extd

@[simp]
lemma eval_extd_iff {e ε} {p : Γ.Semiformula ξ n} :
    Semiformula.Evalm M e ε p.extd.val ↔ Semiformula.Evalm M e ε p.val := by
  induction p <;> simp [extd, *]

lemma ProperOn.extd {p : 𝚫-[m].Semisentence n} (h : p.ProperOn M) : p.extd.ProperOn M := by
  intro e; rcases p; simpa [Semiformula.extd] using h.iff e

lemma ProperWithParamOn.extd {p : 𝚫-[m].Semisentence n} (h : p.ProperOn M) : p.extd.ProperOn M := by
  intro e; rcases p; simpa [Semiformula.extd] using h.iff e

lemma sigma_extd_val (p : 𝚺-[m].Semiformula ξ n) :
    p.extd.val = Semiformula.lMap Language.oringEmb p.val := by
  rcases p; simp [extd]

lemma pi_extd_val (p : 𝚷-[m].Semiformula ξ n) :
    p.extd.val = Semiformula.lMap Language.oringEmb p.val := by
  rcases p; simp [extd]

lemma sigmaZero {Γ} (p : Γ-[0].Semiformula ξ k) : Hierarchy 𝚺 0 p.val :=
  match Γ with
  | 𝚺 => p.sigma_prop
  | 𝚷 => p.pi_prop.of_zero
  | 𝚫 => by simp [val_sigma]

def ofZero {Γ'} (p : Γ'-[0].Semiformula ξ k) : (Γ : HierarchySymbol) → Γ.Semiformula ξ k
  | 𝚺-[_] => mkSigma p.val p.sigmaZero.of_zero
  | 𝚷-[_] => mkPi p.val p.sigmaZero.of_zero
  | 𝚫-[_] => mkDelta (mkSigma p.val p.sigmaZero.of_zero) (mkPi p.val p.sigmaZero.of_zero)

def ofDeltaOne (p : 𝚫₁.Semiformula ξ k) : (Γ : SigmaPiDelta) → (m : ℕ) → Γ-[m+1].Semiformula ξ k
  | 𝚺, m => mkSigma p.sigma.val (p.sigma.sigma_prop.mono (by simp))
  | 𝚷, m => mkPi p.pi.val (p.pi.pi_prop.mono (by simp))
  | 𝚫, m => mkDelta (mkSigma p.sigma.val (p.sigma.sigma_prop.mono (by simp))) (mkPi p.pi.val (p.pi.pi_prop.mono (by simp)))

@[simp] lemma ofZero_val {Γ'} (p : Γ'-[0].Semiformula ξ n) (Γ) : (ofZero p Γ).val = p.val := by
  match Γ with
  | 𝚺-[_] => simp [ofZero]
  | 𝚷-[_] => simp [ofZero]
  | 𝚫-[_] => simp [ofZero]

@[simp] lemma ProperOn.of_zero (p : Γ'-[0].Semisentence k) (m) : (ofZero p 𝚫-[m]).ProperOn M := by
  simp [ProperOn, ofZero]

@[simp] lemma ProperWithParamOn.of_zero (p : Γ'-[0].Semiformula M k) (m) : (ofZero p 𝚫-[m]).ProperWithParamOn M := by
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
  | 𝚺-[m], p, q => mkSigma (p.val ⋏ q.val) (by simp)
  | 𝚷-[m], p, q => mkPi (p.val ⋏ q.val) (by simp)
  | 𝚫-[m], p, q => mkDelta (mkSigma (p.sigma.val ⋏ q.sigma.val) (by simp)) (mkPi (p.pi.val ⋏ q.pi.val) (by simp))

def or : {Γ : HierarchySymbol} → Γ.Semiformula ξ n → Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | 𝚺-[m], p, q => mkSigma (p.val ⋎ q.val) (by simp)
  | 𝚷-[m], p, q => mkPi (p.val ⋎ q.val) (by simp)
  | 𝚫-[m], p, q => mkDelta (mkSigma (p.sigma.val ⋎ q.sigma.val) (by simp)) (mkPi (p.pi.val ⋎ q.pi.val) (by simp))

def negSigma (p : 𝚺-[m].Semiformula ξ n) : 𝚷-[m].Semiformula ξ n := mkPi (~p.val) (by simp)

def negPi (p : 𝚷-[m].Semiformula ξ n) : 𝚺-[m].Semiformula ξ n := mkSigma (~p.val) (by simp)

def negDelta (p : 𝚫-[m].Semiformula ξ n) : 𝚫-[m].Semiformula ξ n := mkDelta (p.pi.negPi) (p.sigma.negSigma)

def ball (t : Semiterm ℒₒᵣ ξ n) : {Γ : HierarchySymbol} → Γ.Semiformula ξ (n + 1) → Γ.Semiformula ξ n
  | 𝚺-[m], p => mkSigma (∀[“#0 < !!(Rew.bShift t)”] p.val) (by simp)
  | 𝚷-[m], p => mkPi (∀[“#0 < !!(Rew.bShift t)”] p.val) (by simp)
  | 𝚫-[m], p =>
    mkDelta (mkSigma (∀[“#0 < !!(Rew.bShift t)”] p.sigma.val) (by simp)) (mkPi (∀[“#0 < !!(Rew.bShift t)”] p.pi.val) (by simp))

def bex (t : Semiterm ℒₒᵣ ξ n) : {Γ : HierarchySymbol} → Γ.Semiformula ξ (n + 1) → Γ.Semiformula ξ n
  | 𝚺-[m], p => mkSigma (∃[“#0 < !!(Rew.bShift t)”] p.val) (by simp)
  | 𝚷-[m], p => mkPi (∃[“#0 < !!(Rew.bShift t)”] p.val) (by simp)
  | 𝚫-[m], p =>
    mkDelta (mkSigma (∃[“#0 < !!(Rew.bShift t)”] p.sigma.val) (by simp)) (mkPi (∃[“#0 < !!(Rew.bShift t)”] p.pi.val) (by simp))

def all (p : 𝚷-[m + 1].Semiformula ξ (n + 1)) : 𝚷-[m + 1].Semiformula ξ n := mkPi (∀' p.val) p.pi_prop.all

def ex (p : 𝚺-[m + 1].Semiformula ξ (n + 1)) : 𝚺-[m + 1].Semiformula ξ n := mkSigma (∃' p.val) p.sigma_prop.ex

instance : Top (Γ.Semiformula ξ n) := ⟨verum⟩

instance : Bot (Γ.Semiformula ξ n) := ⟨falsum⟩

instance : Wedge (Γ.Semiformula ξ n) := ⟨and⟩

instance : Vee (Γ.Semiformula ξ n) := ⟨or⟩

instance : Tilde (𝚫-[m].Semiformula ξ n) := ⟨negDelta⟩

instance : LogicalConnective (𝚫-[m].Semiformula ξ n) where
  arrow p q := ~p ⋎ q

instance : ExQuantifier (𝚺-[m + 1].Semiformula ξ) := ⟨ex⟩

instance : UnivQuantifier (𝚷-[m + 1].Semiformula ξ) := ⟨all⟩

def substSigma (p : 𝚺-[m + 1].Semiformula ξ 1) (F : 𝚺-[m + 1].Semiformula ξ (n + 1)) :
    𝚺-[m + 1].Semiformula ξ n := (F ⋏ p.rew (Rew.substs ![#0])).ex

@[simp] lemma val_verum : (⊤ : Γ.Semiformula ξ n).val = ⊤ := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [val]

@[simp] lemma sigma_verum {m} : (⊤ : 𝚫-[m].Semiformula ξ n).sigma = ⊤ := by simp [Top.top, verum]

@[simp] lemma pi_verum {m} : (⊤ : 𝚫-[m].Semiformula ξ n).pi = ⊤ := by simp [Top.top, verum]

@[simp] lemma val_falsum : (⊥ : Γ.Semiformula ξ n).val = ⊥ := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [val]

@[simp] lemma sigma_falsum {m} : (⊥ : 𝚫-[m].Semiformula ξ n).sigma = ⊥ := by simp [Bot.bot, falsum]

@[simp] lemma pi_falsum {m} : (⊥ : 𝚫-[m].Semiformula ξ n).pi = ⊥ := by simp [Bot.bot, falsum]

@[simp] lemma val_and (p q : Γ.Semiformula ξ n) : (p ⋏ q).val = p.val ⋏ q.val := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [val, val_sigma]

@[simp] lemma sigma_and (p q : 𝚫-[m].Semiformula ξ n) : (p ⋏ q).sigma = p.sigma ⋏ q.sigma := by simp [Wedge.wedge, and]

@[simp] lemma pi_and (p q : 𝚫-[m].Semiformula ξ n) : (p ⋏ q).pi = p.pi ⋏ q.pi := by simp [Wedge.wedge, and]

@[simp] lemma val_or (p q : Γ.Semiformula ξ n) : (p ⋎ q).val = p.val ⋎ q.val := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [val, val_sigma]

@[simp] lemma sigma_or (p q : 𝚫-[m].Semiformula ξ n) : (p ⋎ q).sigma = p.sigma ⋎ q.sigma := by simp [Vee.vee, or]

@[simp] lemma pi_or (p q : 𝚫-[m].Semiformula ξ n) : (p ⋎ q).pi = p.pi ⋎ q.pi := by simp [Vee.vee, or]

@[simp] lemma val_negSigma {m} (p : 𝚺-[m].Semiformula ξ n) : p.negSigma.val = ~p.val := by simp [val, val_sigma]

@[simp] lemma val_negPi {m} (p : 𝚷-[m].Semiformula ξ n) : p.negPi.val = ~p.val := by simp [val, val_sigma]

lemma val_negDelta {m} (p : 𝚫-[m].Semiformula ξ n) : (~p).val = ~p.pi.val := by simp [Tilde.tilde, negDelta]

@[simp] lemma sigma_negDelta {m} (p : 𝚫-[m].Semiformula ξ n) : (~p).sigma = p.pi.negPi := by simp [Tilde.tilde, negDelta]

@[simp] lemma sigma_negPi {m} (p : 𝚫-[m].Semiformula ξ n) : (~p).pi = p.sigma.negSigma := by simp [Tilde.tilde, negDelta]

@[simp] lemma val_ball (t : Semiterm ℒₒᵣ ξ n) (p : Γ.Semiformula ξ (n + 1)) : (ball t p).val = ∀[“#0 < !!(Rew.bShift t)”] p.val := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [val, val_sigma]

@[simp] lemma val_bex (t : Semiterm ℒₒᵣ ξ n) (p : Γ.Semiformula ξ (n + 1)) : (bex t p).val = ∃[“#0 < !!(Rew.bShift t)”] p.val := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [val, val_sigma]

@[simp] lemma val_exSigma {m} (p : 𝚺-[m + 1].Semiformula ξ (n + 1)) : (ex p).val = ∃' p.val := rfl

@[simp] lemma val_allPi {m} (p : 𝚷-[m + 1].Semiformula ξ (n + 1)) : (all p).val = ∀' p.val := rfl

@[simp] lemma ProperOn.verum : (⊤ : 𝚫-[m].Semisentence k).ProperOn M := by intro e; simp

@[simp] lemma ProperOn.falsum : (⊥ : 𝚫-[m].Semisentence k).ProperOn M := by intro e; simp

lemma ProperOn.and {p q : 𝚫-[m].Semisentence k} (hp : p.ProperOn M) (hq : q.ProperOn M) : (p ⋏ q).ProperOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperOn.or {p q : 𝚫-[m].Semisentence k} (hp : p.ProperOn M) (hq : q.ProperOn M) : (p ⋎ q).ProperOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperOn.neg {p : 𝚫-[m].Semisentence k} (hp : p.ProperOn M) : (~p).ProperOn M := by
  intro e; simp [hp.iff]

lemma ProperOn.eval_neg {p : 𝚫-[m].Semisentence k} (hp : p.ProperOn M) (e) :
    Semiformula.Evalbm M e (~p).val ↔ ¬Semiformula.Evalbm M e p.val := by
  simp [val, ←val_sigma, hp.iff]

lemma ProperOn.ball {t} {p : 𝚫-[m + 1].Semisentence (k + 1)} (hp : p.ProperOn M) : (ball t p).ProperOn M := by
  intro e; simp [Semiformula.ball, hp.iff]

lemma ProperOn.bex {t} {p : 𝚫-[m + 1].Semisentence (k + 1)} (hp : p.ProperOn M) : (bex t p).ProperOn M := by
  intro e; simp [Semiformula.bex, hp.iff]

@[simp] lemma ProperWithParamOn.verum : (⊤ : 𝚫-[m].Semiformula M k).ProperWithParamOn M := by intro e; simp

@[simp] lemma ProperWithParamOn.falsum : (⊥ : 𝚫-[m].Semiformula M k).ProperWithParamOn M := by intro e; simp

lemma ProperWithParamOn.and {p q : 𝚫-[m].Semiformula M k}
    (hp : p.ProperWithParamOn M) (hq : q.ProperWithParamOn M) : (p ⋏ q).ProperWithParamOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperWithParamOn.or {p q : 𝚫-[m].Semiformula M k}
    (hp : p.ProperWithParamOn M) (hq : q.ProperWithParamOn M) : (p ⋎ q).ProperWithParamOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperWithParamOn.neg {p : 𝚫-[m].Semiformula M k} (hp : p.ProperWithParamOn M) : (~p).ProperWithParamOn M := by
  intro e; simp [hp.iff]

lemma ProperWithParamOn.eval_neg {p : 𝚫-[m].Semiformula M k} (hp : p.ProperWithParamOn M) (e) :
    Semiformula.Evalm M e id (~p).val ↔ ¬Semiformula.Evalm M e id p.val := by
  simp [val, ←val_sigma, hp.iff]

lemma ProperWithParamOn.ball {t} {p : 𝚫-[m].Semiformula M (k + 1)}
    (hp : p.ProperWithParamOn M) : (ball t p).ProperWithParamOn M := by
  intro e; simp [Semiformula.ball, hp.iff]

lemma ProperWithParamOn.bex {t} {p : 𝚫-[m].Semiformula M (k + 1)}
    (hp : p.ProperWithParamOn M) : (bex t p).ProperWithParamOn M := by
  intro e; simp [Semiformula.bex, hp.iff]

def graphDelta (p : 𝚺-[m].Semiformula ξ (k + 1)) : 𝚫-[m].Semiformula ξ (k + 1) :=
  match m with
  | 0     => p.ofZero _
  | m + 1 => mkDelta p (mkPi “x | ∀ y, !p.val y ⋯ → y = x” (by simp))

@[simp] lemma graphDelta_val (p : 𝚺-[m].Semiformula ξ (k + 1)) : p.graphDelta.val = p.val := by cases m <;> simp [graphDelta]

end Semiformula

end HierarchySymbol

end LO.FirstOrder.Arith
