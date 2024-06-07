import Arithmetization.Vorspiel.Lemmata
import Arithmetization.Definability.Init
import Arithmetization.Vorspiel.Graph
import Logic.FirstOrder.Arith.StrictHierarchy
import Aesop

namespace LO.FirstOrder.Arith

abbrev HierarchySymbol := SigmaPiDelta × ℕ

abbrev HierarchySymbol.sigmaZero : HierarchySymbol := (𝚺, 0)

abbrev HierarchySymbol.piZero : HierarchySymbol := (𝚷, 0)

abbrev HierarchySymbol.deltaZero : HierarchySymbol := (𝚫, 0)

abbrev HierarchySymbol.sigmaOne : HierarchySymbol := (𝚺, 1)

abbrev HierarchySymbol.piOne : HierarchySymbol := (𝚷, 1)

abbrev HierarchySymbol.deltaOne : HierarchySymbol := (𝚫, 1)

notation "𝚺₀" => HierarchySymbol.sigmaZero

notation "𝚷₀" => HierarchySymbol.piZero

notation "𝚫₀" => HierarchySymbol.deltaZero

notation "𝚺₁" => HierarchySymbol.sigmaOne

notation "𝚷₁" => HierarchySymbol.piOne

notation "𝚫₁" => HierarchySymbol.deltaOne

namespace HierarchySymbol
/-
inductive Rel : HierarchySymbol → HierarchySymbol → Prop where
  | delta_le_sigma (m)      : Rel (𝚫, m) (𝚺, m)
  | delta_le_pi (m)         : Rel (𝚫, m) (𝚷, m)
  | sigma_le_delta_succ (m) : Rel (𝚺, m) (𝚫, m + 1)
  | pi_le_delta_succ (m)    : Rel (𝚷, m) (𝚫, m + 1)
  | sigma_le_delta_zero     : Rel (𝚺, 0) (𝚫, 0)
  | pi_le_delta_zero        : Rel (𝚷, 0) (𝚫, 0)

/-- Order structure of arithmetical hierarchy -/
protected inductive LE : HierarchySymbol → HierarchySymbol → Prop where
  | of_rel {Γ₁ Γ₂}          : Rel Γ₁ Γ₂ → HierarchySymbol.LE Γ₁ Γ₂
  | refl (Γ)                : HierarchySymbol.LE Γ Γ
  | trans {Γ₁ Γ₂ Γ₃}        : HierarchySymbol.LE Γ₁ Γ₂ → HierarchySymbol.LE Γ₂ Γ₃ → HierarchySymbol.LE Γ₁ Γ₃

instance : LE HierarchySymbol := ⟨HierarchySymbol.LE⟩

instance : Preorder HierarchySymbol where
  le_refl := HierarchySymbol.LE.refl
  le_trans := fun _ _ _ ↦ HierarchySymbol.LE.trans

@[simp] lemma delta_le : (Γ : SigmaPiDelta) → (m : ℕ) → (𝚫, m) ≤ (Γ, m)
  | 𝚺, m => HierarchySymbol.LE.of_rel (Rel.delta_le_sigma m)
  | 𝚷, m => HierarchySymbol.LE.of_rel (Rel.delta_le_pi m)
  | 𝚫, m => by rfl

@[simp] lemma le_delta_succ : (Γ : SigmaPiDelta) → (m : ℕ) → (Γ, m) ≤ (𝚫, m + 1)
  | 𝚺, m => HierarchySymbol.LE.of_rel (Rel.sigma_le_delta_succ m)
  | 𝚷, m => HierarchySymbol.LE.of_rel (Rel.pi_le_delta_succ m)
  | 𝚫, m => le_trans (delta_le 𝚺 m) (HierarchySymbol.LE.of_rel (Rel.sigma_le_delta_succ m))

@[simp] lemma le_succ (Γ₁ Γ₂ : SigmaPiDelta) (m : ℕ) : (Γ₁, m) ≤ (Γ₂, m + 1) :=
  le_trans (le_delta_succ Γ₁ m) (delta_le Γ₂ (m + 1))

lemma le_of_le (Γ : SigmaPiDelta) {m n : ℕ} (h : m ≤ n) : (Γ, m) ≤ (Γ, n) := by
  have : n = m + (n - m) := (Nat.add_sub_of_le h).symm
  generalize e : n - m = d
  rw [e] at this; rcases this; clear e
  induction' d with d IH
  · rfl
  · exact le_trans (IH <| by simp) (by simp [Nat.add_succ])

lemma le_of_lt (Γ₁ Γ₂ : SigmaPiDelta) {m n : ℕ} (h : m < n) : (Γ₁, m) ≤ (Γ₂, n) := by
  cases' n with n
  · simp_all
  · exact le_trans (le_of_le Γ₁ (by simpa [Nat.lt_succ] using h)) (le_succ Γ₁ Γ₂ n)

@[simp] lemma zero_le (Γ₁ Γ₂ : SigmaPiDelta) : (Γ₁, 0) ≤ (Γ₂, 0) :=
  match Γ₁, Γ₂ with
  | 𝚺, 𝚺 => by rfl
  | 𝚺, 𝚷 => le_trans (HierarchySymbol.LE.of_rel Rel.sigma_le_delta_zero) (by simp)
  | 𝚺, 𝚫 => HierarchySymbol.LE.of_rel Rel.sigma_le_delta_zero
  | 𝚷, 𝚺 => le_trans (HierarchySymbol.LE.of_rel Rel.pi_le_delta_zero) (by simp)
  | 𝚷, 𝚷 => by rfl
  | 𝚷, 𝚫 => HierarchySymbol.LE.of_rel Rel.pi_le_delta_zero
  | 𝚫, 𝚺 => by simp
  | 𝚫, 𝚷 => by simp
  | 𝚫, 𝚫 => by rfl
-/

end HierarchySymbol

end Arith

def Defined {k} (R : (Fin k → M) → Prop) [Structure L M] (p : Semisentence L k) : Prop :=
  ∀ v, R v ↔ Semiformula.Evalbm M v p

def DefinedWithParam {k} (R : (Fin k → M) → Prop) [Structure L M] (p : Semiformula L M k) : Prop :=
  ∀ v, R v ↔ Semiformula.Evalm M v id p

lemma Defined.iff [Structure L M] {k} {R : (Fin k → M) → Prop} {p : Semisentence L k} (h : Defined R p) (v) :
    Semiformula.Evalbm M v p ↔ R v := (h v).symm

lemma DefinedWithParam.iff [Structure L M] {k} {R : (Fin k → M) → Prop} {p : Semiformula L M k} (h : DefinedWithParam R p) (v) :
    Semiformula.Evalm M v id p ↔ R v := (h v).symm

namespace Arith

variable (L : Language.{u}) [L.ORing] (ξ : Type v) (n : ℕ)

inductive HSemiformula : HierarchySymbol → Type _ where
  | mkSigma {m} : (p : Semiformula L ξ n) → Hierarchy 𝚺 m p → HSemiformula (𝚺, m)
  | mkPi {m}    : (p : Semiformula L ξ n) → Hierarchy 𝚷 m p → HSemiformula (𝚷, m)
  | mkDelta {m} : HSemiformula (𝚺, m) → HSemiformula (𝚷, m) → HSemiformula (𝚫, m)

abbrev HSemisentence (Γ : HierarchySymbol) := HSemiformula L Empty n Γ

scoped[LO.FirstOrder.Arith] notation Γ "-Semisentence " n => HSemisentence ℒₒᵣ n Γ

variable {L ξ n}

namespace HSemiformula

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [Structure L M] [Structure.ORing L M]

def val : HSemiformula L ξ n Γ → Semiformula L ξ n
  | mkSigma p _ => p
  | mkPi    p _ => p
  | mkDelta p _ => p.val

@[simp] lemma val_mkSigma (p : Semiformula L ξ n) (hp : Hierarchy 𝚺 m p) : (mkSigma p hp).val = p := rfl

@[simp] lemma val_mkPi (p : Semiformula L ξ n) (hp : Hierarchy 𝚷 m p) : (mkPi p hp).val = p := rfl

@[simp] lemma val_mkDelta (p : HSemiformula L ξ n (𝚺, m)) (q : HSemiformula L ξ n (𝚷, m)) : (mkDelta p q).val = p.val := rfl

@[simp] lemma sigma_prop : (p : HSemiformula L ξ n (𝚺, m)) → Hierarchy 𝚺 m p.val
  | mkSigma _ h => h

@[simp] lemma pi_prop : (p : HSemiformula L ξ n (𝚷, m)) → Hierarchy 𝚷 m p.val
  | mkPi _ h => h

@[simp] lemma polarity_prop : {Γ : Polarity} → (p : HSemiformula L ξ n (Γ, m)) → Hierarchy Γ m p.val
  | 𝚺, p => p.sigma_prop
  | 𝚷, p => p.pi_prop

def sigma : HSemiformula L ξ n (𝚫, m) → HSemiformula L ξ n (𝚺, m)
  | mkDelta p _ => p

@[simp] lemma sigma_mkDelta (p : HSemiformula L ξ n (𝚺, m)) (q : HSemiformula L ξ n (𝚷, m)) : (mkDelta p q).sigma = p := rfl

def pi : HSemiformula L ξ n (𝚫, m) → HSemiformula L ξ n (𝚷, m)
  | mkDelta _ p => p

@[simp] lemma pi_mkDelta (p : HSemiformula L ξ n (𝚺, m)) (q : HSemiformula L ξ n (𝚷, m)) : (mkDelta p q).pi = q := rfl

lemma val_sigma (p : HSemiformula L ξ n (𝚫, m)) : p.sigma.val = p.val := by rcases p; simp

def mkPolarity (p : Semiformula L ξ n) : (Γ : Polarity) → Hierarchy Γ m p → HSemiformula L ξ n (Γ, m)
  | 𝚺, h => mkSigma p h
  | 𝚷, h => mkPi p h

@[simp] lemma val_mkPolarity (p : Semiformula L ξ n) {Γ} (h : Hierarchy Γ m p) : (mkPolarity p Γ h).val = p := by cases Γ <;> rfl

variable (M)

def ProperOn (p : HSemisentence L n (𝚫, m)) : Prop :=
  ∀ (e : Fin n → M), Semiformula.Evalbm M e p.sigma.val ↔ Semiformula.Evalbm M e p.pi.val

def ProperWithParamOn (p : HSemiformula L M n (𝚫, m)) : Prop :=
  ∀ (e : Fin n → M), Semiformula.Evalm M e id p.sigma.val ↔ Semiformula.Evalm M e id p.pi.val

variable {M}

lemma ProperOn.iff {p : HSemisentence L n (𝚫, m)}
    (h : p.ProperOn M) (e : Fin n → M) :
    Semiformula.Evalbm M e p.sigma.val ↔ Semiformula.Evalbm M e p.pi.val := h e

lemma ProperWithParamOn.iff {p : HSemiformula L M n (𝚫, m)}
    (h : p.ProperWithParamOn M) (e : Fin n → M) :
    Semiformula.Evalm M e id p.sigma.val ↔ Semiformula.Evalm (L := L) M e id p.pi.val := h e

lemma ProperOn.iff' {p : HSemisentence L n (𝚫, m)}
    (h : p.ProperOn M) (e : Fin n → M) :
    Semiformula.Evalbm M e p.pi.val ↔ Semiformula.Evalbm M e p.val := by simp [←h.iff, val_sigma]

lemma ProperWithParamOn.iff' {p : HSemiformula L M n (𝚫, m)}
    (h : p.ProperWithParamOn M) (e : Fin n → M) :
    Semiformula.Evalm M e id p.pi.val ↔ Semiformula.Evalm (L := L) M e id p.val := by simp [←h.iff, val_sigma]

def rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) : {Γ : HierarchySymbol} → HSemiformula L ξ₁ n₁ Γ → HSemiformula L ξ₂ n₂ Γ
  | (𝚺, _), mkSigma p hp => mkSigma (ω.hom p) (by simpa using hp)
  | (𝚷, _), mkPi p hp    => mkPi (ω.hom p) (by simpa using hp)
  | (𝚫, _), mkDelta p q  => mkDelta (p.rew ω) (q.rew ω)

@[simp] lemma val_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) {Γ} (p : HSemiformula L ξ₁ n₁ Γ) : (p.rew ω).val = ω.hom p.val := by
  rcases Γ with ⟨Γ, m⟩; rcases p with (_ | _ | ⟨⟨p, _⟩, ⟨q, _⟩⟩) <;> simp [rew]

@[simp] lemma ProperOn.rew {p : HSemisentence L n₁ (𝚫, m)} (h : p.ProperOn M) (ω : Rew L Empty n₁ Empty n₂) : (p.rew ω).ProperOn M := by
  rcases p; simp [ProperOn, HSemiformula.rew, Semiformula.eval_rew, Function.comp, h.iff, Empty.eq_elim]
  intro e; exact h.iff _

@[simp] lemma ProperWithParamOn.rew {p : HSemiformula L M n₁ (𝚫, m)}
    (h : p.ProperWithParamOn M) (f : Fin n₁ → Semiterm L M n₂) : (p.rew (Rew.substs f)).ProperWithParamOn M := by
  rcases p; intro e;
  simp [ProperOn, HSemiformula.rew, Semiformula.eval_rew, Function.comp, h.iff, Empty.eq_elim]
  exact h.iff _

variable (L)

def emb : {Γ : HierarchySymbol} → HSemiformula ℒₒᵣ ξ n Γ → HSemiformula L ξ n Γ
  | (𝚺, _), mkSigma p hp => mkSigma (Semiformula.lMap Language.oringEmb p) (Hierarchy.oringEmb hp)
  | (𝚷, _), mkPi p hp    => mkPi (Semiformula.lMap Language.oringEmb p) (Hierarchy.oringEmb hp)
  | (𝚫, _), mkDelta p q  => mkDelta p.emb q.emb

variable {L}

@[simp] lemma val_emb {Γ} (p : HSemiformula ℒₒᵣ ξ n Γ) : (p.emb L).val = Semiformula.lMap Language.oringEmb p.val := by
  rcases Γ with ⟨Γ, m⟩; rcases p with (_ | _ | ⟨⟨p, _⟩, ⟨q, _⟩⟩) <;> simp [rew, val]

@[simp] lemma pi_emb (p : HSemiformula ℒₒᵣ ξ n (𝚫, m)) : (p.emb L).pi = p.pi.emb L := by cases p; rfl

@[simp] lemma sigma_emb (p : HSemiformula ℒₒᵣ ξ n (𝚫, m)) : (p.emb L).sigma = p.sigma.emb L := by cases p; rfl

@[simp] lemma emb_proper (p : HSemisentence ℒₒᵣ n (𝚫, m)) : (p.emb L).ProperOn M ↔ p.ProperOn M := by
  rcases p; simp [ProperOn, emb]

@[simp] lemma emb_properWithParam (p : HSemiformula ℒₒᵣ M n (𝚫, m)) : (p.emb L).ProperWithParamOn M ↔ p.ProperWithParamOn M := by
  rcases p; simp [ProperWithParamOn, emb]

variable (L)

def extd : HSemiformula ℒₒᵣ ξ n Γ → HSemiformula L ξ n Γ
  | mkSigma p hp => mkSigma (Semiformula.lMap Language.oringEmb p) (Hierarchy.oringEmb hp)
  | mkPi p hp    => mkPi (Semiformula.lMap Language.oringEmb p) (Hierarchy.oringEmb hp)
  | mkDelta p q  => mkDelta p.extd q.extd

variable {L}

@[simp]
lemma eval_extd_iff {e ε} {p : HSemiformula ℒₒᵣ ξ n Γ} :
    Semiformula.Evalm M e ε (p.extd L).val ↔ Semiformula.Evalm M e ε p.val := by
  induction p <;> simp [extd, *]

lemma ProperOn.extd {p : HSemisentence ℒₒᵣ n (𝚫, m)} (h : p.ProperOn M) : (p.extd L).ProperOn M := by
  intro e; rcases p; simpa [HSemiformula.extd] using h.iff e

lemma ProperWithParamOn.extd {p : HSemisentence ℒₒᵣ n (𝚫, m)} (h : p.ProperOn M) : (p.extd L).ProperOn M := by
  intro e; rcases p; simpa [HSemiformula.extd] using h.iff e

lemma sigma_extd_val (p : HSemiformula ℒₒᵣ ξ n (𝚺, m)) :
    (p.extd L).val = Semiformula.lMap Language.oringEmb p.val := by
  rcases p; simp [extd]

lemma pi_extd_val (p : HSemiformula ℒₒᵣ ξ n (𝚷, m)) :
    (p.extd L).val = Semiformula.lMap Language.oringEmb p.val := by
  rcases p; simp [extd]

/-
def ofRel : {Γ₁ Γ₂ : HierarchySymbol} → HierarchySymbol.Rel Γ₁ Γ₂ → HSemiformula L ξ k Γ₁ → HSemiformula L ξ k Γ₂
  | (𝚺, m), (𝚫, n + 1), H, (mkSigma p hp)             =>
    have : n = m := by cases H; rfl
    mkDelta (mkSigma p <| Hierarchy.strict_mono hp 𝚺 (by simp [this])) (mkPi p <| Hierarchy.strict_mono hp 𝚷 (by simp [this]))
  | (𝚷, m), (𝚫, n + 1), H, (mkPi p hp)                =>
    have : n = m := by cases H; rfl
    mkDelta (mkSigma p <| Hierarchy.strict_mono hp 𝚺 (by simp [this])) (mkPi p <| Hierarchy.strict_mono hp 𝚷 (by simp [this]))
  | (𝚫, m), (𝚺, n),     H, (mkDelta (mkSigma p hp) _) =>
    have : n = m := by cases H; rfl
    mkSigma p (by simpa [this] using hp)
  | (𝚫, m), (𝚷, n),     H, (mkDelta _ (mkPi p hp))    =>
    have : n = m := by cases H; rfl
    mkPi p (by simpa [this] using hp)
  | (𝚷, m), (𝚫, 0),     H, (mkPi p hp)                =>
    have : m = 0 := by cases H; rfl
    mkDelta (mkSigma p <| Hierarchy.of_zero (by simpa [this] using hp)) (mkPi p <| by simpa [this] using hp)
  | (𝚺, m), (𝚫, 0),     H, (mkSigma p hp)             =>
    have : m = 0 := by cases H; rfl
    mkDelta (mkSigma p <| by simpa [this] using hp) (mkPi p <| Hierarchy.of_zero (by simpa [this] using hp))
-/

lemma sigmaZero (p : HSemiformula L ξ k (Γ, 0)) : Hierarchy 𝚺 0 p.val :=
  match Γ with
  | 𝚺 => p.sigma_prop
  | 𝚷 => p.pi_prop.of_zero
  | 𝚫 => by simpa [val_sigma] using p.sigma.sigma_prop

def ofZero (p : HSemiformula L ξ k (Γ', 0)) : (Γ : HierarchySymbol) → HSemiformula L ξ k Γ
  | (𝚺, _) => mkSigma p.val p.sigmaZero.of_zero
  | (𝚷, _) => mkPi p.val p.sigmaZero.of_zero
  | (𝚫, _) => mkDelta (mkSigma p.val p.sigmaZero.of_zero) (mkPi p.val p.sigmaZero.of_zero)

def ofDeltaOne (p : HSemiformula L ξ k 𝚫₁) : (Γ : SigmaPiDelta) → (m : ℕ) → HSemiformula L ξ k (Γ, m + 1)
  | 𝚺, m => mkSigma p.sigma.val (p.sigma.sigma_prop.mono (by simp))
  | 𝚷, m => mkPi p.pi.val (p.pi.pi_prop.mono (by simp))
  | 𝚫, m => mkDelta (mkSigma p.sigma.val (p.sigma.sigma_prop.mono (by simp))) (mkPi p.pi.val (p.pi.pi_prop.mono (by simp)))

@[simp] lemma ofZero_val (p : HSemiformula L ξ k (Γ', 0)) (Γ) : (ofZero p Γ).val = p.val := by
  match Γ with
  | (𝚺, _) => simp [ofZero]
  | (𝚷, _) => simp [ofZero]
  | (𝚫, _) => simp [ofZero]

@[simp] lemma ProperOn.of_zero (p : HSemisentence L k (Γ', 0)) (m) : (ofZero p (𝚫, m)).ProperOn M := by
  simp [ProperOn, ofZero]

@[simp] lemma ProperWithParamOn.of_zero (p : HSemiformula L M k (Γ', 0)) (m) : (ofZero p (𝚫, m)).ProperWithParamOn M := by
  simp [ProperWithParamOn, ofZero]

def verum : {Γ : HierarchySymbol} → HSemiformula L ξ n Γ
  | (𝚺, m) => mkSigma ⊤ (by simp)
  | (𝚷, m) => mkPi ⊤ (by simp)
  | (𝚫, m) => mkDelta (mkSigma ⊤ (by simp)) (mkPi ⊤ (by simp))

def falsum : {Γ : HierarchySymbol} → HSemiformula L ξ n Γ
  | (𝚺, m) => mkSigma ⊥ (by simp)
  | (𝚷, m) => mkPi ⊥ (by simp)
  | (𝚫, m) => mkDelta (mkSigma ⊥ (by simp)) (mkPi ⊥ (by simp))

def and : {Γ : HierarchySymbol} → HSemiformula L ξ n Γ → HSemiformula L ξ n Γ → HSemiformula L ξ n Γ
  | (𝚺, m), p, q => mkSigma (p.val ⋏ q.val) (by simp)
  | (𝚷, m), p, q => mkPi (p.val ⋏ q.val) (by simp)
  | (𝚫, m), p, q => mkDelta (mkSigma (p.sigma.val ⋏ q.sigma.val) (by simp)) (mkPi (p.pi.val ⋏ q.pi.val) (by simp))

def or : {Γ : HierarchySymbol} → HSemiformula L ξ n Γ → HSemiformula L ξ n Γ → HSemiformula L ξ n Γ
  | (𝚺, m), p, q => mkSigma (p.val ⋎ q.val) (by simp)
  | (𝚷, m), p, q => mkPi (p.val ⋎ q.val) (by simp)
  | (𝚫, m), p, q => mkDelta (mkSigma (p.sigma.val ⋎ q.sigma.val) (by simp)) (mkPi (p.pi.val ⋎ q.pi.val) (by simp))

def negSigma (p : HSemiformula L ξ n (𝚺, m)) : HSemiformula L ξ n (𝚷, m) := mkPi (~p.val) (by simp)

def negPi (p : HSemiformula L ξ n (𝚷, m)) : HSemiformula L ξ n (𝚺, m) := mkSigma (~p.val) (by simp)

def negDelta (p : HSemiformula L ξ n (𝚫, m)) : HSemiformula L ξ n (𝚫, m) := mkDelta (p.pi.negPi) (p.sigma.negSigma)

def ball (t : Semiterm L ξ n) : {Γ : HierarchySymbol} → HSemiformula L ξ (n + 1) Γ → HSemiformula L ξ n Γ
  | (𝚺, m), p => mkSigma (∀[“#0 < !!(Rew.bShift t)”] p.val) (by simp)
  | (𝚷, m), p => mkPi (∀[“#0 < !!(Rew.bShift t)”] p.val) (by simp)
  | (𝚫, m), p =>
    mkDelta (mkSigma (∀[“#0 < !!(Rew.bShift t)”] p.sigma.val) (by simp)) (mkPi (∀[“#0 < !!(Rew.bShift t)”] p.pi.val) (by simp))

def bex (t : Semiterm L ξ n) : {Γ : HierarchySymbol} → HSemiformula L ξ (n + 1) Γ → HSemiformula L ξ n Γ
  | (𝚺, m), p => mkSigma (∃[“#0 < !!(Rew.bShift t)”] p.val) (by simp)
  | (𝚷, m), p => mkPi (∃[“#0 < !!(Rew.bShift t)”] p.val) (by simp)
  | (𝚫, m), p =>
    mkDelta (mkSigma (∃[“#0 < !!(Rew.bShift t)”] p.sigma.val) (by simp)) (mkPi (∃[“#0 < !!(Rew.bShift t)”] p.pi.val) (by simp))

def all (p : HSemiformula L ξ (n + 1) (𝚷, m + 1)) : HSemiformula L ξ n (𝚷, m + 1) := mkPi (∀' p.val) p.pi_prop.all

def ex (p : HSemiformula L ξ (n + 1) (𝚺, m + 1)) : HSemiformula L ξ n (𝚺, m + 1) := mkSigma (∃' p.val) p.sigma_prop.ex

instance : Top (HSemiformula L ξ n Γ) := ⟨verum⟩

instance : Bot (HSemiformula L ξ n Γ) := ⟨falsum⟩

instance : Wedge (HSemiformula L ξ n Γ) := ⟨and⟩

instance : Vee (HSemiformula L ξ n Γ) := ⟨or⟩

instance : Tilde (HSemiformula L ξ n (𝚫, m)) := ⟨negDelta⟩

instance : LogicalConnective (HSemiformula L ξ n (𝚫, m)) where
  arrow p q := ~p ⋎ q

instance : ExQuantifier (HSemiformula L ξ · (𝚺, m + 1)) := ⟨ex⟩

instance : UnivQuantifier (HSemiformula L ξ · (𝚷, m + 1)) := ⟨all⟩

def substSigma (p : HSemiformula L ξ 1 (𝚺, m + 1)) (F : HSemiformula L ξ (n + 1) (𝚺, m + 1)) :
    HSemiformula L ξ n (𝚺, m + 1) := (F ⋏ p.rew [→ #0]).ex

@[simp] lemma val_verum {Γ}: (⊤ : HSemiformula L ξ n Γ).val = ⊤ := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [val]

@[simp] lemma sigma_verum {m} : (⊤ : HSemiformula L ξ n (𝚫, m)).sigma = ⊤ := by simp [Top.top, verum]

@[simp] lemma pi_verum {m} : (⊤ : HSemiformula L ξ n (𝚫, m)).pi = ⊤ := by simp [Top.top, verum]

@[simp] lemma val_falsum {Γ}: (⊥ : HSemiformula L ξ n Γ).val = ⊥ := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [val]

@[simp] lemma sigma_falsum {m} : (⊥ : HSemiformula L ξ n (𝚫, m)).sigma = ⊥ := by simp [Bot.bot, falsum]

@[simp] lemma pi_falsum {m} : (⊥ : HSemiformula L ξ n (𝚫, m)).pi = ⊥ := by simp [Bot.bot, falsum]

@[simp] lemma val_and {Γ} (p q : HSemiformula L ξ n Γ) : (p ⋏ q).val = p.val ⋏ q.val := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [val, val_sigma]

@[simp] lemma sigma_and (p q : HSemiformula L ξ n (𝚫, m)) : (p ⋏ q).sigma = p.sigma ⋏ q.sigma := by simp [Wedge.wedge, and]

@[simp] lemma pi_and (p q : HSemiformula L ξ n (𝚫, m)) : (p ⋏ q).pi = p.pi ⋏ q.pi := by simp [Wedge.wedge, and]

@[simp] lemma val_or {Γ} (p q : HSemiformula L ξ n Γ) : (p ⋎ q).val = p.val ⋎ q.val := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [val, val_sigma]

@[simp] lemma sigma_or (p q : HSemiformula L ξ n (𝚫, m)) : (p ⋎ q).sigma = p.sigma ⋎ q.sigma := by simp [Vee.vee, or]

@[simp] lemma pi_or (p q : HSemiformula L ξ n (𝚫, m)) : (p ⋎ q).pi = p.pi ⋎ q.pi := by simp [Vee.vee, or]

@[simp] lemma val_negSigma {m} (p : HSemiformula L ξ n (𝚺, m)) : p.negSigma.val = ~p.val := by simp [val, val_sigma]

@[simp] lemma val_negPi {m} (p : HSemiformula L ξ n (𝚷, m)) : p.negPi.val = ~p.val := by simp [val, val_sigma]

lemma val_negDelta {m} (p : HSemiformula L ξ n (𝚫, m)) : (~p).val = ~p.pi.val := by simp [Tilde.tilde, negDelta]

@[simp] lemma sigma_negDelta {m} (p : HSemiformula L ξ n (𝚫, m)) : (~p).sigma = p.pi.negPi := by simp [Tilde.tilde, negDelta]

@[simp] lemma sigma_negPi {m} (p : HSemiformula L ξ n (𝚫, m)) : (~p).pi = p.sigma.negSigma := by simp [Tilde.tilde, negDelta]

@[simp] lemma val_ball {Γ} (t : Semiterm L ξ n) (p : HSemiformula L ξ (n + 1) Γ) : (ball t p).val = ∀[“#0 < !!(Rew.bShift t)”] p.val := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [val, val_sigma]

@[simp] lemma val_bex {Γ} (t : Semiterm L ξ n) (p : HSemiformula L ξ (n + 1) Γ) : (bex t p).val = ∃[“#0 < !!(Rew.bShift t)”] p.val := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [val, val_sigma]

@[simp] lemma val_exSigma {m} (p : HSemiformula L ξ (n + 1) (𝚺, (m + 1))) : (ex p).val = ∃' p.val := rfl

@[simp] lemma val_allPi {m} (p : HSemiformula L ξ (n + 1) (𝚷, (m + 1))) : (all p).val = ∀' p.val := rfl

@[simp] lemma ProperOn.verum : (⊤ : HSemisentence L k (𝚫, m)).ProperOn M := by intro e; simp

@[simp] lemma ProperOn.falsum : (⊥ : HSemisentence L k (𝚫, m)).ProperOn M := by intro e; simp

lemma ProperOn.and {p q : HSemisentence L k (𝚫, m)} (hp : p.ProperOn M) (hq : q.ProperOn M) : (p ⋏ q).ProperOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperOn.or {p q : HSemisentence L k (𝚫, m)} (hp : p.ProperOn M) (hq : q.ProperOn M) : (p ⋎ q).ProperOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperOn.neg {p : HSemisentence L k (𝚫, m)} (hp : p.ProperOn M) : (~p).ProperOn M := by
  intro e; simp [hp.iff]

lemma ProperOn.eval_neg {p : HSemisentence L k (𝚫, m)} (hp : p.ProperOn M) (e) :
    Semiformula.Evalbm M e (~p).val ↔ ¬Semiformula.Evalbm M e p.val := by
  simp [val, ←val_sigma, hp.iff]

lemma ProperOn.ball {t} {p : HSemisentence L (k + 1) (𝚫, m)} (hp : p.ProperOn M) : (ball t p).ProperOn M := by
  intro e; simp [HSemiformula.ball, hp.iff]

lemma ProperOn.bex {t} {p : HSemisentence L (k + 1) (𝚫, m)} (hp : p.ProperOn M) : (bex t p).ProperOn M := by
  intro e; simp [HSemiformula.bex, hp.iff]

@[simp] lemma ProperWithParamOn.verum : (⊤ : HSemiformula L M k (𝚫, m)).ProperWithParamOn M := by intro e; simp

@[simp] lemma ProperWithParamOn.falsum : (⊥ : HSemiformula L M k (𝚫, m)).ProperWithParamOn M := by intro e; simp

lemma ProperWithParamOn.and {p q : HSemiformula L M k (𝚫, m)}
    (hp : p.ProperWithParamOn M) (hq : q.ProperWithParamOn M) : (p ⋏ q).ProperWithParamOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperWithParamOn.or {p q : HSemiformula L M k (𝚫, m)}
    (hp : p.ProperWithParamOn M) (hq : q.ProperWithParamOn M) : (p ⋎ q).ProperWithParamOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma ProperWithParamOn.neg {p : HSemiformula L M k (𝚫, m)} (hp : p.ProperWithParamOn M) : (~p).ProperWithParamOn M := by
  intro e; simp [hp.iff]

lemma ProperWithParamOn.eval_neg {p : HSemiformula L M k (𝚫, m)} (hp : p.ProperWithParamOn M) (e) :
    Semiformula.Evalm M e id (~p).val ↔ ¬Semiformula.Evalm M e id p.val := by
  simp [val, ←val_sigma, hp.iff]

lemma ProperWithParamOn.ball {t} {p : HSemiformula L M (k + 1) (𝚫, m)}
    (hp : p.ProperWithParamOn M) : (ball t p).ProperWithParamOn M := by
  intro e; simp [HSemiformula.ball, hp.iff]

lemma ProperWithParamOn.bex {t} {p : HSemiformula L M (k + 1) (𝚫, m)}
    (hp : p.ProperWithParamOn M) : (bex t p).ProperWithParamOn M := by
  intro e; simp [HSemiformula.bex, hp.iff]

def graphDelta (p : HSemiformula L ξ (k + 1) (𝚺, m)) : HSemiformula L ξ (k + 1) (𝚫, m) :=
  match m with
  | 0     => p.ofZero _
  | m + 1 => mkDelta p (mkPi “∀ (!(Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.val) → #0 = #1)” (by simp))

@[simp] lemma graphDelta_val (p : HSemiformula L ξ (k + 1) (𝚺, m)) : p.graphDelta.val = p.val := by cases m <;> simp [graphDelta]

end HSemiformula

namespace Definability

namespace HSemiformula

variable (ξ : Type*) (n) (Γ : SigmaPiDelta) (m : ℕ)

@[simp] lemma hierarchy_sigma (p : HSemiformula L ξ n (𝚺, m)) : Hierarchy 𝚺 m p.val := p.sigma_prop

@[simp] lemma hierarchy_pi (p : HSemiformula L ξ n (𝚷, m)) : Hierarchy 𝚷 m p.val := p.pi_prop

@[simp] lemma hierarchy_zero {Γ Γ' m} (p : HSemiformula L ξ n (Γ, 0)) : Hierarchy Γ' m p.val := by
  cases Γ
  · exact Hierarchy.of_zero p.sigma_prop
  · exact Hierarchy.of_zero p.pi_prop
  · cases p
    simp; exact Hierarchy.of_zero (HSemiformula.sigma_prop _)

end HSemiformula

end Definability

namespace Model

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐏𝐀⁻] [Structure L M] [Structure.ORing L M] [Structure.Monotone L M]

variable {Γ : HierarchySymbol}

open Definability

def Defined (R : (Fin k → M) → Prop) : {Γ : HierarchySymbol} → HSemisentence L k Γ → Prop
  | (𝚺, _), p => FirstOrder.Defined R p.val
  | (𝚷, _), p => FirstOrder.Defined R p.val
  | (𝚫, _), p => p.ProperOn M ∧ FirstOrder.Defined R p.val

def DefinedWithParam (R : (Fin k → M) → Prop) : {Γ : HierarchySymbol} → HSemiformula L M k Γ → Prop
  | (𝚺, _), p => FirstOrder.DefinedWithParam R p.val
  | (𝚷, _), p => FirstOrder.DefinedWithParam R p.val
  | (𝚫, _), p => p.ProperWithParamOn M ∧ FirstOrder.DefinedWithParam R p.val

variable (L Γ)

class Definable {k} (P : (Fin k → M) → Prop) : Prop where
  definable : ∃ p : HSemiformula L M k Γ, DefinedWithParam P p

abbrev DefinedPred (P : M → Prop) (p : HSemisentence L 1 Γ) : Prop :=
  Defined (λ v ↦ P (v 0)) p

abbrev DefinedRel (R : M → M → Prop) (p : HSemisentence L 2 Γ) : Prop :=
  Defined (λ v ↦ R (v 0) (v 1)) p

abbrev DefinedRel₃ (R : M → M → M → Prop) (p : HSemisentence L 3 Γ) : Prop :=
  Defined (λ v ↦ R (v 0) (v 1) (v 2)) p

abbrev DefinedRel₄ (R : M → M → M → M → Prop) (p : HSemisentence L 4 Γ) : Prop :=
  Defined (λ v ↦ R (v 0) (v 1) (v 2) (v 3)) p

abbrev DefinedFunction {k} (f : (Fin k → M) → M) (p : HSemisentence L (k + 1) Γ) : Prop :=
  Defined (fun v => v 0 = f (v ·.succ)) p

abbrev DefinedFunction₁ (f : M → M) (p : HSemisentence L 2 Γ) : Prop :=
  DefinedFunction L Γ (fun v => f (v 0)) p

abbrev DefinedFunction₂ (f : M → M → M) (p : HSemisentence L 3 Γ) : Prop :=
  DefinedFunction L Γ (fun v => f (v 0) (v 1)) p

abbrev DefinedFunction₃ (f : M → M → M → M) (p : HSemisentence L 4 Γ) : Prop :=
  DefinedFunction L Γ (fun v => f (v 0) (v 1) (v 2)) p

abbrev DefinablePred (P : M → Prop) : Prop := Definable L Γ (k := 1) (fun v ↦ P (v 0))

abbrev DefinableRel (P : M → M → Prop) : Prop := Definable L Γ (k := 2) (fun v ↦ P (v 0) (v 1))

abbrev DefinableRel₃ (P : M → M → M → Prop) : Prop := Definable L Γ (k := 3) (fun v ↦ P (v 0) (v 1) (v 2))

abbrev DefinableRel₄ (P : M → M → M → M → Prop) : Prop := Definable L Γ (k := 4) (fun v ↦ P (v 0) (v 1) (v 2) (v 3))

abbrev DefinableFunction (f : (Fin k → M) → M) : Prop := Definable L Γ (k := k + 1) (fun v ↦ v 0 = f (v ·.succ))

abbrev DefinableFunction₁ (f : M → M) : Prop := DefinableFunction L Γ (k := 1) (fun v ↦ f (v 0))

abbrev DefinableFunction₂ (f : M → M → M) : Prop := DefinableFunction L Γ (k := 2) (fun v ↦ f (v 0) (v 1))

abbrev DefinableFunction₃ (f : M → M → M → M) : Prop := DefinableFunction L Γ (k := 3) (fun v ↦ f (v 0) (v 1) (v 2))

notation Γ "-Predicate " P " via " p => DefinedPred ℒₒᵣ Γ P p

notation Γ "-Relation " P " via " p => DefinedRel ℒₒᵣ Γ P p

notation Γ "-Relation₃ " P " via " p => DefinedRel₃ ℒₒᵣ Γ P p

notation Γ "-Relation₄ " P " via " p => DefinedRel₄ ℒₒᵣ Γ P p

notation Γ "-Function₁ " f " via " p => DefinedFunction₁ ℒₒᵣ Γ f p

notation Γ "-Function₂ " f " via " p => DefinedFunction₂ ℒₒᵣ Γ f p

notation Γ "-Function₃ " f " via " p => DefinedFunction₃ ℒₒᵣ Γ f p

notation Γ "-Predicate " P => DefinablePred ℒₒᵣ Γ P

notation Γ "-Relation " P => DefinableRel ℒₒᵣ Γ P

notation Γ "-Relation₃ " P => DefinableRel₃ ℒₒᵣ Γ P

notation Γ "-Relation₄ " P => DefinableRel₄ ℒₒᵣ Γ P

notation Γ "-Function₁ " f => DefinableFunction₁ ℒₒᵣ Γ f

notation Γ "-Function₂ " f => DefinableFunction₂ ℒₒᵣ Γ f

notation Γ "-Function₃ " f => DefinableFunction₃ ℒₒᵣ Γ f

variable {L Γ}

section

variable {k} {P Q : (Fin k → M) → Prop}

namespace Defined

lemma df {R : (Fin k → M) → Prop} {Γ} {p : HSemisentence L k Γ} (h : Defined R p) : FirstOrder.Defined R p.val :=
  match Γ with
  | (𝚺, _) => h
  | (𝚷, _) => h
  | (𝚫, _) => h.2

lemma proper {R : (Fin k → M) → Prop} {m} {p : HSemisentence L k (𝚫, m)} (h : Defined R p) : p.ProperOn M := h.1

lemma of_zero {R : (Fin k → M) → Prop} {Γ} {p : HSemisentence L k (𝚺, 0)} (h : Defined R p) : Defined R (p.ofZero Γ) :=
  match Γ with
  | (𝚺, m) => by intro _; simp [h.iff]
  | (𝚷, m) => by intro _; simp [h.iff]
  | (𝚫, m) => ⟨by simp, by intro _; simp [h.iff]⟩

lemma emb {R : (Fin k → M) → Prop} {Γ} {p : HSemisentence ℒₒᵣ k Γ} (h : Defined R p) : Defined R (p.emb L) :=
  match Γ with
  | (𝚺, m) => by intro _; simp [h.iff]
  | (𝚷, m) => by intro _; simp [h.iff]
  | (𝚫, m) => ⟨by simpa using h.proper, by intro _; simp [h.df.iff]⟩

lemma of_iff {P Q : (Fin k → M) → Prop} (h : ∀ x, P x ↔ Q x)
    {p : HSemisentence L k Γ} (H : Defined Q p) : Defined P p := by
  rwa [show P = Q from by funext v; simp [h]]

lemma to_definable (p : HSemisentence L k Γ) (hP : Defined P p) : Definable L Γ P := ⟨p.rew Rew.emb, by
  match Γ with
  | (𝚺, _) => intro; simp [hP.iff]
  | (𝚷, _) => intro; simp [hP.iff]
  | (𝚫, _) => exact ⟨
    fun v ↦ by rcases p; simpa [HSemiformula.rew] using hP.proper.rew Rew.emb v,
    by intro; simp [hP.df.iff]⟩⟩

lemma to_definable₀ (p : HSemisentence L k (𝚺, 0)) (hP : Defined P p) :
    Definable L Γ P := Defined.to_definable (p.ofZero Γ) hP.of_zero

lemma to_definable_oRing (p : HSemisentence ℒₒᵣ k Γ) (hP : Defined P p) :
    Definable L Γ P := Defined.to_definable (p.emb L) hP.emb

lemma to_definable_oRing₀ (p : 𝚺₀-Semisentence k) (hP : Defined P p) :
    Definable L Γ P := Defined.to_definable₀ (p.emb L) hP.emb

end Defined

namespace DefinedFunction

lemma of_eq {f g : (Fin k → M) → M} (h : ∀ x, f x = g x)
    {p : HSemisentence L (k + 1) Γ} (H : DefinedFunction L Γ f p) : DefinedFunction L Γ g p :=
  Defined.of_iff (by intro; simp [h]) H

lemma graph_delta {f : (Fin k → M) → M} {p : HSemisentence L (k + 1) (𝚺, m)}
    (h : DefinedFunction L (𝚺, m) f p) : DefinedFunction L (𝚫, m) f p.graphDelta :=
  ⟨by cases' m with m <;> simp [HSemiformula.graphDelta]
      intro e; simp [Empty.eq_elim, h.df.iff]
      rw [eq_comm],
   by intro v; simp [h.df.iff]⟩

end DefinedFunction

namespace DefinedWithParam

lemma df {R : (Fin k → M) → Prop} {Γ} {p : HSemiformula L M k Γ} (h : DefinedWithParam R p) : FirstOrder.DefinedWithParam R p.val :=
  match Γ with
  | (𝚺, _) => h
  | (𝚷, _) => h
  | (𝚫, _) => h.2

lemma proper {R : (Fin k → M) → Prop} {m} {p : HSemiformula L M k (𝚫, m)} (h : DefinedWithParam R p) : p.ProperWithParamOn M := h.1

lemma of_zero {R : (Fin k → M) → Prop} {Γ} {p : HSemiformula L M k (Γ', 0)}
    (h : DefinedWithParam R p) : DefinedWithParam R (p.ofZero Γ) :=
  match Γ with
  | (𝚺, m) => by intro _; simp [h.df.iff]
  | (𝚷, m) => by intro _; simp [h.df.iff]
  | (𝚫, m) => ⟨by simp , by intro _; simp [h.df.iff]⟩

lemma of_deltaOne {R : (Fin k → M) → Prop} {Γ m} {p : HSemiformula L M k 𝚫₁}
    (h : DefinedWithParam R p) : DefinedWithParam R (p.ofDeltaOne Γ m) :=
  match Γ with
  | 𝚺 => by intro _; simp [HSemiformula.ofDeltaOne, h.df.iff, HSemiformula.val_sigma]
  | 𝚷 => by intro _; simp [HSemiformula.ofDeltaOne, h.df.iff, h.proper.iff']
  | 𝚫 => ⟨by intro _; simp [HSemiformula.ofDeltaOne, h.df.iff, HSemiformula.val_sigma, h.proper.iff'],
    by intro _; simp [HSemiformula.ofDeltaOne, h.df.iff, HSemiformula.val_sigma]⟩

lemma emb {R : (Fin k → M) → Prop} {Γ} {p : HSemiformula ℒₒᵣ M k Γ}
    (h : DefinedWithParam R p) : DefinedWithParam R (p.emb L) :=
  match Γ with
  | (𝚺, m) => by intro _; simp [h.iff]
  | (𝚷, m) => by intro _; simp [h.iff]
  | (𝚫, m) => ⟨by simpa using h.proper, by intro _; simp [h.df.iff]⟩

lemma of_iff {P Q : (Fin k → M) → Prop} (h : ∀ x, P x ↔ Q x)
    {p : HSemiformula L M k Γ} (H : DefinedWithParam Q p) : DefinedWithParam P p := by
  rwa [show P = Q from by funext v; simp [h]]

lemma to_definable {p : HSemiformula L M k Γ} (h : DefinedWithParam P p) : Definable L Γ P := ⟨p, h⟩

lemma to_definable₀ {p : HSemiformula L M k (Γ', 0)}
    (h : DefinedWithParam P p) : Definable L Γ P := ⟨p.ofZero Γ, h.of_zero⟩

lemma to_definable_deltaOne {p : HSemiformula L M k 𝚫₁} {Γ m}
    (h : DefinedWithParam P p) : Definable L (Γ, m + 1) P := ⟨p.ofDeltaOne Γ m, h.of_deltaOne⟩

lemma retraction {p : HSemiformula L M k Γ} (hp : DefinedWithParam P p) (f : Fin k → Fin l) :
    DefinedWithParam (fun v ↦ P fun i ↦ v (f i)) (p.rew <| Rew.substs fun x ↦ #(f x)) :=
  match Γ with
  | (𝚺, _) => by intro; simp [hp.df.iff]
  | (𝚷, _) => by intro; simp [hp.df.iff]
  | (𝚫, _) => ⟨hp.proper.rew _, by intro; simp [hp.df.iff]⟩

@[simp] lemma verum :
    DefinedWithParam (fun _ ↦ True) (⊤ : HSemiformula L M k Γ) :=
  match Γ with
  | (𝚺, m) => by intro v; simp
  | (𝚷, m) => by intro v; simp
  | (𝚫, m) => ⟨by simp, by intro v; simp⟩

@[simp] lemma falsum :
    DefinedWithParam (fun _ ↦ False) (⊥ : HSemiformula L M k Γ) :=
  match Γ with
| (𝚺, m) => by intro v; simp
  | (𝚷, m) => by intro v; simp
  | (𝚫, m) => ⟨by simp, by intro v; simp⟩

lemma and {p q : HSemiformula L M k Γ} (hp : DefinedWithParam P p) (hq : DefinedWithParam Q q) :
    DefinedWithParam (fun x ↦ P x ∧ Q x) (p ⋏ q) :=
  match Γ with
  | (𝚺, m) => by intro v; simp [hp.iff, hq.iff]
  | (𝚷, m) => by intro v; simp [hp.iff, hq.iff]
  | (𝚫, m) => ⟨hp.proper.and hq.proper, by intro v; simp [hp.df.iff, hq.df.iff]⟩

lemma or {p q : HSemiformula L M k Γ} (hp : DefinedWithParam P p) (hq : DefinedWithParam Q q) :
    DefinedWithParam (fun x ↦ P x ∨ Q x) (p ⋎ q) :=
  match Γ with
  | (𝚺, m) => by intro v; simp [hp.iff, hq.iff]
  | (𝚷, m) => by intro v; simp [hp.iff, hq.iff]
  | (𝚫, m) => ⟨hp.proper.or hq.proper, by intro v; simp [hp.df.iff, hq.df.iff]⟩

lemma negSigma {p : HSemiformula L M k (𝚺, m)} (hp : DefinedWithParam P p) :
    DefinedWithParam (fun x ↦ ¬P x) p.negSigma := by intro v; simp [hp.iff]

lemma negPi {p : HSemiformula L M k (𝚷, m)} (hp : DefinedWithParam P p) :
    DefinedWithParam (fun x ↦ ¬P x) p.negPi := by intro v; simp [hp.iff]

lemma not {p : HSemiformula L M k (𝚫, m)} (hp : DefinedWithParam P p) :
    DefinedWithParam (fun x ↦ ¬P x) (~p) := ⟨hp.proper.neg, by intro v; simp [hp.proper.eval_neg, hp.df.iff]⟩

lemma imp {p q : HSemiformula L M k (𝚫, m)} (hp : DefinedWithParam P p) (hq : DefinedWithParam Q q) :
    DefinedWithParam (fun x ↦ P x → Q x) (p ⟶ q) := (hp.not.or hq).of_iff (by intro x; simp [imp_iff_not_or])

lemma iff {p q : HSemiformula L M k (𝚫, m)} (hp : DefinedWithParam P p) (hq : DefinedWithParam Q q) :
    DefinedWithParam (fun x ↦ P x ↔ Q x) (p ⟷ q) := ((hp.imp hq).and (hq.imp hp)).of_iff <| by intro v; simp [iff_iff_implies_and_implies]

lemma ball {P : (Fin (k + 1) → M) → Prop} {p : HSemiformula L M (k + 1) Γ}
    (hp : DefinedWithParam P p) (t : Semiterm L M k) :
    DefinedWithParam (fun v ↦ ∀ x < t.valm M v id, P (x :> v)) (HSemiformula.ball t p) :=
  match Γ with
  | (𝚺, m) => by intro v; simp [hp.df.iff]
  | (𝚷, m) => by intro v; simp [hp.df.iff]
  | (𝚫, m) => ⟨hp.proper.ball, by intro v; simp [hp.df.iff]⟩

lemma bex {P : (Fin (k + 1) → M) → Prop} {p : HSemiformula L M (k + 1) Γ}
    (hp : DefinedWithParam P p) (t : Semiterm L M k) :
    DefinedWithParam (fun v ↦ ∃ x < t.valm M v id, P (x :> v)) (HSemiformula.bex t p) :=
  match Γ with
  | (𝚺, m) => by intro v; simp [hp.df.iff]
  | (𝚷, m) => by intro v; simp [hp.df.iff]
  | (𝚫, m) => ⟨hp.proper.bex, by intro v; simp [hp.df.iff]⟩

lemma ex {P : (Fin (k + 1) → M) → Prop} {p : HSemiformula L M (k + 1) (𝚺, m + 1)}
    (hp : DefinedWithParam P p) :
    DefinedWithParam (fun v ↦ ∃ x, P (x :> v)) p.ex := by intro _; simp [hp.df.iff]

lemma all {P : (Fin (k + 1) → M) → Prop} {p : HSemiformula L M (k + 1) (𝚷, m + 1)}
    (hp : DefinedWithParam P p) :
    DefinedWithParam (fun v ↦ ∀ x, P (x :> v)) p.all := by intro _; simp [hp.df.iff]

end DefinedWithParam

namespace Definable

lemma mkPolarity {P : (Fin k → M) → Prop} {Γ : Polarity}
    (p : Semiformula L M k) (hp : Hierarchy Γ m p) (hP : ∀ v, P v ↔ Semiformula.Evalm M v id p) : Definable L (Γ, m) P :=
  match Γ with
  | 𝚺 => ⟨.mkSigma p hp, by intro v; simp [hP]⟩
  | 𝚷 => ⟨.mkPi p hp, by intro v; simp [hP]⟩

lemma of_iff (Q : (Fin k → M) → Prop) (h : ∀ x, P x ↔ Q x) (H : Definable L Γ Q) : Definable L Γ P := by
  rwa [show P = Q from by funext v; simp [h]]

lemma of_oRing (h : Definable ℒₒᵣ Γ P) : Definable L Γ P := by
  rcases h with ⟨p, hP⟩; exact ⟨p.emb L, hP.emb⟩

lemma of_delta (h : Definable L (𝚫, m) P) {Γ} : Definable L (Γ, m) P := by
  rcases h with ⟨p, h⟩
  match Γ with
  | 𝚺 => exact ⟨p.sigma, by intro v; simp [HSemiformula.val_sigma, h.df.iff]⟩
  | 𝚷 => exact ⟨p.pi, by intro v; simp [←h.proper v, HSemiformula.val_sigma, h.df.iff]⟩
  | 𝚫 => exact ⟨p, h⟩

instance [Definable L (𝚫, m) P] (Γ) : Definable L (Γ, m) P := of_delta inferInstance

lemma of_sigma_of_pi (hσ : Definable L (𝚺, m) P) (hπ : Definable L (𝚷, m) P) : Definable L (𝚫, m) P := by
  rcases hσ with ⟨p, hp⟩; rcases hπ with ⟨q, hq⟩
  exact ⟨.mkDelta p q, by intro v; simp [hp.df.iff, hq.df.iff], by intro v; simp [hp.df.iff]⟩

instance [Definable ℒₒᵣ Γ P] : Definable L Γ P := Definable.of_oRing inferInstance

lemma of_zero (h : Definable L (Γ', 0) P) (Γ) : Definable L Γ P := by
  rcases h with ⟨⟨p, hp⟩⟩; exact hp.to_definable₀

lemma of_deltaOne (h : Definable L 𝚫₁ P) (Γ m) : Definable L (Γ, m + 1) P := by
  rcases h with ⟨⟨p, hp⟩⟩; exact hp.to_definable_deltaOne

instance [Definable L 𝚺₀ P] (Γ) : Definable L Γ P := Definable.of_zero (Γ' := 𝚺) inferInstance Γ

lemma retraction (h : Definable L Γ P) (f : Fin k → Fin n) :
    Definable L Γ fun v ↦ P (fun i ↦ v (f i)) := by
  rcases h with ⟨p, h⟩
  exact ⟨p.rew (Rew.substs (fun i ↦ #(f i))),
  match Γ with
  | (𝚺, _) => by intro; simp [h.df.iff]
  | (𝚷, _) => by intro; simp [h.df.iff]
  | (𝚫, _) => ⟨h.proper.rew _, by intro; simp [h.df.iff]⟩⟩

lemma const {P : Prop} : Definable L Γ (fun _ : Fin k → M ↦ P) := of_zero (by
  by_cases hP : P
  · exact ⟨.mkSigma ⊤ (by simp), by intro; simp[hP]⟩
  · exact ⟨.mkSigma ⊥ (by simp), by intro; simp[hP]⟩) Γ

lemma and (h₁ : Definable L Γ P) (h₂ : Definable L Γ Q) :
    Definable L Γ (fun v ↦ P v ∧ Q v) := by
  rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
  exact ⟨p₁ ⋏ p₂, h₁.and h₂⟩

lemma or (h₁ : Definable L Γ P) (h₂ : Definable L Γ Q) :
    Definable L Γ (fun v ↦ P v ∨ Q v) := by
  rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
  exact ⟨p₁ ⋎ p₂, h₁.or h₂⟩

lemma not {Γ} (h : Definable L (SigmaPiDelta.alt Γ, m) P) :
    Definable L (Γ, m) (fun v ↦ ¬P v) := by
  match Γ with
  | 𝚺 => rcases h with ⟨p, h⟩; exact ⟨p.negPi, h.negPi⟩
  | 𝚷 => rcases h with ⟨p, h⟩; exact ⟨p.negSigma, h.negSigma⟩
  | 𝚫 => rcases h with ⟨p, h⟩; exact ⟨p.negDelta, h.not⟩

lemma imp {Γ} (h₁ : Definable L (SigmaPiDelta.alt Γ, m) P) (h₂ : Definable L (Γ, m) Q) :
    Definable L (Γ, m) (fun v ↦ P v → Q v) := by
  match Γ with
  | 𝚺 =>
    rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
    exact ⟨p₁.negPi.or p₂, (h₁.negPi.or h₂).of_iff (fun x ↦ by simp [imp_iff_not_or])⟩
  | 𝚷 =>
    rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
    exact ⟨p₁.negSigma.or p₂, (h₁.negSigma.or h₂).of_iff (fun x ↦ by simp [imp_iff_not_or])⟩
  | 𝚫 =>
    rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩; exact ⟨p₁ ⟶ p₂, h₁.imp h₂⟩

lemma iff (h₁ : Definable L (𝚫, m) P) (h₂ : Definable L (𝚫, m) Q) {Γ} :
    Definable L (Γ, m) (fun v ↦ P v ↔ Q v) :=
  .of_delta (by rcases h₁ with ⟨p, hp⟩; rcases h₂ with ⟨q, hq⟩; exact ⟨p ⟷ q, hp.iff hq⟩)

lemma all {P : (Fin k → M) → M → Prop} (h : Definable L (𝚷, s + 1) (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L (𝚷, s + 1) (fun v ↦ ∀ x, P v x) := by
  rcases h with ⟨p, hp⟩
  exact ⟨.mkPi (∀' p.val) (by simp), by intro v; simp [hp.df.iff]⟩

lemma ex {P : (Fin k → M) → M → Prop} (h : Definable L (𝚺, s + 1) (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L (𝚺, s + 1) (fun v ↦ ∃ x, P v x) := by
  rcases h with ⟨p, hp⟩
  exact ⟨.mkSigma (∃' p.val) (by simp), by intro v; simp [hp.df.iff]⟩

lemma comp₁ {k} {P : M → Prop} {f : (Fin k → M) → M} (hf : DefinableFunction L (𝚺, m + 1) f)
    {Γ : SigmaPiDelta} (hP : DefinablePred L (Γ, m + 1) P) : Definable L (Γ, m + 1) (fun v ↦ P (f v)) := by
  match Γ with
  | 𝚺 =>
    rcases hP with ⟨p, hp⟩; rcases hf with ⟨pf, hpf⟩
    exact ⟨(pf ⋏ (p.rew [→ #0])).ex, by intro v; simp [hp.df.iff, hpf.df.iff]⟩
  | 𝚷 =>
    rcases hP with ⟨p, hp⟩; rcases hf with ⟨pf, hpf⟩
    exact ⟨(pf.negSigma ⋎ (p.rew [→ #0])).all, by intro v; simp [hp.df.iff, hpf.df.iff, ←imp_iff_not_or]⟩
  | 𝚫 =>
    rcases hP with ⟨p, hp⟩; rcases hf with ⟨pf, hpf⟩
    exact of_sigma_of_pi
      ⟨(pf ⋏ (p.sigma.rew [→ #0])).ex, by intro v; simp [hp.df.iff, hpf.df.iff, HSemiformula.val_sigma]  ⟩
      ⟨(pf.negSigma ⋎ (p.pi.rew [→ #0])).all, by intro v; simp [hp.df.iff, hpf.df.iff, ←imp_iff_not_or, hp.proper.iff']⟩

lemma comp₁' {k} {P : M → Prop} {f : (Fin k → M) → M} (hf : DefinableFunction L (𝚺, m + 1) f)
    {Γ : SigmaPiDelta} [DefinablePred L (Γ, m + 1) P] : Definable L (Γ, m + 1) (fun v ↦ P (f v)) :=
  comp₁ hf inferInstance

lemma comp₂ {k} {P : M → M → Prop} {f g : (Fin k → M) → M}
    (hf : DefinableFunction L (𝚺, m + 1) f) (hg : DefinableFunction L (𝚺, m + 1) g)
    {Γ : SigmaPiDelta} (hP : DefinableRel L (Γ, m + 1) P) : Definable L (Γ, m + 1) (fun v ↦ P (f v) (g v)) := by
  match Γ with
  | 𝚺 =>
    rcases hP with ⟨p, hp⟩; rcases hf with ⟨pf, hpf⟩; rcases hg with ⟨pg, hpg⟩
    exact ⟨(pf.rew (Rew.substs $ #0 :> (#·.succ.succ)) ⋏ pg.rew (Rew.substs $ #1 :> (#·.succ.succ)) ⋏ (p.rew [→ #0, #1])).ex.ex, by
      intro v; simp [hp.df.iff, hpf.df.iff, hpg.df.iff]⟩
  | 𝚷 =>
    rcases hP with ⟨p, hp⟩; rcases hf with ⟨pf, hpf⟩; rcases hg with ⟨pg, hpg⟩
    exact ⟨((pf.rew (Rew.substs $ #0 :> (#·.succ.succ))).negSigma ⋎ (pg.rew (Rew.substs $ #1 :> (#·.succ.succ))).negSigma ⋎ (p.rew [→ #0, #1])).all.all, by
      intro v; simp [hp.df.iff, hpf.df.iff, hpg.df.iff, ←imp_iff_not_or]⟩
  | 𝚫 =>
    rcases hP with ⟨p, hp⟩; rcases hf with ⟨pf, hpf⟩; rcases hg with ⟨pg, hpg⟩
    exact of_sigma_of_pi
      ⟨(pf.rew (Rew.substs $ #0 :> (#·.succ.succ)) ⋏ pg.rew (Rew.substs $ #1 :> (#·.succ.succ)) ⋏ (p.sigma.rew [→ #0, #1])).ex.ex, by
        intro v; simp [hp.df.iff, hpf.df.iff, hpg.df.iff, HSemiformula.val_sigma]⟩
      ⟨((pf.rew (Rew.substs $ #0 :> (#·.succ.succ))).negSigma
          ⋎ (pg.rew (Rew.substs $ #1 :> (#·.succ.succ))).negSigma ⋎ (p.pi.rew [→ #0, #1])).all.all, by
        intro v; simp [hp.df.iff, hpf.df.iff, hpg.df.iff, ←imp_iff_not_or, hp.proper.iff']⟩

lemma comp₂' {k} {P : M → M → Prop} {f g : (Fin k → M) → M}
    (hf : DefinableFunction L (𝚺, m + 1) f) (hg : DefinableFunction L (𝚺, m + 1) g)
    {Γ : SigmaPiDelta} [DefinableRel L (Γ, m + 1) P] : Definable L (Γ, m + 1) (fun v ↦ P (f v) (g v)) :=
  comp₂ hf hg inferInstance

lemma comp₃ {k} {P : M → M → M → Prop} {f₁ f₂ f₃ : (Fin k → M) → M}
    (hf₁ : DefinableFunction L (𝚺, m + 1) f₁) (hf₂ : DefinableFunction L (𝚺, m + 1) f₂) (hf₃ : DefinableFunction L (𝚺, m + 1) f₃)
    {Γ : SigmaPiDelta} (hP : DefinableRel₃ L (Γ, m + 1) P) : Definable L (Γ, m + 1) (fun v ↦ P (f₁ v) (f₂ v) (f₃ v)) := by
  rcases hf₁ with ⟨pf₁, hpf₁⟩; rcases hf₂ with ⟨pf₂, hpf₂⟩; rcases hf₃ with ⟨pf₃, hpf₃⟩
  match Γ with
  | 𝚺 =>
    rcases hP with ⟨p, hp⟩
    exact
      ⟨(  pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ))
        ⋏ pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ))
        ⋏ pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ))
        ⋏ (p.rew [→ #0, #1, #2])).ex.ex.ex, by
      intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff]⟩
  | 𝚷 =>
    rcases hP with ⟨p, hp⟩
    exact
      ⟨(  (pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ))).negSigma
        ⋎ (pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ))).negSigma
        ⋎ (pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ))).negSigma
        ⋎ (p.rew [→ #0, #1, #2])).all.all.all, by
      intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, ←imp_iff_not_or]⟩
  | 𝚫 =>
    rcases hP with ⟨p, hp⟩
    exact of_sigma_of_pi
      ⟨(  pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ))
        ⋏ pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ))
        ⋏ pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ))
        ⋏ (p.sigma.rew [→ #0, #1, #2])).ex.ex.ex, by
        intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, HSemiformula.val_sigma]⟩
      ⟨(  (pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ))).negSigma
        ⋎ (pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ))).negSigma
        ⋎ (pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ))).negSigma
        ⋎ (p.pi.rew [→ #0, #1, #2])).all.all.all, by
        intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, ←imp_iff_not_or, hp.proper.iff']⟩

lemma comp₃' {k} {P : M → M → M → Prop} {f₁ f₂ f₃ : (Fin k → M) → M}
    (hf₁ : DefinableFunction L (𝚺, m + 1) f₁) (hf₂ : DefinableFunction L (𝚺, m + 1) f₂) (hf₃ : DefinableFunction L (𝚺, m + 1) f₃)
    {Γ : SigmaPiDelta} [DefinableRel₃ L (Γ, m + 1) P] : Definable L (Γ, m + 1) (fun v ↦ P (f₁ v) (f₂ v) (f₃ v)) :=
  comp₃ hf₁ hf₂ hf₃ inferInstance

lemma comp₄ {k} {P : M → M → M → M → Prop} {f₁ f₂ f₃ f₄ : (Fin k → M) → M}
    (hf₁ : DefinableFunction L (𝚺, m + 1) f₁) (hf₂ : DefinableFunction L (𝚺, m + 1) f₂)
    (hf₃ : DefinableFunction L (𝚺, m + 1) f₃) (hf₄ : DefinableFunction L (𝚺, m + 1) f₄)
    {Γ : SigmaPiDelta} (hP : DefinableRel₄ L (Γ, m + 1) P) : Definable L (Γ, m + 1) (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v)) := by
  rcases hf₁ with ⟨pf₁, hpf₁⟩; rcases hf₂ with ⟨pf₂, hpf₂⟩; rcases hf₃ with ⟨pf₃, hpf₃⟩; rcases hf₄ with ⟨pf₄, hpf₄⟩
  match Γ with
  | 𝚺 =>
    rcases hP with ⟨p, hp⟩
    exact
      ⟨(  pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ.succ))
        ⋏ pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ.succ))
        ⋏ pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ.succ))
        ⋏ pf₄.rew (Rew.substs $ #3 :> (#·.succ.succ.succ.succ))
        ⋏ (p.rew [→ #0, #1, #2, #3])).ex.ex.ex.ex, by
      intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, hpf₄.df.iff]⟩
  | 𝚷 =>
    rcases hP with ⟨p, hp⟩
    exact
      ⟨(  (pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ.succ))).negSigma
        ⋎ (pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ.succ))).negSigma
        ⋎ (pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ.succ))).negSigma
        ⋎ (pf₄.rew (Rew.substs $ #3 :> (#·.succ.succ.succ.succ))).negSigma
        ⋎ (p.rew [→ #0, #1, #2, #3])).all.all.all.all, by
      intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, hpf₄.df.iff, ←imp_iff_not_or]⟩
  | 𝚫 =>
    rcases hP with ⟨p, hp⟩
    exact of_sigma_of_pi
      ⟨(  pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ.succ))
        ⋏ pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ.succ))
        ⋏ pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ.succ))
        ⋏ pf₄.rew (Rew.substs $ #3 :> (#·.succ.succ.succ.succ))
        ⋏ (p.sigma.rew [→ #0, #1, #2, #3])).ex.ex.ex.ex, by
        intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, hpf₄.df.iff, HSemiformula.val_sigma]⟩
      ⟨(  (pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ.succ))).negSigma
        ⋎ (pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ.succ))).negSigma
        ⋎ (pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ.succ))).negSigma
        ⋎ (pf₄.rew (Rew.substs $ #3 :> (#·.succ.succ.succ.succ))).negSigma
        ⋎ (p.pi.rew [→ #0, #1, #2, #3])).all.all.all.all, by
        intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, hpf₄.df.iff, ←imp_iff_not_or, hp.proper.iff']⟩

lemma comp₄' {k} {P : M → M → M → M → Prop} {f₁ f₂ f₃ f₄ : (Fin k → M) → M}
    (hf₁ : DefinableFunction L (𝚺, m + 1) f₁) (hf₂ : DefinableFunction L (𝚺, m + 1) f₂)
    (hf₃ : DefinableFunction L (𝚺, m + 1) f₃) (hf₄ : DefinableFunction L (𝚺, m + 1) f₄)
    {Γ : SigmaPiDelta} [DefinableRel₄ L (Γ, m + 1) P] : Definable L (Γ, m + 1) (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  comp₄ hf₁ hf₂ hf₃ hf₄ inferInstance

end Definable

lemma DefinablePred.of_iff {P : M → Prop} (Q) (h : ∀ x, P x ↔ Q x) (H : DefinablePred L Γ Q) : DefinablePred L Γ P := by
  rwa [show P = Q from by funext v; simp [h]]

instance DefinableFunction₁.graph {f : M → M} [h : DefinableFunction₁ L Γ f] :
  DefinableRel L Γ (Function.Graph f) := h

instance DefinableFunction₂.graph {f : M → M → M} [h : DefinableFunction₂ L Γ f] :
  DefinableRel₃ L Γ (Function.Graph₂ f) := h

instance DefinableFunction₃.graph {f : M → M → M → M} [h : DefinableFunction₃ L Γ f] :
  DefinableRel₄ L Γ (Function.Graph₃ f) := h

namespace DefinableFunction

lemma graph_delta {k} {f : (Fin k → M) → M}
    (h : DefinableFunction L (𝚺, m) f) : DefinableFunction L (𝚫, m) f := by
  rcases h with ⟨p, h⟩
  exact ⟨p.graphDelta, by
    cases' m with m <;> simp [HSemiformula.graphDelta]
    intro e; simp [Empty.eq_elim, h.df.iff]
    exact eq_comm, by
    intro v; simp [h.df.iff]⟩

instance {k} {f : (Fin k → M) → M} [h : DefinableFunction L (𝚺, m) f] : DefinableFunction L (𝚫, m) f :=
  DefinableFunction.graph_delta h

instance {k} {f : (Fin k → M) → M} [DefinableFunction L 𝚺₀ f] (Γ) : DefinableFunction L Γ f := inferInstance

lemma of_sigmaOne {k} {f : (Fin k → M) → M}
    (h : DefinableFunction L 𝚺₁ f) (Γ m) : DefinableFunction L (Γ, m + 1) f := Definable.of_deltaOne (graph_delta h) Γ m

@[simp] lemma var {k} (i : Fin k) : DefinableFunction L Γ (fun v : Fin k → M ↦ v i) :=
  .of_zero (Γ' := 𝚺) ⟨.mkSigma “#0 = !!#i.succ” (by simp), by intro _; simp⟩ _

@[simp] lemma const {k} (c : M) : DefinableFunction L Γ (fun _ : Fin k → M ↦ c) :=
  .of_zero (Γ' := 𝚺) ⟨.mkSigma “#0 = &c” (by simp), by intro v; simp⟩ _

@[simp] lemma term_retraction (t : Semiterm L M n) (e : Fin n → Fin k) :
    DefinableFunction L Γ fun v : Fin k → M ↦ Semiterm.valm M (fun x ↦ v (e x)) id t :=
  .of_zero (Γ' := 𝚺)
    ⟨.mkSigma “#0 = !!(Rew.substs (fun x ↦ #(e x).succ) t)” (by simp), by intro v; simp [Semiterm.val_substs]⟩ _

@[simp] lemma term (t : Semiterm L M k) :
    DefinableFunction L Γ fun v : Fin k → M ↦ Semiterm.valm M v id t :=
  .of_zero (Γ' := 𝚺)
    ⟨.mkSigma “#0 = !!(Rew.bShift t)” (by simp), by intro v; simp [Semiterm.val_bShift']⟩ _

lemma of_eq {f : (Fin k → M) → M} (g) (h : ∀ v, f v = g v) (H : DefinableFunction L Γ f) : DefinableFunction L Γ g := by
  rwa [show g = f from by funext v; simp [h]]

lemma retraction {f : (Fin k → M) → M} (hf : DefinableFunction L Γ f) (e : Fin k → Fin n) :
    DefinableFunction L Γ fun v ↦ f (fun i ↦ v (e i)) := by
  have := Definable.retraction (n := n + 1) hf (0 :> fun i ↦ (e i).succ); simp at this
  exact this.of_iff _ (by intro x; simp)

lemma rel {f : (Fin k → M) → M} (h : DefinableFunction L Γ f) :
  Definable L Γ (fun v ↦ v 0 = f (v ·.succ)) := h

end DefinableFunction

lemma DefinableFunction₁.comp {Γ} {k} {f : M → M} {g : (Fin k → M) → M}
    (hf : DefinableFunction₁ L (Γ, m + 1) f) (hg : DefinableFunction L (𝚺, m + 1) g) :
    DefinableFunction L (Γ, m + 1) (fun v ↦ f (g v)) := by
  simpa using Definable.comp₂ (P := Function.Graph f) (DefinableFunction.var 0) (hg.retraction Fin.succ) hf

lemma DefinableFunction₂.comp {Γ} {k} {f : M → M → M} {g₁ g₂ : (Fin k → M) → M}
    (hf : DefinableFunction₂ L (Γ, m + 1) f) (hg₁ : DefinableFunction L (𝚺, m + 1) g₁) (hg₂ : DefinableFunction L (𝚺, m + 1) g₂) :
    DefinableFunction L (Γ, m + 1) (fun v ↦ f (g₁ v) (g₂ v)) := by
  simpa using Definable.comp₃ (P := Function.Graph₂ f) (DefinableFunction.var 0) (hg₁.retraction Fin.succ) (hg₂.retraction Fin.succ) hf

lemma DefinableFunction₃.comp {Γ} {k} {f : M → M → M → M} {g₁ g₂ g₃ : (Fin k → M) → M}
    (hf : DefinableFunction₃ L (Γ, m + 1) f) (hg₁ : DefinableFunction L (𝚺, m + 1) g₁)
    (hg₂ : DefinableFunction L (𝚺, m + 1) g₂) (hg₃ : DefinableFunction L (𝚺, m + 1) g₃) :
    DefinableFunction L (Γ, m + 1) (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) := by
  simpa using Definable.comp₄ (P := Function.Graph₃ f) (DefinableFunction.var 0)
    (hg₁.retraction Fin.succ) (hg₂.retraction Fin.succ) (hg₃.retraction Fin.succ) hf

lemma DefinableFunction.comp₁ {Γ} {k} {f : M → M} [DefinableFunction₁ L (Γ, m + 1) f]
    {g : (Fin k → M) → M} (hg : DefinableFunction L (𝚺, m + 1) g) :
    DefinableFunction L (Γ, m + 1) (fun v ↦ f (g v)) :=
  DefinableFunction₁.comp inferInstance hg

lemma DefinableFunction.comp₂ {Γ} {k} {f : M → M → M} [DefinableFunction₂ L (Γ, m + 1) f]
    {g₁ g₂ : (Fin k → M) → M} (hg₁ : DefinableFunction L (𝚺, m + 1) g₁) (hg₂ : DefinableFunction L (𝚺, m + 1) g₂) :
    DefinableFunction L (Γ, m + 1) (fun v ↦ f (g₁ v) (g₂ v)) :=
  DefinableFunction₂.comp inferInstance hg₁ hg₂

lemma DefinableFunction.comp₃ {Γ} {k} {f : M → M → M → M} [DefinableFunction₃ L (Γ, m + 1) f]
    {g₁ g₂ g₃ : (Fin k → M) → M}
    (hg₁ : DefinableFunction L (𝚺, m + 1) g₁) (hg₂ : DefinableFunction L (𝚺, m + 1) g₂) (hg₃ : DefinableFunction L (𝚺, m + 1) g₃) :
    DefinableFunction L (Γ, m + 1) (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) :=
  DefinableFunction₃.comp inferInstance hg₁ hg₂ hg₃

namespace DefinableRel

@[simp] instance eq : DefinableRel L Γ (Eq : M → M → Prop) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1” (by simp)) (by intro _; simp)

@[simp] instance lt : DefinableRel L Γ (LT.lt : M → M → Prop) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 < #1” (by simp)) (by intro _; simp)

@[simp] instance le : DefinableRel L Γ (LE.le : M → M → Prop) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 ≤ #1” (by simp)) (by intro _; simp)

end DefinableRel

namespace DefinableFunction₂

@[simp] instance add : DefinableFunction₂ L Γ ((· + ·) : M → M → M) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1 + #2” (by simp)) (by intro _; simp)

@[simp] instance mul : DefinableFunction₂ L Γ ((· * ·) : M → M → M) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1 * #2” (by simp)) (by intro _; simp)

@[simp] instance hAdd : DefinableFunction₂ L Γ (HAdd.hAdd : M → M → M) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1 + #2” (by simp)) (by intro _; simp)

@[simp] instance hMul : DefinableFunction₂ L Γ (HMul.hMul : M → M → M) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1 * #2” (by simp)) (by intro _; simp)

end DefinableFunction₂

namespace Definable

lemma ball_lt {Γ} {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : DefinableFunction L (𝚺, m + 1) f) (h : Definable L (Γ, m + 1) (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L (Γ, m + 1) (fun v ↦ ∀ x < f v, P v x) := by
  rcases hf with ⟨bf, hbf⟩
  rcases h with ⟨p, hp⟩
  match Γ with
  | 𝚺 => exact
    ⟨ .mkSigma (∃' (bf.val ⋏ (∀[“#0 < #1”] Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.val))) (by simp),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | 𝚷 => exact
    ⟨ .mkPi (∀' (bf.val ⟶ (∀[“#0 < #1”] Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.val))) (by simp),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | 𝚫 =>
    exact .of_sigma_of_pi
      ⟨ .mkSigma (∃' (bf.val ⋏ (∀[“#0 < #1”] Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.sigma.val))) (by simp),
          by intro v; simp [hbf.df.iff, hp.df.iff, HSemiformula.val_sigma] ⟩
      ⟨ .mkPi (∀' (bf.val ⟶ (∀[“#0 < #1”] Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.pi.val))) (by simp),
        by intro v; simp [hbf.df.iff, hp.df.iff, hp.proper.iff'] ⟩

lemma bex_lt {Γ} {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : DefinableFunction L (𝚺, m + 1) f) (h : Definable L (Γ, m + 1) (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L (Γ, m + 1) (fun v ↦ ∃ x < f v, P v x) := by
  rcases hf with ⟨bf, hbf⟩
  rcases h with ⟨p, hp⟩
  match Γ with
  | 𝚺 => exact
    ⟨ .mkSigma (∃' (bf.val ⋏ (∃[“#0 < #1”] Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.val))) (by simp),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | 𝚷 => exact
    ⟨ .mkPi (∀' (bf.val ⟶ (∃[“#0 < #1”] Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.val))) (by simp),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | 𝚫 =>
    exact .of_sigma_of_pi
      ⟨ .mkSigma (∃' (bf.val ⋏ (∃[“#0 < #1”] Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.sigma.val))) (by simp),
          by intro v; simp [hbf.df.iff, hp.df.iff, HSemiformula.val_sigma] ⟩
      ⟨ .mkPi (∀' (bf.val ⟶ (∃[“#0 < #1”] Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.pi.val))) (by simp),
        by intro v; simp [hbf.df.iff, hp.df.iff, hp.proper.iff'] ⟩

lemma ball_le {Γ} {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : DefinableFunction L (𝚺, m + 1) f) (h : Definable L (Γ, m + 1) (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L (Γ, m + 1) (fun v ↦ ∀ x ≤ f v, P v x) := by
  have : Definable L (Γ, m + 1) (fun v ↦ ∀ x < f v + 1, P v x) := ball_lt (DefinableFunction₂.comp (by simp) hf (by simp)) h
  exact this.of_iff <| by intro v; simp [lt_succ_iff_le]

lemma bex_le {Γ} {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : DefinableFunction L (𝚺, m + 1) f) (h : Definable L (Γ, m + 1) (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L (Γ, m + 1) (fun v ↦ ∃ x ≤ f v, P v x) := by
  have : Definable L (Γ, m + 1) (fun v ↦ ∃ x < f v + 1, P v x) := bex_lt (DefinableFunction₂.comp (by simp) hf (by simp)) h
  exact this.of_iff <| by intro v; simp [lt_succ_iff_le]

lemma ball_lt' {Γ} {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : DefinableFunction L (𝚺, m + 1) f) (h : Definable L (Γ, m + 1) (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L (Γ, m + 1) (fun v ↦ ∀ {x}, x < f v → P v x) := ball_lt hf h

lemma ball_le' {Γ} {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : DefinableFunction L (𝚺, m + 1) f) (h : Definable L (Γ, m + 1) (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L (Γ, m + 1) (fun v ↦ ∀ {x}, x ≤ f v → P v x) := ball_le hf h

end Definable

end

end Model

end Arith

end LO.FirstOrder
