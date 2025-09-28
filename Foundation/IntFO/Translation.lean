import Foundation.IntFO.Basic

namespace LO.FirstOrder

namespace Sequent

instance : Tilde (List (Semiformula L ξ n)) := ⟨fun Γ ↦ Γ.map (∼·)⟩

@[simp] lemma neg_def (Γ : List (Semiformula L ξ n)) : ∼Γ = Γ.map (∼·) := rfl

@[simp] lemma neg_nil : ∼([] : List (Semiformula L ξ n)) = [] := rfl

@[simp] lemma neg_cons (Γ : List (Semiformula L ξ n)) (φ) : ∼(φ :: Γ) = ∼φ :: ∼Γ := rfl

@[simp] lemma neg_neg_eq (Γ : List (Semiformula L ξ n)) : ∼∼Γ = Γ := by simp [Function.comp_def]

end Sequent

namespace Semiformula

def doubleNegation {n} : Semiformula L ξ n → Semiformulaᵢ L ξ n
  | rel r v  => ∼∼(.rel r v)
  | nrel r v => ∼(.rel r v)
  | ⊤        => ∼⊥
  | ⊥        => ⊥
  | φ ⋏ ψ    => φ.doubleNegation ⋏ ψ.doubleNegation
  | φ ⋎ ψ    => ∼(∼φ.doubleNegation ⋏ ∼ψ.doubleNegation)
  | ∀' φ     => ∀' φ.doubleNegation
  | ∃' φ     => ∼(∀' ∼φ.doubleNegation)

scoped[LO.FirstOrder] postfix:max "ᴺ" => Semiformula.doubleNegation

@[simp] lemma doubleNegation_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v)ᴺ = ∼∼(.rel r v) := rfl

@[simp] lemma doubleNegation_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v)ᴺ = ∼(.rel r v) := rfl

@[simp] lemma doubleNegation_verum : (⊤ : Semiformula L ξ n)ᴺ = ∼⊥ := rfl

@[simp] lemma doubleNegation_falsum : (⊥ : Semiformula L ξ n)ᴺ = ⊥ := rfl

@[simp] lemma doubleNegation_and (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ)ᴺ = φᴺ ⋏ ψᴺ := rfl

@[simp] lemma doubleNegation_or (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ)ᴺ = ∼(∼φᴺ ⋏ ∼ψᴺ) := rfl

@[simp] lemma doubleNegation_all (φ : Semiformula L ξ (n + 1)) : (∀' φ)ᴺ = ∀' φᴺ := rfl

@[simp] lemma doubleNegation_ex (φ : Semiformula L ξ (n + 1)) : (∃' φ)ᴺ = ∼(∀' ∼φᴺ) := rfl

@[simp] lemma doubleNegation_isNegative (φ : Semiformula L ξ n) : φᴺ.IsNegative := by
  induction φ using rec' <;> simp [*]

lemma rew_doubleNegation (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) : ω ▹ φᴺ = (ω ▹ φ)ᴺ := by
  induction φ using rec' generalizing n₂ <;> simp [rew_rel, rew_nrel, Semiformulaᵢ.rew_rel, *]

lemma subst_doubleNegation (φ : Semiformula L ξ n₁) (v : Fin n₁ → Semiterm L ξ n₂) : φᴺ ⇜ v = (φ ⇜ v)ᴺ := rew_doubleNegation _ _

end Semiformula

abbrev Theory.doubleNegation (T : Theory L) : Theoryᵢ L := Semiformula.doubleNegation '' T

scoped[LO.FirstOrder] postfix:max "ᴺ" => Theory.doubleNegation

abbrev Sequent.doubleNegation (Γ : List (Semiformula L ξ n)) : List (Semiformulaᵢ L ξ n) := Γ.map (·ᴺ)

scoped[LO.FirstOrder] postfix:max "ᴺ" => Sequent.doubleNegation

namespace Derivation

variable {L : Language} [L.DecidableEq] {T : Theory L}

open Rewriting LO.Entailment Entailment.FiniteContext HilbertProofᵢ

noncomputable
def negDoubleNegation : (φ : SyntacticFormula L) → 𝗠𝗶𝗻¹ ⊢! ∼φᴺ ⭤ (∼φ)ᴺ
  | .rel r v  => Entailment.tneIff (φ := Semiformulaᵢ.rel r v)
  | .nrel r v => Entailment.E_Id (φ := ∼∼(Semiformulaᵢ.rel r v))
  | ⊤         => Entailment.ENNOO
  | ⊥         => Entailment.E_Id (φ := ∼⊥)
  | φ ⋏ ψ     =>
    have ihφ : 𝗠𝗶𝗻¹ ⊢! ∼φᴺ ⭤ (∼φ)ᴺ := negDoubleNegation φ
    have ihψ : 𝗠𝗶𝗻¹ ⊢! ∼ψᴺ ⭤ (∼ψ)ᴺ := negDoubleNegation ψ
    have : 𝗠𝗶𝗻¹ ⊢! φᴺ ⋏ ψᴺ ⭤ ∼(∼φ)ᴺ ⋏ ∼(∼ψ)ᴺ :=
      Entailment.EKK_of_E_of_E (iffnegOfNegIff (by simp) ihφ) (iffnegOfNegIff (by simp) ihψ)
    Entailment.ENN_of_E this
  | φ ⋎ ψ     =>
    have ihφ : 𝗠𝗶𝗻¹ ⊢! ∼φᴺ ⭤ (∼φ)ᴺ := negDoubleNegation φ
    have ihψ : 𝗠𝗶𝗻¹ ⊢! ∼ψᴺ ⭤ (∼ψ)ᴺ := negDoubleNegation ψ
    have : 𝗠𝗶𝗻¹ ⊢! ∼φᴺ ⋏ ∼ψᴺ ⭤ (∼φ)ᴺ ⋏ (∼ψ)ᴺ := Entailment.EKK_of_E_of_E ihφ ihψ
    have : 𝗠𝗶𝗻¹ ⊢! ∼∼(∼φᴺ ⋏ ∼ψᴺ) ⭤ (∼φ)ᴺ ⋏ (∼ψ)ᴺ := Entailment.E_trans (DN_of_isNegative (by simp)) this
    this
  | ∀' φ      =>
    have ihφ : 𝗠𝗶𝗻¹ ⊢! ∼(free φ)ᴺ ⭤ (∼(free φ))ᴺ := negDoubleNegation (free φ)
    have : 𝗠𝗶𝗻¹ ⊢! (free φ)ᴺ ⭤ (∼(∼(free φ))ᴺ) := iffnegOfNegIff (by simp) ihφ
    have : 𝗠𝗶𝗻¹ ⊢! ∀' φᴺ ⭤ ∀' ∼(∼φ)ᴺ :=
      allIffAllOfIff <| Entailment.cast (by simp [Semiformula.rew_doubleNegation]) this
    Entailment.ENN_of_E this
  | ∃' φ      =>
    have ihφ : 𝗠𝗶𝗻¹ ⊢! ∼(free φ)ᴺ ⭤ (∼(free φ))ᴺ := negDoubleNegation (free φ)
    have : 𝗠𝗶𝗻¹ ⊢! ∀' ∼φᴺ ⭤ ∀' (∼φ)ᴺ :=
      allIffAllOfIff <| Entailment.cast (by simp [Semiformula.rew_doubleNegation]) ihφ
    have : 𝗠𝗶𝗻¹ ⊢! ∼∼(∀' ∼φᴺ) ⭤ ∀' (∼φ)ᴺ := Entailment.E_trans (DN_of_isNegative (by simp)) this
    this
  termination_by φ => φ.complexity

open Entailment

noncomputable
def goedelGentzen {Γ : Sequent L} : ⊢ᵀ Γ → (∼Γ)ᴺ ⊢[𝗠𝗶𝗻¹]! ⊥
  | axL Γ r v            => nthAxm 1 ⨀ nthAxm 0
  | verum Γ              => nthAxm 0
  | @and _ _ Γ φ ψ dφ dψ =>
    have ihφ : ((∼φ)ᴺ :: (∼Γ)ᴺ) ⊢[𝗠𝗶𝗻¹]! ⊥ := goedelGentzen dφ
    have ihψ : ((∼ψ)ᴺ :: (∼Γ)ᴺ) ⊢[𝗠𝗶𝗻¹]! ⊥ := goedelGentzen dψ
    have : (∼Γ)ᴺ ⊢[𝗠𝗶𝗻¹]! ∼(∼φ)ᴺ ⋏ ∼(∼ψ)ᴺ := Entailment.K_intro (deduct ihφ) (deduct ihψ)
    deductInv (Entailment.dni' this)
  | @or _ _ Γ φ ψ d      =>
    have : (∼Γ)ᴺ ⊢[𝗠𝗶𝗻¹]! (∼ψ)ᴺ ➝ (∼φ)ᴺ ➝ ⊥ := deduct <| deduct  <| goedelGentzen d
    have : ((∼φ)ᴺ ⋏ (∼ψ)ᴺ :: (∼Γ)ᴺ) ⊢[𝗠𝗶𝗻¹]! ⊥ :=
      Entailment.FiniteContext.weakening (by simp) this ⨀ (Entailment.K_right (nthAxm 0)) ⨀ (Entailment.K_left (nthAxm 0))
    this
  | @all _ _ Γ φ d       =>
    have eΓ : (∼Γ⁺)ᴺ = ((∼Γ)ᴺ)⁺ := by
      simp [Sequent.doubleNegation, Rewriting.shifts, Sequent.neg_def, Semiformula.rew_doubleNegation]
    have : ((∼Γ)ᴺ)⁺ ⊢[𝗠𝗶𝗻¹]! free (∼(∼φ)ᴺ) :=
      FiniteContext.cast (deduct (goedelGentzen d)) eΓ (by simp [Semiformula.rew_doubleNegation]; rfl)
    deductInv <| dni' <| geNOverFiniteContext this
  | @ex _ _ Γ φ t d      =>
    have ih : (∼Γ)ᴺ ⊢[𝗠𝗶𝗻¹]! ∼((∼φ)ᴺ/[t]) :=
      Entailment.cast (by simp [Semiformula.rew_doubleNegation]; rfl) <| deduct (goedelGentzen d)
    have : ((∀' (∼φ)ᴺ) :: (∼Γ)ᴺ) ⊢[𝗠𝗶𝗻¹]! (∼φ)ᴺ/[t] := specializeOverContext (nthAxm 0) t
    (FiniteContext.weakening (by simp) ih) ⨀ this
  | @cut _ _ Γ φ dp dn   =>
    have ihp : ((∼φ)ᴺ :: (∼Γ)ᴺ) ⊢[𝗠𝗶𝗻¹]! ⊥ := goedelGentzen dp
    have ihn : (φᴺ :: (∼Γ)ᴺ) ⊢[𝗠𝗶𝗻¹]! ⊥ := cast (by simp) (goedelGentzen dn)
    have b₁ : (∼Γ)ᴺ ⊢[𝗠𝗶𝗻¹]! ∼∼φᴺ := Entailment.C_trans (of <| Entailment.K_left (negDoubleNegation φ)) (deduct ihp)
    have b₂ : (∼Γ)ᴺ ⊢[𝗠𝗶𝗻¹]! ∼φᴺ := deduct ihn
    b₁ ⨀ b₂
  | @wk _ _ Γ Δ d h      => FiniteContext.weakening (by simpa using List.map_subset _ h) (goedelGentzen d)

end Derivation

end LO.FirstOrder
