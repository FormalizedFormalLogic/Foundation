module

public import Foundation.FirstOrder.Intuitionistic.Deduction
public import Foundation.Meta.IntProver

@[expose] public section
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
  |  rel r v => ∼∼(.rel r v)
  | nrel r v => ∼(.rel r v)
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |    φ ⋏ ψ => φ.doubleNegation ⋏ ψ.doubleNegation
  |    φ ⋎ ψ => ∼(∼φ.doubleNegation ⋏ ∼ψ.doubleNegation)
  |     ∀⁰ φ => ∀⁰ φ.doubleNegation
  |     ∃⁰ φ => ∼(∀⁰ ∼φ.doubleNegation)

scoped[LO.FirstOrder] postfix:max "ᴺ" => Semiformula.doubleNegation

@[simp] lemma doubleNegation_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v)ᴺ = ∼∼(.rel r v) := rfl

@[simp] lemma doubleNegation_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v)ᴺ = ∼(.rel r v) := rfl

@[simp] lemma doubleNegation_verum : (⊤ : Semiformula L ξ n)ᴺ = ∼⊥ := rfl

@[simp] lemma doubleNegation_falsum : (⊥ : Semiformula L ξ n)ᴺ = ⊥ := rfl

@[simp] lemma doubleNegation_and (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ)ᴺ = φᴺ ⋏ ψᴺ := rfl

@[simp] lemma doubleNegation_or (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ)ᴺ = ∼(∼φᴺ ⋏ ∼ψᴺ) := rfl

@[simp] lemma doubleNegation_all (φ : Semiformula L ξ (n + 1)) : (∀⁰ φ)ᴺ = ∀⁰ φᴺ := rfl

@[simp] lemma doubleNegation_ex (φ : Semiformula L ξ (n + 1)) : (∃⁰ φ)ᴺ = ∼(∀⁰ ∼φᴺ) := rfl

lemma doubleNegation_imply (φ ψ : Semiformula L ξ n) : (φ 🡒 ψ)ᴺ = ∼(∼(∼φ)ᴺ ⋏ ∼ψᴺ) := by simp [imp_eq]

@[simp] lemma doubleNegation_isNegative (φ : Semiformula L ξ n) : φᴺ.IsNegative := by
  induction φ using rec' <;> simp [*]

@[simp] lemma doubleNegation_conj₂ (Γ : List (Semiformula L ξ n)) :
    (Γ.conj₂)ᴺ = (Γ.map Semiformula.doubleNegation).conj₂ :=
  match Γ with
  |          [] => by simp; rfl
  |         [φ] => by simp
  | φ :: ψ :: Γ => by simp [doubleNegation_conj₂ (ψ :: Γ)]

lemma doubleNegation_fconj (s : Finset (Semiformula L ξ n)) :
    (s.conj)ᴺ = (s.toList.map Semiformula.doubleNegation).conj₂ := doubleNegation_conj₂ _

lemma rew_doubleNegation (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) : ω ▹ φᴺ = (ω ▹ φ)ᴺ := by
  induction φ using rec' generalizing n₂ <;> simp [rew_rel, rew_nrel, Semiformulaᵢ.rew_rel, *]

lemma subst_doubleNegation (φ : Semiformula L ξ n₁) (v : Fin n₁ → Semiterm L ξ n₂) :
    φᴺ ⇜ v = (φ ⇜ v)ᴺ := rew_doubleNegation _ _

lemma emb_doubleNegation (φ : Semisentence L n₁) :
    Rewriting.emb (φᴺ) = (Rewriting.emb φ : Semiformula L ξ n₁)ᴺ := rew_doubleNegation _ _

end Semiformula

abbrev Sequent.doubleNegation (Γ : List (Semiformula L ξ n)) : List (Semiformulaᵢ L ξ n) := Γ.map (·ᴺ)

scoped[LO.FirstOrder] postfix:max "ᴺ" => Sequent.doubleNegation

def Theory.ToTheoryᵢ (T : Theory L) (Λ : Hilbertᵢ L) : Theoryᵢ L Λ where
  theory := Semiformula.doubleNegation '' T

@[simp] lemma Theory.ToTheoryᵢ_theory_def (T : Theory L) (Λ : Hilbertᵢ L) :
    (T.ToTheoryᵢ Λ).theory = Semiformula.doubleNegation '' T := rfl

namespace Derivation

variable {L : Language} [L.DecidableEq] {T : Theory L} {Λ : Hilbertᵢ L}

open Rewriting LO.Entailment Entailment.FiniteContext HilbertProofᵢ

def negDoubleNegation : (φ : SyntacticFormula L) → Λ ⊢! ∼φᴺ 🡘 (∼φ)ᴺ
  | .rel r v => Entailment.tneIff (φ := Semiformulaᵢ.rel r v)
  | .nrel r v => Entailment.E_Id (φ := ∼∼(Semiformulaᵢ.rel r v))
  | ⊤ => Entailment.ENNOO
  | ⊥ => Entailment.E_Id (φ := ∼⊥)
  | φ ⋏ ψ =>
    have ihφ : Λ ⊢! ∼φᴺ 🡘 (∼φ)ᴺ := negDoubleNegation φ
    have ihψ : Λ ⊢! ∼ψᴺ 🡘 (∼ψ)ᴺ := negDoubleNegation ψ
    have : Λ ⊢! φᴺ ⋏ ψᴺ 🡘 ∼(∼φ)ᴺ ⋏ ∼(∼ψ)ᴺ :=
      Entailment.EKK_of_E_of_E (iffnegOfNegIff (by simp) ihφ) (iffnegOfNegIff (by simp) ihψ)
    Entailment.ENN_of_E this
  | φ ⋎ ψ =>
    have ihφ : Λ ⊢! ∼φᴺ 🡘 (∼φ)ᴺ := negDoubleNegation φ
    have ihψ : Λ ⊢! ∼ψᴺ 🡘 (∼ψ)ᴺ := negDoubleNegation ψ
    have : Λ ⊢! ∼φᴺ ⋏ ∼ψᴺ 🡘 (∼φ)ᴺ ⋏ (∼ψ)ᴺ := Entailment.EKK_of_E_of_E ihφ ihψ
    have : Λ ⊢! ∼∼(∼φᴺ ⋏ ∼ψᴺ) 🡘 (∼φ)ᴺ ⋏ (∼ψ)ᴺ := Entailment.E_trans (DN_of_isNegative (by simp)) this
    this
  | ∀⁰ φ =>
    have ihφ : Λ ⊢! ∼(free φ)ᴺ 🡘 (∼(free φ))ᴺ := negDoubleNegation (free φ)
    have : Λ ⊢! (free φ)ᴺ 🡘 (∼(∼(free φ))ᴺ) := iffnegOfNegIff (by simp) ihφ
    have : Λ ⊢! ∀⁰ φᴺ 🡘 ∀⁰ ∼(∼φ)ᴺ :=
      allIffAllOfIff <| Entailment.cast (by simp [Semiformula.rew_doubleNegation]) this
    Entailment.ENN_of_E this
  | ∃⁰ φ =>
    have ihφ : Λ ⊢! ∼(free φ)ᴺ 🡘 (∼(free φ))ᴺ := negDoubleNegation (free φ)
    have : Λ ⊢! ∀⁰ ∼φᴺ 🡘 ∀⁰ (∼φ)ᴺ :=
      allIffAllOfIff <| Entailment.cast (by simp [Semiformula.rew_doubleNegation]) ihφ
    have : Λ ⊢! ∼∼(∀⁰ ∼φᴺ) 🡘 ∀⁰ (∼φ)ᴺ := Entailment.E_trans (DN_of_isNegative (by simp)) this
    this
  termination_by φ => φ.complexity

lemma neg_doubleNegation (φ : SyntacticFormula L) : Λ ⊢ ∼φᴺ 🡘 (∼φ)ᴺ := ⟨negDoubleNegation φ⟩

lemma neg_doubleNegation' (φ : SyntacticFormula L) : Λ ⊢ ∼(∼φ)ᴺ 🡘 φᴺ := by simpa using neg_doubleNegation (∼φ)

open FiniteContext

lemma imply_doubleNegation (φ ψ : SyntacticFormula L) : Λ ⊢ (φᴺ 🡒 ψᴺ) 🡘 (φ 🡒 ψ)ᴺ := by
  suffices Λ ⊢ (φᴺ 🡒 ψᴺ) 🡘 ∼(∼(∼φ)ᴺ ⋏ ∼ψᴺ) by simpa [Semiformula.doubleNegation_imply]
  have hφ₀ : Λ ⊢ ∼(∼φ)ᴺ 🡘 φᴺ := by simpa using neg_doubleNegation (∼φ)
  have hψ : Λ ⊢ ∼∼ψᴺ 🡘 ψᴺ := ⟨DN_of_isNegative (by simp)⟩
  apply Entailment.E!_intro
  · apply FiniteContext.deduct'!
    apply FiniteContext.deduct!
    let Γ := [∼(∼φ)ᴺ ⋏ ∼ψᴺ, φᴺ 🡒 ψᴺ]
    have : Γ ⊢[Λ] φᴺ := of'! (K!_left hφ₀) ⨀ (K!_left by_axm₀!)
    have : Γ ⊢[Λ] ψᴺ := by_axm₁! ⨀ this
    exact K!_right by_axm₀! ⨀ this
  · apply FiniteContext.deduct'!
    apply FiniteContext.deduct!
    refine of'! (K!_left hψ) ⨀ ?_
    apply FiniteContext.deduct!
    let Γ := [∼ψᴺ, φᴺ, ∼(∼(∼φ)ᴺ ⋏ ∼ψᴺ)]
    have : Γ ⊢[Λ] ∼(∼φ)ᴺ := of'! (Γ := Γ) (K!_right hφ₀) ⨀ by_axm₁!
    exact by_axm₂! ⨀ (K!_intro this by_axm₀!)

open Entailment

def gödelGentzen {Γ : Sequent L} : ⊢ᵀ Γ → (∼Γ)ᴺ ⊢[Λ]! ⊥
  | axL r v => nthAxm 1 ⨀ nthAxm 0
  | verum => nthAxm 0
  | and (Γ := Γ) (φ := φ) (ψ := ψ) dφ dψ =>
    have ihφ : ((∼φ)ᴺ :: (∼Γ)ᴺ) ⊢[Λ]! ⊥ := gödelGentzen dφ
    have ihψ : ((∼ψ)ᴺ :: (∼Γ)ᴺ) ⊢[Λ]! ⊥ := gödelGentzen dψ
    have : (∼Γ)ᴺ ⊢[Λ]! ∼(∼φ)ᴺ ⋏ ∼(∼ψ)ᴺ := Entailment.K_intro (deduct ihφ) (deduct ihψ)
    deductInv (Entailment.dni' this)
  | or (Γ := Γ) (φ := φ) (ψ := ψ) d =>
    have : (∼Γ)ᴺ ⊢[Λ]! (∼ψ)ᴺ 🡒 (∼φ)ᴺ 🡒 ⊥ := deduct <| deduct  <| gödelGentzen d
    have : ((∼φ)ᴺ ⋏ (∼ψ)ᴺ :: (∼Γ)ᴺ) ⊢[Λ]! ⊥ :=
      Entailment.FiniteContext.weakening (by simp) this ⨀ (Entailment.K_right (nthAxm 0)) ⨀ (Entailment.K_left (nthAxm 0))
    this
  | all (Γ := Γ) (φ := φ) d =>
    have eΓ : (∼Γ⁺)ᴺ = ((∼Γ)ᴺ)⁺ := by
      simp [Sequent.doubleNegation, Rewriting.shifts, Sequent.neg_def, Semiformula.rew_doubleNegation]
    have : ((∼Γ)ᴺ)⁺ ⊢[Λ]! free (∼(∼φ)ᴺ) :=
      FiniteContext.cast (deduct (gödelGentzen d)) eΓ (by simp [Semiformula.rew_doubleNegation]; rfl)
    deductInv <| dni' <| geNOverFiniteContext this
  | exs (Γ := Γ) (φ := φ) t d =>
    have ih : (∼Γ)ᴺ ⊢[Λ]! ∼((∼φ)ᴺ/[t]) :=
      Entailment.cast (by simp [Semiformula.rew_doubleNegation]; rfl) <| deduct (gödelGentzen d)
    have : ((∀⁰ (∼φ)ᴺ) :: (∼Γ)ᴺ) ⊢[Λ]! (∼φ)ᴺ/[t] := specializeOverContext (nthAxm 0) t
    (FiniteContext.weakening (by simp) ih) ⨀ this
  | cut (Γ := Γ) (φ := φ) dp dn =>
    have ihp : ((∼φ)ᴺ :: (∼Γ)ᴺ) ⊢[Λ]! ⊥ := gödelGentzen dp
    have ihn : (φᴺ :: (∼Γ)ᴺ) ⊢[Λ]! ⊥ := cast (by simp) (gödelGentzen dn)
    have b₁ : (∼Γ)ᴺ ⊢[Λ]! ∼∼φᴺ := Entailment.C_trans (of <| Entailment.K_left (negDoubleNegation φ)) (deduct ihp)
    have b₂ : (∼Γ)ᴺ ⊢[Λ]! ∼φᴺ := deduct ihn
    b₁ ⨀ b₂
  | wk (Γ := Γ) (Δ := Δ) d h => FiniteContext.weakening (by simpa using List.map_subset _ h) (gödelGentzen d)

end Derivation

open Classical LO.Entailment

/-- Gödel-Gentzen translation of classical first-order logic to intiotionistic first-order logic. -/
theorem gödel_gentzen {T : Theory L} {φ} : T ⊢ φ → T.ToTheoryᵢ Λ ⊢ φᴺ := by
  intro h
  let ⟨⟨s, hs⟩, b⟩ := Theory.compact' h
  have h : (∅ : Schema L) ⊢ ↑s.conj 🡒 ↑φ := by simpa using provable_def.mp b
  let ψ : SyntacticFormula L := ↑s.conj 🡒 ↑φ
  have h₁ : Λ ⊢ ∼(∼ψ)ᴺ := by
    simpa using Entailment.FiniteContext.provable_iff.mp ⟨Derivation.gödelGentzen h.get⟩
  have h₂ : Λ ⊢ ∼(∼ψ)ᴺ 🡘 ψᴺ := by simpa using Derivation.neg_doubleNegation (∼ψ)
  have : Λ ⊢ ψᴺ := K!_left h₂ ⨀ h₁
  have H : Λ ⊢ (↑s.conj : SyntacticFormula L)ᴺ 🡒 ↑φᴺ :=
    by simpa [Semiformula.emb_doubleNegation] using (K!_right (Derivation.imply_doubleNegation _ _)) ⨀ this
  let U : Set (SyntacticFormulaᵢ L) := (Rewriting.emb '' (T.ToTheoryᵢ Λ).theory)
  suffices
      U *⊢[Λ] ⋀ s.toList.map fun φ : Sentence L ↦ (↑φ : SyntacticFormula L)ᴺ by
    apply Theoryᵢ.provable_def.mpr
    apply Context.of! H ⨀ ?_
    simpa [Finset.conj, List.map_conj₂, Function.comp_def]
  apply LO.Entailment.Conj₂!_intro
  have : ∀ ψ ∈ s, U *⊢[Λ] ↑ψᴺ := by
    intro ψ hψ
    exact Context.by_axm (by simpa [U] using ⟨ψ, hs hψ, rfl⟩)
  simpa [←Semiformula.emb_doubleNegation] using this

end LO.FirstOrder
