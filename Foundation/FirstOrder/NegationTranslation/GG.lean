module

public import Foundation.FirstOrder.Intuitionistic.LJ

@[expose] public section
namespace LO.FirstOrder

namespace Semiformula

def doubleNegation {n} : Semiformula L ξ n → Semiformulaᵢ L ξ n
  |  rel r v => ∼∼(.rel r v)
  | nrel r v => ∼(.rel r v)
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |    φ ⋏ ψ => φ.doubleNegation ⋏ ψ.doubleNegation
  |    φ ⋎ ψ => ∼(∼φ.doubleNegation ⋏ ∼ψ.doubleNegation)
  |     ∀¹ φ => ∀¹ φ.doubleNegation
  |     ∃¹ φ => ∼(∀¹ ∼φ.doubleNegation)

scoped[LO.FirstOrder] postfix:max "ᴺ" => Semiformula.doubleNegation

@[simp] lemma doubleNegation_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v)ᴺ = ∼∼(.rel r v) := rfl

@[simp] lemma doubleNegation_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v)ᴺ = ∼(.rel r v) := rfl

@[simp] lemma doubleNegation_verum : (⊤ : Semiformula L ξ n)ᴺ = ∼⊥ := rfl

@[simp] lemma doubleNegation_falsum : (⊥ : Semiformula L ξ n)ᴺ = ⊥ := rfl

@[simp] lemma doubleNegation_and (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ)ᴺ = φᴺ ⋏ ψᴺ := rfl

@[simp] lemma doubleNegation_or (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ)ᴺ = ∼(∼φᴺ ⋏ ∼ψᴺ) := rfl

@[simp] lemma doubleNegation_all (φ : Semiformula L ξ (n + 1)) : (∀¹ φ)ᴺ = ∀¹ φᴺ := rfl

@[simp] lemma doubleNegation_ex (φ : Semiformula L ξ (n + 1)) : (∃¹ φ)ᴺ = ∼(∀¹ ∼φᴺ) := rfl

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
  induction φ using rec' generalizing n₂ <;> simp [Semiformulaᵢ.rew_rel, *, Function.comp_def]

lemma subst_doubleNegation (φ : Semiformula L ξ n₁) (v : Fin n₁ → Semiterm L ξ n₂) :
    φᴺ ⇜ v = (φ ⇜ v)ᴺ := rew_doubleNegation _ _

lemma emb_doubleNegation (φ : Semisentence L n₁) :
    Rewriting.emb (φᴺ) = (Rewriting.emb φ : Semiformula L ξ n₁)ᴺ := rew_doubleNegation _ _

end Semiformula

namespace Sequent

def doubleNegation (Γ : Sequent L) : LJ.Sequent L :=
  Γ.map Semiformula.doubleNegation

scoped[LO.FirstOrder] postfix:max "ᴺ" => Sequent.doubleNegation

@[simp] lemma doubleNegation_zero : (0 : Sequent L)ᴺ = 0 := rfl

@[simp] lemma doubleNegation_atom (φ : Proposition L) :
    (⦃φ⦄ : Sequent L)ᴺ = ⦃φᴺ⦄ := by simp [doubleNegation]

@[simp] lemma doubleNegation_add (Γ Δ : Sequent L) : (Γ + Δ)ᴺ = Γᴺ + Δᴺ := by
  simp [doubleNegation]

lemma shift_doubleNegation (Γ : Sequent L) : (Γᴺ)⁺ᵐ = (Γ⁺ᵐ)ᴺ := by
  simp [Sequent.doubleNegation, Rewriting.shiftsM, Semiformula.rew_doubleNegation]

end Sequent

def Theory.doubleNegation (T : Theory L) : Theoryᵢ L :=
  Semiformula.doubleNegation '' T

namespace LJ.Derivation

open Rewriting LawfulSyntacticRewriting

variable {L : Language} [L.DecidableEq]

def negDoubleNegation : (φ : Proposition L) →
    Interderivable L (∼φᴺ) ((∼φ)ᴺ)
  | .rel R v => Interderivable.dne (by simp)
  | .nrel R v => Interderivable.refl _
  | ⊤ => by
      constructor
      · exact negElim (eta (∼(⊤ : Propositionᵢ L))) <|
          weakening verum (by simp)
      · apply positiveNeg
        exact assumption (by simp)
  | ⊥ => Interderivable.refl _
  | φ ⋏ ψ => by
      have eφ := (negDoubleNegation φ).iffnegOfNegIff (by simp)
      have eψ := (negDoubleNegation ψ).iffnegOfNegIff (by simp)
      simpa using (eφ.and eψ).neg
  | φ ⋎ ψ => by
      have e := (negDoubleNegation φ).and (negDoubleNegation ψ)
      exact (Interderivable.dne (by simp)).trans e
  | ∀¹ φ => by
      have e := (negDoubleNegation (Rewriting.free φ)).iffnegOfNegIff (by simp)
      have e : Interderivable L (Rewriting.free φᴺ)
          (Rewriting.free (∼(∼φ)ᴺ)) :=
        by simpa [Semiformula.rew_doubleNegation] using e
      simpa using (Interderivable.all e).neg
  | ∃¹ φ => by
      have e := negDoubleNegation (Rewriting.free φ)
      have e : Interderivable L (Rewriting.free (∼φᴺ))
          (Rewriting.free ((∼φ)ᴺ)) :=
        by simpa [Semiformula.rew_doubleNegation] using e
      exact (Interderivable.dne (by simp)).trans (Interderivable.all e)
  termination_by φ => φ.complexity

def negDoubleNegation' (φ : Proposition L) :
    Interderivable L (∼(∼φ)ᴺ) φᴺ := by
  simpa using negDoubleNegation (∼φ)

end LJ.Derivation

namespace Derivation

open Rewriting LawfulSyntacticRewriting

variable {L : Language} [L.DecidableEq]

/-- Discharges a translated negated formula from an LJ contradiction derivation. -/
def deductNeg {Γ : Sequent L} {φ : Proposition L}
    (d : (∼(Γ + ⦃φ⦄))ᴺ ⊢ᴸᴶ¹ (⊥ : Propositionᵢ L)) :
    (∼Γ)ᴺ ⊢ᴸᴶ¹ (∼(∼φ)ᴺ : Propositionᵢ L) :=
  LJ.Derivation.positiveNeg (Γ := (∼Γ)ᴺ) (φ := (∼φ)ᴺ) <|
    d.cast (by simp)

def gödelGentzen {Γ : Sequent L} : ⊢ᴸᴷ¹ Γ → (∼Γ)ᴺ ⊢ᴸᴶ¹ (⊥ : Propositionᵢ L)
  | identity R v => by
      exact LJ.Derivation.contraction
        (LJ.Derivation.eta (∼(.rel R v) : Propositionᵢ L)).negativeNeg
        (by simp [Sequent.doubleNegation]) (by simp)
  | verum => by
      simpa [Sequent.doubleNegation] using LJ.Derivation.eta (⊥ : Propositionᵢ L)
  | and (Γ := Γ) (φ := φ) (ψ := ψ) dφ dψ => by
      have dφ : (∼Γ)ᴺ ⊢ᴸᴶ¹ (∼(∼φ)ᴺ : Propositionᵢ L) :=
        deductNeg (gödelGentzen dφ)
      have dψ : (∼Γ)ᴺ ⊢ᴸᴶ¹ (∼(∼ψ)ᴺ : Propositionᵢ L) :=
        deductNeg (gödelGentzen dψ)
      have dAnd := LJ.Derivation.positiveAnd dφ dψ
      exact LJ.Derivation.contraction dAnd.negativeNeg
        (by simp [Sequent.doubleNegation]) (by simp)
  | or (Γ := Γ) (φ := φ) (ψ := ψ) d =>
      (LJ.Derivation.negativeAnd (Γ := (∼Γ)ᴺ) (φ := (∼φ)ᴺ)
        (ψ := (∼ψ)ᴺ) (Ξ := (⊥ : Propositionᵢ L)) <|
        (gödelGentzen d).cast (by simp)).cast (by simp [Sequent.doubleNegation])
  | all (Γ := Γ) (φ := φ) d => by
      have hshift : (∼Γ⁺ᵐ)ᴺ = ((∼Γ)ᴺ)⁺ᵐ := by
        rw [←Rewriting.shiftsM_neg, Sequent.shift_doubleNegation]
      have dFree : ((∼Γ)ᴺ)⁺ᵐ ⊢ᴸᴶ¹
          (∼Rewriting.free ((∼φ)ᴺ) : Propositionᵢ L) :=
        (deductNeg (gödelGentzen d)).cast
          (by simp [hshift]) (by simp [Semiformula.rew_doubleNegation])
      have dAll := LJ.Derivation.positiveForall (Γ := (∼Γ)ᴺ)
        (φ := ∼(∼φ)ᴺ) <|
        dFree.cast (heq := by simp [Semiformula.rew_doubleNegation])
      exact LJ.Derivation.contraction dAll.negativeNeg
        (by simp [Sequent.doubleNegation]) (by simp)
  | exs (Γ := Γ) (φ := φ) (t := t) d =>
      (LJ.Derivation.negativeForall (Γ := (∼Γ)ᴺ) (φ := (∼φ)ᴺ)
        (t := t) (Ξ := (⊥ : Propositionᵢ L)) <|
        (gödelGentzen d).cast (by simp [Semiformula.rew_doubleNegation]))
        |>.cast (by simp [Sequent.doubleNegation])
  | cut (Γ := Γ) (Δ := Δ) (φ := φ) d dn => by
      have ihn := gödelGentzen dn
      have dnφ : (∼Γ)ᴺ ⊢ᴸᴶ¹ (∼(∼φ)ᴺ : Propositionᵢ L) :=
        deductNeg (gödelGentzen d)
      have dφ : (∼Γ)ᴺ ⊢ᴸᴶ¹ φᴺ :=
        LJ.Derivation.cutOne dnφ (LJ.Derivation.negDoubleNegation' φ).1
      exact (LJ.Derivation.cut (Γ := (∼Γ)ᴺ) (Δ := (∼Δ)ᴺ)
        (φ := φᴺ) (Ξ := (⊥ : Propositionᵢ L)) dφ <|
        ihn.cast (by simp)).cast (by simp [Sequent.doubleNegation])
  | contraction d h =>
      LJ.Derivation.weakening (gödelGentzen d) <|
        Multiset.map_subset_map <| Multiset.map_subset_map h

end Derivation

theorem Provable.gödel_gentzen {L : Language.{u}} [L.DecidableEq] {φ : Proposition L} :
    𝐋𝐊¹ ⊢ φ → 𝐋𝐉¹ ⊢ φᴺ := by
  rintro ⟨d⟩
  have d : ⦃(∼φ)ᴺ⦄ ⊢ᴸᴶ¹ (⊥ : Propositionᵢ L) := by
    simpa [Sequent.doubleNegation] using Derivation.gödelGentzen d
  have dn : (0 : LJ.Sequent L) ⊢ᴸᴶ¹ (∼(∼φ)ᴺ : Propositionᵢ L) :=
    LJ.Derivation.positiveNeg (φ := (∼φ)ᴺ) d
  exact ⟨LJ.Derivation.cutOne dn (LJ.Derivation.negDoubleNegation' φ).1⟩

end LO.FirstOrder
