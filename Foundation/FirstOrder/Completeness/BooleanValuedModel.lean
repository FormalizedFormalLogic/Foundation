module

public import Foundation.Vorspiel.Order.LowerSet
public import Foundation.Vorspiel.Order.Ideal
public import Foundation.Vorspiel.Order.Heyting
public import Foundation.Vorspiel.Order.Lattice
public import Foundation.FirstOrder.Completeness.CanonicalModel
public import Mathlib.Order.PFilter
public import Mathlib.Order.PrimeSeparator

@[expose] public section

/-!
# Heyting and Boolean-valued model associated to the canonical model

Main reference: Jeremy Avigad, Algebraic proofs of cut elimination [Avi01]
 -/

namespace LO.FirstOrder.Derivation

variable {L : Language}

namespace Canonical

open Classical

variable (L)

def ConsistentSequent := {Γ : Sequent L // IsEmpty (⊢ᴸᴷ¹ ∼Γ)}

variable {L}

local notation "ℙ" => Sequent L

local notation "ℂ" => ConsistentSequent L

namespace ConsistentSequent

instance : Preorder ℂ where
  le q p := q.val ≤ p.val
  le_refl p := by simp
  le_trans p q r := le_trans

instance : Inhabited ℂ := ⟨⟨[], by simp⟩⟩

end ConsistentSequent

/-! ## Heyting-valued model -/

namespace HeytingValuedModel

scoped notation "ℍ" => LowerSet ℂ

instance : Order.Frame ℍ := inferInstance

instance : Nontrivial ℍ := ⟨⊥, ⊤, fun e ↦ by simpa using SetLike.ext_iff.mp e default⟩

/-- Heyting value of a proposition -/
def hValue (φ : Propositionᵢ L) : ℍ where
  carrier := { p | p.val ⊩ φ }
  lower' := fun _ _ hqp hp ↦ IsForced.monotone hqp hp

scoped prefix:max "♯" => hValue

protected lemma ext {φ ψ : Propositionᵢ L} : (∀ p : ℂ, p.val ⊩ φ ↔ p.val ⊩ ψ) → ♯φ = ♯ψ := by
  intro h; ext p; simp [hValue, h]

@[simp] lemma mem_hValue {p : ℂ} {φ : Propositionᵢ L} : p ∈ ♯φ ↔ p.val ⊩ φ := by simp [hValue]

@[simp] lemma falsum : ♯(⊥ : Propositionᵢ L) = ⊥ := by
  ext p; simp [hValue, IsForced.falsum, p.prop]

@[simp] lemma imply_eq_himp {φ ψ : Propositionᵢ L} : ♯(φ 🡒 ψ) = (♯φ ⇨ ♯ψ) := by
  ext p
  suffices (∀ q ≤ p.val, q ⊩ φ → q ⊩ ψ) ↔ ∀ q ≤ p, q.val ⊩ φ → q.val ⊩ ψ by
    simpa [IsForced.imply, LowerSet.mem_himp_iff]
  constructor
  · intro h q hqp hqφ
    exact h q.val hqp hqφ
  · intro h q hqp hqφ
    by_cases! hq : IsEmpty (⊢ᴸᴷ¹ ∼q)
    · exact h ⟨q, hq⟩ hqp hqφ
    · exact IsForced.efq (p := q) (by simp [IsForced.falsum, hq]) ψ

@[simp] lemma and_eq_inf {φ ψ : Propositionᵢ L} : ♯(φ ⋏ ψ) = (♯φ ⊓ ♯ψ) := by
  ext p; simp [hValue]

@[simp] lemma or_eq_sup {φ ψ : Propositionᵢ L} : ♯(φ ⋎ ψ) = (♯φ ⊔ ♯ψ) := by
  ext p; simp [hValue]

@[simp] lemma fal_eq_Inf {φ : Semipropositionᵢ L 1} : ♯(∀⁰ φ) = ⨅ t, ♯(φ/[t]) := by
  ext p; simp [hValue,]

@[simp] lemma exs_eq_Sup {φ : Semipropositionᵢ L 1} : ♯(∃⁰ φ) = ⨆ t, ♯(φ/[t]) := by
  ext p; simp [hValue,]

@[simp] lemma neg_eq_himp_bot (φ : Propositionᵢ L) : ♯(∼φ) = (♯φ)ᶜ := by
  simp [Semiformulaᵢ.neg_def]

set_option backward.isDefEq.respectTransparency false in
/-- Completeness of the Heyting-valued model `ℍ` -/
lemma complete {φ : Proposition L} : ♯φᴺ = ⊤ ↔ 𝐋𝐊¹ ⊢ φ := calc
  ♯φᴺ = ⊤ ↔ ⊤ ≤ ♯φᴺ := by simp only [top_le_iff]
  _       ↔ (∀ p : ℂ, p.val ⊩ φᴺ) := by simp [SetLike.le_def]
  _       ↔ ℙ ∀⊩ φᴺ := by
    constructor
    · intro h p
      by_cases! hp : IsEmpty (⊢ᴸᴷ¹ ∼p)
      · exact h ⟨p, hp⟩
      · exact IsForced.efq (p := p) (by simp [IsForced.falsum, hp]) φᴺ
    · intro h p; exact h p.val
  _       ↔ 𝐋𝐊¹ ⊢ φ := IsForced.complete

lemma cocomplete {φ : Proposition L} : ♯φᴺ < ⊤ ↔ 𝐋𝐊¹ ⊬ φ := by
  simp [Entailment.Unprovable, ←complete, lt_top_iff_ne_top]

lemma hValue_dn_neg (φ : Proposition L) : ♯(∼φ)ᴺ = (♯φᴺ)ᶜ := calc
  ♯(∼φ)ᴺ = ♯(∼φᴺ) := HeytingValuedModel.ext <| by simp [←IsForced.dn_neg_iff]
  _      = (♯φᴺ)ᶜ := by simp

@[simp] lemma dn_isRegular (φ : Proposition L) : Heyting.IsRegular ♯φᴺ := by
  have : ♯φᴺ = (♯(∼φ)ᴺ)ᶜ := by simp [←hValue_dn_neg]
  simpa [this] using Heyting.isRegular_compl ♯(∼φ)ᴺ

end HeytingValuedModel

/-! ## Boolean-valued model -/

namespace BooleanValuedModel

open HeytingValuedModel

scoped notation "𝔹" => Heyting.Regular ℍ

instance : CompleteBooleanAlgebra 𝔹 := inferInstance

instance : Nontrivial 𝔹 :=
  ⟨⊥, ⊤, fun e ↦ by simpa using Heyting.Regular.coe_inj.mpr e⟩

/-- Boolean value of a proposition -/
def bValue (φ : Proposition L) : 𝔹 := ⟨♯φᴺ, by simp⟩

scoped prefix:max "♭" => bValue

@[simp] lemma coe_bValue (φ : Proposition L) : (♭φ : ℍ) = ♯φᴺ := rfl

@[simp] lemma falsum : ♭(⊥ : Proposition L) = ⊥ := Heyting.Regular.coe_inj.mp <| by simp

@[simp] lemma verum : ♭(⊤ : Proposition L) = ⊤ := Heyting.Regular.coe_inj.mp <| by simp

@[simp] lemma and_eq_inf : ♭(φ ⋏ ψ) = ♭φ ⊓ ♭ψ := Heyting.Regular.coe_inj.mp <| by simp

@[simp] lemma lConj_eq_inf (Γ : List (Proposition L)) : ♭(⋀Γ) = Γ.toFinset.inf bValue :=
  match Γ with
  |          [] => by simp
  |         [φ] => by simp
  | φ :: ψ :: Γ => by
    simp [lConj_eq_inf (ψ :: Γ),]; rfl

@[simp] lemma or_eq_sup : ♭(φ ⋎ ψ) = ♭φ ⊔ ♭ψ := Heyting.Regular.coe_inj.mp <| by simp

@[simp] lemma fal_eq_Inf : ♭(∀⁰ φ) = ⨅ t, ♭(φ/[t]) := Heyting.Regular.coe_inj.mp <| by
  simp [Semiformula.subst_doubleNegation]

@[simp] lemma exs_eq_Sup : ♭(∃⁰ φ) = ⨆ t, ♭(φ/[t]) := Heyting.Regular.coe_inj.mp <| by
  simp [Semiformula.subst_doubleNegation, compl_iSup']

@[simp] lemma neg_eq_compl (φ : Proposition L) : ♭(∼φ) = (♭φ)ᶜ := Heyting.Regular.coe_inj.mp <| by
  simp [hValue_dn_neg]

@[simp] lemma imply_eq_himp (φ ψ : Proposition L) : ♭(φ 🡒 ψ) = (♭φ ⇨ ♭ψ) := by
  simp [Semiformula.imp_eq, BooleanAlgebra.himp_eq]; grind

/-- Completeness of the Boolean-valued model `𝔹` -/
lemma complete : ♭φ = ⊤ ↔ 𝐋𝐊¹ ⊢ φ := calc
  ♭φ = ⊤ ↔ ♯φᴺ = ⊤ := by rw [←Heyting.Regular.coe_inj]; simp
  _      ↔ 𝐋𝐊¹ ⊢ φ := HeytingValuedModel.complete

lemma cocomplete : ♭φ < ⊤ ↔ 𝐋𝐊¹ ⊬ φ := by
  simp [Entailment.Unprovable, ←complete, lt_top_iff_ne_top]

open Order OrderDual

/-- Filter induced by a schema `𝔖` -/
def _root_.LO.FirstOrder.Schema.filter (𝔖 : Schema L) : Order.PFilter 𝔹 :=
  ⟨⨆ φ : 𝔖, Ideal.principal (toDual ♭φ)⟩

open Classical

variable {𝔖 : Schema L}

lemma mem_filter_iff :
    x ∈ 𝔖.filter ↔ ∃ Γ : Finset (Proposition L), ↑Γ ⊆ 𝔖 ∧ Γ.inf bValue ≤ x := calc
  x ∈ 𝔖.filter ↔ toDual x ∈ ⨆ φ : 𝔖, Ideal.principal (P := 𝔹ᵒᵈ) (toDual ♭φ) := Order.PFilter.mem_mk _ _
  _            ↔ ∃ Γ : Finset 𝔖, toDual x ∈ Γ.sup (Ideal.principal ∘ toDual ∘ bValue ∘ Subtype.val) := by rw [Ideal.mem_iSup_iff]; rfl
  _            ↔ ∃ Γ : Finset 𝔖, toDual x ≤ Γ.sup (toDual ∘ bValue ∘ Subtype.val) := by simp [Ideal.mem_finsup_principal]
  _            ↔ ∃ Γ : Finset 𝔖, Γ.inf (bValue ∘ Subtype.val) ≤ x := exists_congr fun Γ ↦ by simp [OrderDual.toDual_le, Function.comp_def]
  _            ↔ ∃ Γ : Finset (Proposition L), ↑Γ ⊆ 𝔖 ∧ Γ.inf bValue ≤ x := by
    constructor
    · rintro ⟨Γ, hΓ⟩
      exact ⟨Γ.map (Function.Embedding.subtype _), fun x ↦ by simp; tauto, by simpa [Function.comp_def]⟩
    · rintro ⟨Γ, hΓ⟩
      refine ⟨Γ.subtype _, ?_⟩
      rw [Finset.subtype_inf_val_of]
      · exact hΓ.2
      · intro i hi; exact hΓ.1 hi

/-- Completeness of a filter induced by a schema `𝔖` -/
lemma filter_complete :
    ♭φ ∈ 𝔖.filter ↔ 𝔖 ⊢ φ := calc
  ♭φ ∈ 𝔖.filter ↔ ∃ Γ : Finset (Proposition L), ↑Γ ⊆ 𝔖 ∧ Γ.inf bValue ≤ ♭φ := mem_filter_iff
  _             ↔ ∃ Γ : List (Proposition L), ↑Γ.toFinset ⊆ 𝔖 ∧ Γ.toFinset.inf bValue ≤ ♭φ := by
    constructor
    · rintro ⟨Γ, hΓ⟩
      exact ⟨Γ.toList, by simpa using hΓ⟩
    · rintro ⟨Γ, hΓ⟩
      exact ⟨Γ.toFinset, by simpa using hΓ⟩
  _             ↔ ∃ Γ : List (Proposition L), ↑Γ.toFinset ⊆ 𝔖 ∧ 𝐋𝐊¹ ⊢ ⋀Γ 🡒 φ := by simp [←complete]
  _             ↔ 𝔖 *⊢[𝐋𝐊¹] φ := by
    constructor
    · rintro ⟨Γ, hΓ, ⟨b⟩⟩
      exact ⟨Γ, fun ψ hψ ↦ hΓ (by simpa using hψ), b⟩
    · intro ⟨b⟩
      exact ⟨b.ctx, fun ψ ↦ by simpa using b.subset ψ, ⟨b.prf⟩⟩
  _             ↔ 𝔖 ⊢ φ := Schema.iff_context.symm

lemma bot_not_mem_iff_consistent : ⊥ ∉ 𝔖.filter ↔ Entailment.Consistent 𝔖 := by
  simpa [←Entailment.inconsistent_iff_provable_bot] using Iff.not <| filter_complete (φ := ⊥) (𝔖 := 𝔖)

lemma primeIdeal_exists (𝔖 : Schema L) (con : Entailment.Consistent 𝔖) :
    ∃ J : Order.Ideal 𝔹, J.IsPrime ∧ Disjoint (𝔖.filter : Set 𝔹) J := by
  have : Disjoint (𝔖.filter : Set 𝔹) (⊥ : Ideal 𝔹) := Set.disjoint_iff.mpr <| by
    intro x
    have := bot_not_mem_iff_consistent.mpr con
    simp; grind
  simpa using DistribLattice.prime_ideal_of_disjoint_filter_ideal this

noncomputable def primeIdealOf (𝔖 : Schema L) (con : Entailment.Consistent 𝔖) : Ideal 𝔹 :=
  Classical.choose <| primeIdeal_exists 𝔖 con

lemma primeIdealOf_isPrime (𝔖 : Schema L) (con : Entailment.Consistent 𝔖) : (primeIdealOf 𝔖 con).IsPrime :=
  Classical.choose_spec (primeIdeal_exists 𝔖 con) |>.1

lemma primeIdealOf_disjoint (𝔖 : Schema L) (con : Entailment.Consistent 𝔖) :
    Disjoint (𝔖.filter : Set 𝔹) (primeIdealOf 𝔖 con) :=
  Classical.choose_spec (primeIdeal_exists 𝔖 con) |>.2

end BooleanValuedModel

end Canonical

end LO.FirstOrder.Derivation
