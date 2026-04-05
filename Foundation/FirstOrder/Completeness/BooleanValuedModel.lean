module

public import Foundation.Vorspiel.Order.LowerSet
public import Foundation.Vorspiel.Order.Ideal
public import Foundation.Vorspiel.Order.Heyting
public import Foundation.FirstOrder.Completeness.CanonicalModel
public import Mathlib.Order.PFilter

@[expose] public section

/-!
# Heyting and Boolean-valued model associated to the canonical model

Main reference: Jeremy Avigad, Algebraic proofs of cut elimination [Avi01]
 -/

namespace LO.FirstOrder.Derivation

variable {L : Language}

namespace Canonical

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

/-- ## Heyting-valued model -/

local notation "ℍ" => LowerSet ℂ

instance : Nontrivial ℍ := ⟨⊥, ⊤, fun e ↦ by simpa using SetLike.ext_iff.mp e default⟩

def hValue (φ : Propositionᵢ L) : ℍ where
  carrier := { p | p.val ⊩ φ }
  lower' := fun _ _ hqp hp ↦ IsForced.monotone hqp hp

scoped prefix:max "♯" => hValue

lemma hValue_ext {φ ψ : Propositionᵢ L} : (∀ p : ℂ, p.val ⊩ φ ↔ p.val ⊩ ψ) → ♯φ = ♯ψ := by
  intro h; ext p; simp [hValue, h]

@[simp] lemma mem_hValue {p : ℂ} {φ : Propositionᵢ L} : p ∈ ♯φ ↔ p.val ⊩ φ := by simp [hValue]

@[simp] lemma hValue_and_eq_inf {φ ψ : Propositionᵢ L} : ♯(φ ⋏ ψ) = (♯φ ⊓ ♯ψ) := by
  ext p; simp [hValue]

@[simp] lemma hValue_or_eq_sup {φ ψ : Propositionᵢ L} : ♯(φ ⋎ ψ) = (♯φ ⊔ ♯ψ) := by
  ext p; simp [hValue]

@[simp] lemma hValue_fal_eq_Inf {φ : Semipropositionᵢ L 1} : ♯(∀⁰ φ) = ⨅ t, ♯(φ/[t]) := by
  ext p; simp [hValue,]

@[simp] lemma hValue_exs_eq_Sup {φ : Semipropositionᵢ L 1} : ♯(∃⁰ φ) = ⨆ t, ♯(φ/[t]) := by
  ext p; simp [hValue,]

@[simp] lemma hValue_falsum : ♯(⊥ : Propositionᵢ L) = ⊥ := by
  ext p; simp [hValue, IsForced.falsum, p.prop]

@[simp] lemma hValue_imply_eq_himp {φ ψ : Propositionᵢ L} : ♯(φ 🡒 ψ) = (♯φ ⇨ ♯ψ) := by
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

@[simp] lemma hValue_neg_eq_himp_bot (φ : Propositionᵢ L) : ♯(∼φ) = (♯φ)ᶜ := by
  simp [Semiformulaᵢ.neg_def]

set_option backward.isDefEq.respectTransparency false in
lemma hValue_eq_top_iff_provable {φ : Proposition L} : ♯φᴺ = ⊤ ↔ 𝐋𝐊¹ ⊢ φ := calc
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

lemma hValue_lt_top_iff_provable {φ : Proposition L} : ♯φᴺ < ⊤ ↔ 𝐋𝐊¹ ⊬ φ := by
  simp [Entailment.Unprovable, ←hValue_eq_top_iff_provable, lt_top_iff_ne_top]

lemma hValue_dn_neg (φ : Proposition L) : ♯(∼φ)ᴺ = (♯φᴺ)ᶜ := calc
  ♯(∼φ)ᴺ = ♯(∼φᴺ) := hValue_ext <| by simp [←IsForced.dn_neg_iff]
  _      = (♯φᴺ)ᶜ := by simp

@[simp] lemma dn_isRegular (φ : Proposition L) : Heyting.IsRegular ♯φᴺ := by
  have : ♯φᴺ = (♯(∼φ)ᴺ)ᶜ := by simp [←hValue_dn_neg]
  simpa [this] using Heyting.isRegular_compl ♯(∼φ)ᴺ

/-- ## Boolean-valued model -/

local notation "𝔹" => Heyting.Regular ℍ

instance : Nontrivial 𝔹 :=
  ⟨⊥, ⊤, fun e ↦ by simpa using Heyting.Regular.coe_inj.mpr e⟩

/-- Boolean value -/
def bValue (φ : Proposition L) : 𝔹 := ⟨♯φᴺ, by simp⟩

scoped prefix:max "♭" => bValue

@[simp] lemma coe_bValue (φ : Proposition L) : (♭φ : ℍ) = ♯φᴺ := rfl

@[simp] lemma bValue_and_eq_inf : ♭(φ ⋏ ψ) = ♭φ ⊓ ♭ψ := Heyting.Regular.coe_inj.mp <| by simp

@[simp] lemma bValue_or_eq_sup : ♭(φ ⋎ ψ) = ♭φ ⊔ ♭ψ := Heyting.Regular.coe_inj.mp <| by simp

@[simp] lemma bValue_fal_eq_Inf : ♭(∀⁰ φ) = ⨅ t, ♭(φ/[t]) := Heyting.Regular.coe_inj.mp <| by
  simp [Semiformula.subst_doubleNegation]

@[simp] lemma bValue_exs_eq_Sup : ♭(∃⁰ φ) = ⨆ t, ♭(φ/[t]) := Heyting.Regular.coe_inj.mp <| by
  simp [Semiformula.subst_doubleNegation, compl_iSup']

@[simp] lemma bValue_neg_eq_himp : ♭(∼φ) = (♭φ)ᶜ := Heyting.Regular.coe_inj.mp <| by
  simp [hValue_dn_neg]

@[simp] lemma bValue_falsum : ♭(⊥ : Proposition L) = ⊥ := Heyting.Regular.coe_inj.mp <| by simp

lemma bValue_eq_top_iff_provable : ♭φ = ⊤ ↔ 𝐋𝐊¹ ⊢ φ := calc
  ♭φ = ⊤ ↔ ♯φᴺ = ⊤ := by rw [←Heyting.Regular.coe_inj]; simp
  _      ↔ 𝐋𝐊¹ ⊢ φ := hValue_eq_top_iff_provable

lemma bValue_lt_top_iff_provable : ♭φ < ⊤ ↔ 𝐋𝐊¹ ⊬ φ := by
  simp [Entailment.Unprovable, ←bValue_eq_top_iff_provable, lt_top_iff_ne_top]

/-- Filter induced by a schema -/
def _root_.LO.FirstOrder.Schema.filter (𝔖 : Schema L) : Order.PFilter 𝔹 :=
  ⟨⨆ φ ∈ 𝔖, Order.Ideal.principal ♭φ⟩

@[simp] lemma mem_filter_iff {𝔖 : Schema L} {x} :
    x ∈ 𝔖.filter ↔ ∃ u : Finset (Proposition L), (∀ φ ∈ u, φ ∈ 𝔖) ∧ ⨅ φ ∈ u, ♭φ ≤ x := by sorry

lemma bValue_mem_filter_iff_provable {𝔖 : Schema L} {φ : Proposition L} :
    ♭φ ∈ 𝔖.filter ↔ 𝔖 ⊢ φ := by sorry

end Canonical

end LO.FirstOrder.Derivation
