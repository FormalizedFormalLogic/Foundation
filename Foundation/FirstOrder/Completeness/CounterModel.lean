module

public import Foundation.FirstOrder.Completeness.CanonicalModel
public import Foundation.Vorspiel.Order.Dense
public import Mathlib.Logic.Equiv.List
public import Mathlib.Logic.Encodable.Basic

@[expose] public section

namespace LO.FirstOrder.Derivation.Canonical

open Order

variable {L : Language}

local notation "ℙ" => Sequent L
local notation "ℙ⁻" => ConsistentSequent L

scoped notation "ℍ" => LowerSet ℙ⁻

instance [L.Encodable] [L.DecidableEq] : Encodable (Sequent L) := List.encodable

open Classical in
noncomputable instance [L.Encodable] : Encodable ℙ⁻ := Subtype.encodable

open Classical
def decidablePoints (φ : Proposition L) : DenseSet ℙ⁻ where
  set := {p | p ⊩ᶜ φ ∨ p ⊩ᶜ ∼φ}
  is_dense := by
    intro p
    have : p ⊩ᶜ φ ⋎ ∼φ := IsWeaklyForced.complete.mpr Entailment.lem! p
    have : ∀ q ≤ p, ∃ r ≤ q, r ⊩ᶜ φ ∨ r ⊩ᶜ ∼φ := by simpa using this
    simpa using this p (by rfl)

@[simp] lemma mem_decidablePoints_def (p : ℙ⁻) (φ : Proposition L) :
    p ∈ decidablePoints φ ↔ p ⊩ᶜ φ ∨ p ⊩ᶜ ∼φ := by rfl

def henkinPoints (φ : Semiproposition L 1) : DenseSet ℙ⁻ where
  set := {p | ∀ q ≤ p, q ⊩ᶜ ∃⁰ φ → ∃ t, q ⊩ᶜ φ/[t]}
  is_dense := by
    intro p
    suffices ∃ q ≤ p, ∀ q_1 ≤ q, (∀ q ≤ q_1, ∃ r ≤ q, ∃ t, r ⊩ᶜ φ/[t]) → ∃ t, q_1 ⊩ᶜ φ/[t] by
      simpa only [IsWeaklyForced.exs, Set.mem_setOf_eq]
    have : p ⊩ᶜ (∃⁰ φ) ⋎ (∀⁰ ∼φ) := IsWeaklyForced.complete.mpr Entailment.lem! p
    have : ∀ q ≤ p, ∃ r ≤ q, (∀ q ≤ r, ∃ r ≤ q, ∃ t, r ⊩ᶜ φ/[t]) ∨
        (∀ t, ∀ q ≤ r, ¬q ⊩ᶜ φ/[t]) := by simpa using this
    rcases this p (by rfl) with ⟨q, hqp, (h | h)⟩
    · rcases h q (by rfl) with ⟨r, hrq, t, ht⟩
      refine ⟨r, le_trans hrq hqp, fun s hsr _ ↦ ⟨t, IsWeaklyForced.monotone hsr ht⟩⟩
    · refine ⟨q, hqp, ?_⟩
      intro r hrq hA
      rcases hA r (by rfl) with ⟨s, hsr, u, hu⟩
      have : ¬s ⊩ᶜ φ/[u] := h u s (le_trans hsr hrq)
      contradiction

@[simp] lemma mem_henkinPoints_def (p : ℙ⁻) (φ : Semiproposition L 1) :
    p ∈ henkinPoints φ ↔ ∀ q ≤ p, q ⊩ᶜ ∃⁰ φ → ∃ t, q ⊩ᶜ φ/[t] := by rfl

abbrev denseSets : Set (DenseSet ℙ⁻) := Set.range decidablePoints ∪ Set.range henkinPoints

variable [L.Encodable]

theorem exists_genericFilter (p : ℙ⁻) :
    ∃ G : PFilter ℙ⁻, G.IsGeneric denseSets ∧ p ∈ G :=
  PFilter.exists_genericFilter_of_countable denseSets
    (Set.countable_union.mpr ⟨Set.countable_range decidablePoints, Set.countable_range henkinPoints⟩) p

noncomputable def genericFilter (p : ℙ⁻) : PFilter ℙ⁻ := Classical.choose (exists_genericFilter p)

instance genericFilter_isGeneric (p : ℙ⁻) : (genericFilter p).IsGeneric denseSets :=
  Classical.choose_spec (exists_genericFilter p) |>.1

@[simp] lemma mem_genericFilter (p : ℙ⁻) : p ∈ genericFilter p :=
  Classical.choose_spec (exists_genericFilter p) |>.2

def GenericForces (p : ℙ⁻) (φ : Proposition L) : Prop := ∃ q ∈ genericFilter p, q ⊩ᶜ φ

local infix: 60 " ⊫ " => GenericForces

lemma GenericForces.em (p : ℙ⁻) (φ : Proposition L) : p ⊫ φ ∨ p ⊫ ∼φ := by
  have : ∃ q ∈ genericFilter p, q ∈ decidablePoints φ :=
    (genericFilter_isGeneric p).isGeneric (decidablePoints φ) (by simp)
  rcases this with ⟨q, hqG, hq⟩
  have : q ⊩ᶜ φ ∨ q ⊩ᶜ ∼φ := by simpa using hq
  rcases this with (em | em)
  · left
    refine ⟨q, hqG, em⟩
  · right
    refine ⟨q, hqG, em⟩

@[simp] lemma GenericForces.neg {p : ℙ⁻} {φ : Proposition L} : p ⊫ ∼φ ↔ ¬p ⊫ φ := by
  suffices p ⊫ ∼φ → p ⊫ φ → False by
    have := GenericForces.em p φ
    grind
  rintro ⟨q₀, hG₀, h₀⟩
  rintro ⟨q₁, hG₁, h₁⟩
  have : ∃ r ∈ genericFilter p, r ≤ q₀ ∧ r ≤ q₁ := (genericFilter p).directed _ hG₀ _ hG₁
  rcases this with ⟨r, hG, hr₀, hr₁⟩
  have : r ⊩ᶜ φ := h₁.monotone hr₁
  have : ¬r ⊩ᶜ φ := IsWeaklyForced.not.mp h₀ r (by assumption)
  contradiction

@[simp] lemma GenericForces.verum (p : ℙ⁻) : p ⊫ ⊤ :=
  ⟨p, by simp⟩

@[simp] lemma GenericForces.not_falsum (p : ℙ⁻) : ¬p ⊫ ⊥ := by
  rintro ⟨q, hq⟩; simp_all

@[simp] lemma GenericForces.nrel {p : ℙ⁻} : p ⊫ .nrel R v ↔ ¬p ⊫ .rel R v := calc
  p ⊫ .nrel R v ↔ p ⊫ ∼(.rel R v) := by simp
  _         ↔ ¬p ⊫ .rel R v := by rw [GenericForces.neg]

lemma GenericForces.henkin {p : ℙ⁻} {φ : Semiproposition L 1} : p ⊫ ∃⁰ φ → ∃ t, p ⊫ φ/[t] := by
  have : ∃ q ∈ genericFilter p, ∀ r ≤ q, r ⊩ᶜ ∃⁰ φ → ∃ t, r ⊩ᶜ φ/[t] :=
    (genericFilter_isGeneric p).isGeneric (henkinPoints φ) (by simp)
  rcases this with ⟨q, hqG, H⟩
  rintro ⟨r, hrG, hr⟩
  have : ∃ z ∈ genericFilter p, z ≤ q ∧ z ≤ r := (genericFilter p).directed _ hqG _ hrG
  rcases this with ⟨z, hGz, hzq, hzr⟩
  have : ∃ t, z ⊩ᶜ φ/[t] := H z hzq (hr.monotone hzr)
  rcases this with ⟨t, hzt⟩
  refine ⟨t, ⟨z, hGz, hzt⟩⟩

@[simp] lemma GenericForces.exs {p : ℙ⁻} : p ⊫ ∃⁰ φ ↔ ∃ t, p ⊫ φ/[t] := by
  constructor
  · exact GenericForces.henkin
  · rintro ⟨t, q, hqG, h⟩
    refine ⟨q, hqG, ?_⟩
    suffices ∀ r ≤ q, ∃ s ≤ r, ∃ t, s ⊩ᶜ φ/[t] by simpa
    intro r hrq
    refine ⟨r, by simp, t, h.monotone hrq⟩

@[simp] lemma GenericForces.fal {p : ℙ⁻} : p ⊫ ∀⁰ φ ↔ ∀ t, p ⊫ φ/[t] := calc
  p ⊫ ∀⁰ φ ↔ p ⊫ ∼(∃⁰ ∼φ) := by simp
  _         ↔ ¬p ⊫ ∃⁰ ∼φ := by rw [GenericForces.neg]
  _         ↔ ∀ t, p ⊫ φ/[t] := by simp [GenericForces.exs]

@[simp] lemma GenericForces.and {p : ℙ⁻} {φ ψ : Proposition L} : p ⊫ φ ⋏ ψ ↔ p ⊫ φ ∧ p ⊫ ψ := by
  constructor
  · rintro ⟨q, hqG, hq⟩
    have : q ⊩ᶜ φ ∧ q ⊩ᶜ ψ := by simpa using hq
    rcases this with ⟨hφ, hψ⟩
    exact ⟨⟨q, hqG, hφ⟩, ⟨q, hqG, hψ⟩⟩
  · rintro ⟨⟨q₁, hG₁, h₁⟩, ⟨q₂, hG₂, h₂⟩⟩
    have : ∃ r ∈ genericFilter p, r ≤ q₁ ∧ r ≤ q₂ := (genericFilter p).directed _ hG₁ _ hG₂
    rcases this with ⟨r, hGr, hr₁, hr₂⟩
    refine ⟨r, hGr, ?_⟩
    have : r ⊩ᶜ φ := h₁.monotone hr₁
    have : r ⊩ᶜ ψ := h₂.monotone hr₂
    simp [*]

@[simp] lemma GenericForces.or {p : ℙ⁻} {φ ψ : Proposition L} : p ⊫ φ ⋎ ψ ↔ p ⊫ φ ∨ p ⊫ ψ := calc
  p ⊫ φ ⋎ ψ ↔ p ⊫ ∼(∼φ ⋏ ∼ψ) := by simp
  _         ↔ ¬p ⊫ ∼φ ⋏ ∼ψ := by rw [GenericForces.neg]
  _         ↔ p ⊫ φ ∨ p ⊫ ψ := by simp; tauto

local notation "𝔗" => Term L ℕ

abbrev termModelOf (p : ℙ⁻) : Structure L 𝔗 where
  func _ f v := .func f v
  rel _ R v := p ⊫ .rel R v

@[simp] lemma termModel_func_def (f : L.Func k) (v : Fin k → 𝔗) :
    (termModelOf p).func f v = Semiterm.func f v := rfl

@[simp] lemma termModel_rel_def (R : L.Rel k) (v) :
    (termModelOf p).rel R v ↔ p ⊫ .rel R v := by rfl

@[simp] lemma termModel_val_eq (t : Semiterm L ξ n) (fv : ξ → 𝔗) (bv : Fin n → 𝔗) :
    t.val (s := termModelOf p) bv fv = Rew.bind bv fv t := by
  induction t <;> simp [*, Function.comp_def]

lemma forcing_lemma (φ : Semiformula L ξ n) (fv : ξ → 𝔗) (bv : Fin n → 𝔗) :
    φ.Eval (s := termModelOf p) bv fv ↔ p ⊫ Rew.bind bv fv ▹ φ :=
  have e (t : 𝔗) (φ : Semiformula L ξ (n + 1)) : ((Rew.bind bv fv).q ▹ φ)/[t] = Rew.bind (t :> bv) fv ▹ φ := by
    unfold Rewriting.subst; rw [←TransitiveRewriting.comp_app]
    congr; ext x
    · cases x using Fin.cases <;> simp [Rew.comp_app]
    · simp [Rew.comp_app]
  match φ with
  | .rel R v | .nrel R v => by simp [Function.comp_def]
  | ⊤ | ⊥ => by simp
  | φ ⋏ ψ | φ ⋎ ψ => by simp [forcing_lemma φ, forcing_lemma ψ]
  | ∀⁰ φ | ∃⁰ φ => by simp [e, forcing_lemma φ]

end LO.FirstOrder.Derivation.Canonical
