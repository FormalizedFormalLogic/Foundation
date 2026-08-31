module

public import Foundation.FirstOrder.Arithmetic.ISigma1.Prenex
public import Foundation.FirstOrder.Bootstrapping.Syntax.Theory
public import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Iteration
public import Foundation.FirstOrder.Basic.Padding

/-!
# Craig's trick
-/

@[expose] public section

namespace LO.FirstOrder.Theory

open LO.FirstOrder.Arithmetic

variable {L : Language} [L.Encodable] [L.LORDefinable]

noncomputable def «Σ₁witness» (T : Theory L) [T.«Σ₁»] : 𝚺₀.Semisentence 2 :=
  let h := ISigma1.exists_delta0_witness_provable T.«Σ₁ch».sigma_prop;
  .mkSigma h.choose h.choose_spec.1

lemma «Σ₁witness_spec» (T : Theory L) [T.«Σ₁»]
    (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin 1 → V) :
    V ⊧/e T.«Σ₁ch».val ↔ ∃ w, V ⊧/(w :> e) T.«Σ₁witness».val := by
  simpa [«Σ₁witness»] using
    (models_iff_of_provable_iff
      (ISigma1.exists_delta0_witness_provable T.«Σ₁ch».sigma_prop).choose_spec.2 V e).trans
      Semiformula.eval_ex

def craig (T : Theory L) [T.«Σ₁»] : Theory L :=
  { φ : Sentence L | ∃ (σ : Sentence L) (s : ℕ),
      ℕ ⊧/![(s : ℕ), ⌜σ⌝] T.«Σ₁witness».val ∧ φ = σ.padding s }

end LO.FirstOrder.Theory

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

def _root_.LO.FirstOrder.Theory.IsCraigAxiom (T : Theory L) [T.«Σ₁»] : V → Prop :=
  fun x ↦ ∃ s p : V, x = p ^⋏ qqVerums s ∧ V ⊧/![s, p] T.«Σ₁witness».val

noncomputable def _root_.LO.FirstOrder.Theory.craigCh (T : Theory L) [T.«Σ₁»]
  : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “x. ∃ s < x, ∃ p < x, ∃ v < x,
    !qqVerumsGraph v s ∧ !qqAndDef x p v ∧ !(T.«Σ₁witness».val) s p”
  )
  (.mkPi “x. ∃ s < x, ∃ p < x, ∃ v < x,
    (∀ v', !qqVerumsGraph v' s → v' = v) ∧ !qqAndDef x p v ∧ !(T.«Σ₁witness».val) s p”
  )

instance Theory.IsCraigAxiom.defined (T : Theory L) [T.«Σ₁»] :
    𝚫₁-Predicate[V] (T.IsCraigAxiom : V → Prop) via T.craigCh := .mk <| by
  have h (v : Fin 1 → V) :
      (∃ s < v 0, ∃ p < v 0, qqVerums s < v 0 ∧ v 0 = p ^⋏ qqVerums s
        ∧ (Semiformula.Eval ![s, p] Empty.elim) T.«Σ₁witness».val) ↔
        ∃ s p, v 0 = p ^⋏ qqVerums s ∧ (Semiformula.Evalb ![s, p]) T.«Σ₁witness».val := by
    constructor
    . rintro ⟨s, _, p, _, _, h, hT⟩
      exact ⟨s, p, h, hT⟩
    . rintro ⟨s, p, hx, hT⟩
      use s
      and_intros
      . rw [hx]
        exact lt_of_le_of_lt (le_qqVerums s) (lt_K!_right _ _)
      use p
      and_intros
      . rw [hx]
        exact lt_K!_left _ _
      . rw [hx]
        exact lt_K!_right _ _
      . exact hx
      . exact hT
  constructor
  . intro v; simp [Theory.craigCh, h]
  . intro v; simp [Theory.craigCh, Theory.IsCraigAxiom, h]

lemma quote_eq_qqAnd_iff {φ : Proposition L} {p q : ℕ} :
    (⌜φ⌝ : ℕ) = p ^⋏ q ↔ ∃ φ₁ φ₂, φ = φ₁ ⋏ φ₂ ∧ p = ⌜φ₁⌝ ∧ q = ⌜φ₂⌝ := by
  constructor
  . intro h
    cases φ with
    | rel | nrel => simp [qqRel, qqNRel, qqAnd] at h
    | verum =>
      change qqVerum = p ^⋏ q at h;
      simp [qqVerum, qqAnd] at h
    | falsum =>
      change qqFalsum = p ^⋏ q at h;
      simp [qqFalsum, qqAnd] at h
    | or φ₁ φ₂ =>
      change ⌜φ₁⌝ ^⋎ ⌜φ₂⌝ = p ^⋏ q at h;
      simp [qqOr, qqAnd] at h
    | all φ =>
      change ^∀ ⌜φ⌝ = p ^⋏ q at h;
      simp [qqAll, qqAnd] at h
    | exs φ =>
      change ^∃ ⌜φ⌝ = p ^⋏ q at h
      simp [qqExs, qqAnd] at h
    | and φ₁ φ₂ =>
      rcases (qqAnd_inj _ _ _ _).mp h with ⟨rfl, rfl⟩
      exact ⟨φ₁, φ₂, rfl, rfl, rfl⟩
  . rintro ⟨φ₁, φ₂, rfl, rfl, rfl⟩;
    rfl

lemma quote_weight (k : ℕ) :
    (⌜(Semiformula.weight k : Proposition L)⌝ : V) = qqVerums (k : V) := by
  induction k with
  | zero => simp [Semiformula.weight]
  | succ k ih =>
    change ⌜(⊤ : Proposition L) ⋏ Semiformula.weight k⌝ = _
    simp [ih]

lemma quote_eq_qqVerums {χ : Proposition L} {s : ℕ} :
    (⌜χ⌝ : ℕ) = qqVerums (s : ℕ) → χ = Semiformula.weight s := by
  intro h;
  exact (Semiformula.quote_inj_iff (V := ℕ)).mp <| by simpa [quote_weight] using h

lemma quote_padding (φ : Proposition L) (k : ℕ) :
    (⌜φ.padding k⌝ : V) = ⌜φ⌝ ^⋏ qqVerums (k : V) := by
  change ⌜φ ⋏ Semiformula.weight k⌝ = _
  simp [quote_weight]

namespace Sentence

lemma quote_padding (σ : Sentence L) (k : ℕ) :
    (⌜σ.padding k⌝ : V) = ⌜σ⌝ ^⋏ qqVerums (k : V) := by
  simpa [Sentence.quote_def] using
    LO.FirstOrder.Arithmetic.Bootstrapping.quote_padding (V := V) (Rewriting.emb σ) k

end Sentence

lemma Theory.isCraigAxiom_quote_iff {T : Theory L} [T.«Σ₁»] (φ : Proposition L) :
    T.IsCraigAxiom (⌜φ⌝ : ℕ) ↔ ∃ ρ ∈ T.craig, φ = ρ := by
  constructor
  . rintro ⟨s, p, hφ, hT⟩
    rcases quote_eq_qqAnd_iff.mp hφ with ⟨φ₁, φ₂, hφ, hp, hs⟩
    have hφ₂ : φ₂ = Semiformula.weight s := quote_eq_qqVerums hs.symm
    have h₁ : ℕ ⊧/![p] T.«Σ₁ch».val := (Theory.«Σ₁witness_spec» T ℕ ![p]).mpr ⟨s, hT⟩
    rcases (Theory.«Σ₁».mem_iff φ₁).mp (by simpa [hp] using h₁) with ⟨ρ, hρ, hρ'⟩
    use ρ.padding s
    and_intros
    . use ρ, s
      and_intros
      . simpa [hp, hρ', Sentence.quote_def] using hT
      . rfl
    . rw [Semiformula.rew_padding]
      simpa [Semiformula.padding, Semiformula.weight, hρ', hφ₂] using hφ
  . rintro ⟨ρ, ⟨σ, s, hT, rfl⟩, rfl⟩
    use s, ⌜σ⌝
    and_intros
    . simpa [Sentence.quote_def] using Sentence.quote_padding (V := ℕ) σ s
    . exact hT

end LO.FirstOrder.Arithmetic.Bootstrapping

namespace LO.FirstOrder.Theory

open Arithmetic.Bootstrapping

variable {L : Language} [L.Encodable] [L.LORDefinable]

open LO.Entailment

noncomputable instance craig.delta1 (T : Theory L) [T.«Σ₁»] : (T.craig).Δ₁ where
  ch := T.craigCh
  mem_iff φ := (Theory.IsCraigAxiom.defined (V := ℕ) T).iff.trans
    (Theory.isCraigAxiom_quote_iff φ)
  isDelta1 := Arithmetic.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦
    (Theory.IsCraigAxiom.defined (V := V) T).proper

noncomputable instance craig.weakerThan (T : Theory L) [L.DecidableEq] [T.«Σ₁»] : T.craig ⪯ T :=
  WeakerThan.ofAxm! $ by
    rintro σ ⟨ρ, s, hρ, rfl⟩;
    have hρ' : ℕ ⊧/![⌜ρ⌝] T.«Σ₁ch».val := («Σ₁witness_spec» T ℕ ![⌜ρ⌝]).mpr ⟨s, hρ⟩
    rcases («Σ₁».mem_iff (Rewriting.emb ρ)).mp
      (by simpa [Sentence.quote_def] using hρ') with ⟨τ, hτ, hρτ⟩
    have hρT : ρ ∈ T := Rewriting.emb_injective hρτ ▸ hτ
    exact mdp (C_of_E_mpr (Entailment.padding_iff ρ s)) (by_axm hρT)

noncomputable instance craig.original_weakerThan {T : Theory L} [L.DecidableEq] [T.«Σ₁»]
  : T ⪯ T.craig :=
  WeakerThan.ofAxm! fun {σ} hσ ↦ by
    have hσ' : ℕ ⊧/![⌜σ⌝] T.«Σ₁ch».val :=
      («Σ₁».mem_iff (Rewriting.emb σ)).mpr ⟨σ, hσ, rfl⟩
    rcases («Σ₁witness_spec» T ℕ ![⌜σ⌝]).mp hσ' with ⟨s, hs⟩
    have hpadding : σ.padding s ∈ T.craig := ⟨σ, s, hs, rfl⟩
    exact mdp (C_of_E_mp (Entailment.padding_iff σ s)) (by_axm hpadding)

noncomputable instance craig_equiv {T : Theory L} [L.DecidableEq] [T.«Σ₁»]
  : T ≊ T.craig :=
  Equiv.antisymm_iff.mpr ⟨inferInstance, inferInstance⟩

noncomputable instance craig.consistent {T : Theory L} [L.DecidableEq] [T.«Σ₁»] [Consistent T]
  : Consistent T.craig :=
  Consistent.of_le (𝓢 := T) (𝓣 := T.craig) inferInstance inferInstance

end LO.FirstOrder.Theory
