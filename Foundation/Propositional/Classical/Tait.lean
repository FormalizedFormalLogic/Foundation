import Foundation.Propositional.Classical.NNFormula
import Foundation.Propositional.Tait.Calculus

namespace LO.Propositional



variable {α : Type*} {T : Theory α} {Γ : Sequent α}

open Propositional.Classical
namespace Derivation

theorem sound : T ⟹ Γ → T ⊨[Valuation α] Γ.disj := by
  intro d v hv
  induction d
  case axL Γ a =>
    simp [List.map_disj]
    by_cases v a <;> simp [*]
  case verum => simp [List.map_disj]
  case and Γ φ ψ _ _ ihp ihq =>
    by_cases hv : v ⊧ Γ.disj
    · simp [hv]
    · have : v ⊧ φ := by simpa[hv] using ihp
      have : v ⊧ ψ := by simpa[hv] using ihq
      simp [*]
  case or Γ φ ψ d ih =>
    simpa [or_assoc] using ih
  case wk Γ Ξ _ ss ih =>
    have : ∃ φ ∈ Γ, v ⊧ φ := by simpa [List.map_disj] using ih
    rcases this with ⟨φ, hp, hvp⟩
    simp [List.map_disj]; exact ⟨φ, ss hp, hvp⟩
  case cut Γ φ _ _ ihp ihn =>
    by_cases hv : v ⊧ Γ.disj
    · simp [hv]
    · have : v ⊧ φ := by simpa[hv] using ihp
      have : ¬v ⊧ φ := by simpa[hv] using ihn
      contradiction
  case root φ h =>
    have : v ⊧* T := by simpa [Semantics.models] using hv
    simpa using Semantics.realizeSet_iff.mp hv h

theorem sound! : T ⟹! Γ → T ⊨[Valuation α] Γ.disj := fun h ↦ sound h.get

end Derivation

lemma soundness {T : Theory α} {φ} : T ⊢! φ → T ⊨[Valuation α] φ := by
  rintro ⟨b⟩ v hv; simpa using Derivation.sound b hv
namespace Classical
instance (T : Theory α) : Sound T (Semantics.models (Valuation α) T)  := ⟨soundness⟩

section complete

open Classical

def consistentTheory : Set (Theory α) := { U : Theory α | Entailment.Consistent U }

variable {T : Theory α}

open Entailment Derivation

lemma exists_maximal_consistent_theory (consisT : Entailment.Consistent T) :
    ∃ Z, Consistent Z ∧ T ⊆ Z ∧ ∀ U, Consistent U → Z ⊆ U → U = Z :=
  have : ∃ Z : Theory α, T ⊆ Z ∧ Maximal Consistent Z :=
    zorn_subset_nonempty { U : Theory α | Consistent U }
      ( fun c hc chain hnc ↦ ⟨⋃₀ c, by
          haveI : DecidableEq α := Classical.typeDecidableEq α
          by_contra A
          rcases Entailment.inconsistent_compact.mp (Entailment.not_consistent_iff_inconsistent.mp A) with ⟨𝓕, h𝓕, fin, 𝓕_consis⟩
          rcases Set.subset_mem_chain_of_finite c hnc chain (s := 𝓕) fin h𝓕 with ⟨U, hUc, hsU⟩
          have : Consistent U := hc hUc
          have : ¬Consistent U := (𝓕_consis.of_supset hsU).not_con
          contradiction,
        fun s a => Set.subset_sUnion_of_mem a⟩) T consisT
  by rcases this with ⟨Z, ss, con, hZ⟩
     exact ⟨Z, con, ss, by intro U conU ssU; exact Set.Subset.antisymm (hZ conU ssU) ssU⟩

noncomputable def maximalConsistentTheory (consisT : Entailment.Consistent T) : Theory α :=
  Classical.choose (exists_maximal_consistent_theory consisT)

@[simp] lemma maximalConsistentTheory_consistent : Consistent (maximalConsistentTheory consisT) :=
  (Classical.choose_spec (exists_maximal_consistent_theory consisT)).1

@[simp] lemma subset_maximalConsistentTheory {consisT : Entailment.Consistent T} :
    T ⊆ maximalConsistentTheory consisT :=
  (Classical.choose_spec (exists_maximal_consistent_theory consisT)).2.1

lemma maximalConsistentTheory_maximal :
    ∀ U, Consistent U → maximalConsistentTheory consisT ⊆ U → U = maximalConsistentTheory consisT :=
  (Classical.choose_spec (exists_maximal_consistent_theory consisT)).2.2

@[simp] lemma theory_maximalConsistentTheory_eq :
    theory (maximalConsistentTheory consisT) = maximalConsistentTheory consisT :=
  maximalConsistentTheory_maximal (U := theory (maximalConsistentTheory consisT)) (by simp)
    (by simpa using Entailment.Axiomatized.axm_subset (maximalConsistentTheory consisT))

lemma mem_or_neg_mem_maximalConsistentTheory {consisT : Entailment.Consistent T} (φ) :
    φ ∈ maximalConsistentTheory consisT ∨ ∼φ ∈ maximalConsistentTheory consisT := by
  haveI : DecidableEq α := Classical.typeDecidableEq α
  by_contra A
  have hp : φ ∉ maximalConsistentTheory consisT ∧ ∼φ ∉ maximalConsistentTheory consisT := by simpa [not_or] using A
  have : Consistent (insert φ (maximalConsistentTheory consisT)) :=
    Derivation.consistent_iff_unprovable.mpr
      (show ∼φ ∉ theory (maximalConsistentTheory consisT) from by simpa using hp.2)
  have : insert φ (maximalConsistentTheory consisT) ≠ maximalConsistentTheory consisT := by
    simp [hp]
  have : insert φ (maximalConsistentTheory consisT) = maximalConsistentTheory consisT :=
    maximalConsistentTheory_maximal _ (by assumption) (by simp)
  contradiction

lemma mem_maximalConsistentTheory_iff :
    φ ∈ maximalConsistentTheory consisT ↔ maximalConsistentTheory consisT ⊢! φ :=
  ⟨fun h ↦ ⟨Entailment.byAxm h⟩, fun h ↦ by have : φ ∈ theory (maximalConsistentTheory consisT) := h; simpa using this⟩

lemma maximalConsistentTheory_consistent' {φ} :
    φ ∈ maximalConsistentTheory consisT → ∼φ ∉ maximalConsistentTheory consisT := by
  intro h hn
  have : Inconsistent (maximalConsistentTheory consisT) :=
    Entailment.inconsistent_iff_provable_bot.mpr
      (neg_mdp! (mem_maximalConsistentTheory_iff.mp hn) (mem_maximalConsistentTheory_iff.mp h))
  have := this.not_con
  simp_all

lemma not_mem_maximalConsistentTheory_iff :
    φ ∉ maximalConsistentTheory consisT ↔ maximalConsistentTheory consisT ⊢! ∼φ := by
  by_cases hp : φ ∈ maximalConsistentTheory consisT <;> simp [hp]
  · intro bnp
    have : Inconsistent (maximalConsistentTheory consisT) :=
      Entailment.inconsistent_of_provable (neg_mdp! bnp (mem_maximalConsistentTheory_iff.mp hp))
    have := this.not_con
    simp_all
  · exact mem_maximalConsistentTheory_iff.mp
      (by simpa [hp] using mem_or_neg_mem_maximalConsistentTheory (consisT := consisT) φ)

lemma mem_maximalConsistentTheory_and {φ ψ} (h : φ ⋏ ψ ∈ maximalConsistentTheory consisT) :
    φ ∈ maximalConsistentTheory consisT ∧ ψ ∈ maximalConsistentTheory consisT := by
  have : maximalConsistentTheory consisT ⊢! φ ⋏ ψ := mem_maximalConsistentTheory_iff.mp h
  exact ⟨mem_maximalConsistentTheory_iff.mpr (and_left! this),
         mem_maximalConsistentTheory_iff.mpr (and_right! this)⟩

lemma mem_maximalConsistentTheory_or {φ ψ} (h : φ ⋎ ψ ∈ maximalConsistentTheory consisT) :
    φ ∈ maximalConsistentTheory consisT ∨ ψ ∈ maximalConsistentTheory consisT := by
  by_contra A
  have b : maximalConsistentTheory consisT ⊢! ∼φ ∧ maximalConsistentTheory consisT ⊢! ∼ψ := by
    simpa [not_or, not_mem_maximalConsistentTheory_iff] using A
  have : Inconsistent (maximalConsistentTheory consisT) :=
    Entailment.inconsistent_of_provable
      (χ!_of_cφχ!_of_cψχ!_of_aφψ! (nφ!_iff_cφo!.mp b.1) (nφ!_iff_cφo!.mp b.2) (mem_maximalConsistentTheory_iff.mp h))
  have := this.not_con
  simp_all

lemma maximalConsistentTheory_satisfiable :
    Valuation.mk (NNFormula.atom · ∈ maximalConsistentTheory consisT) ⊧* maximalConsistentTheory consisT := ⟨by
  intro φ hp
  induction φ using NNFormula.rec' <;> simp
  case hatom => simpa
  case hnatom =>
    simpa using maximalConsistentTheory_consistent' hp
  case hfalsum =>
    have : Inconsistent (maximalConsistentTheory consisT) := Entailment.inconsistent_of_provable ⟨Entailment.byAxm hp⟩
    have := this.not_con
    simp_all
  case hand φ ψ ihp ihq =>
    exact ⟨ihp (mem_maximalConsistentTheory_and hp).1, ihq (mem_maximalConsistentTheory_and hp).2⟩
  case hor φ ψ ihp ihq =>
    rcases mem_maximalConsistentTheory_or hp with (hp | hq)
    · left; exact ihp hp
    · right; exact ihq hq⟩

lemma satisfiable_of_consistent (consisT : Consistent T) : Semantics.Satisfiable (Valuation α) T :=
  ⟨⟨(NNFormula.atom · ∈ maximalConsistentTheory consisT)⟩,
    Semantics.RealizeSet.of_subset maximalConsistentTheory_satisfiable (by simp)⟩

theorem completeness! : T ⊨[Valuation α] φ → T ⊢! φ := by
  haveI : DecidableEq α := Classical.typeDecidableEq α
  suffices Consistent (insert (∼φ) T) → Semantics.Satisfiable (Valuation α) (insert (∼φ) T) by
    contrapose
    intro hp hs
    have : Semantics.Satisfiable (Valuation α) (insert (∼φ) T) :=
      this (Derivation.consistent_iff_unprovable.mpr $ by simpa)
    rcases this with ⟨v, hv⟩
    have : v ⊧* T := Semantics.RealizeSet.of_subset hv (by simp)
    have : v ⊧ φ := hs this
    have : ¬v ⊧ φ := by
      simpa using hv.realize v (Set.mem_insert (∼φ) T)
    contradiction
  intro consis
  exact satisfiable_of_consistent consis

noncomputable def completeness : T ⊨[Valuation α] φ → T ⊢ φ :=
  fun h ↦ (completeness! h).get

instance (T : Theory α) : Complete T (Semantics.models (Valuation α) T)  where
  complete := completeness!


end complete

end Classical

theorem Derivation.complete : T ⊨[Valuation α] Γ.disj → T ⟹! Γ := fun h ↦
  Tait.derivable_iff_provable_disj.mpr (completeness! h)

theorem Derivation.complete_iff : T ⟹! Γ ↔ T ⊨[Valuation α] Γ.disj := ⟨sound!, complete⟩

theorem Sequent.isTautology_iff : Γ.IsTautology ↔ ∀ v : Classical.Valuation α, ∃ φ ∈ Γ, v ⊧ φ := by
  simp [Sequent.IsTautology, Derivation.complete_iff, Semantics.consequence_iff]

theorem Sequent.notTautology_iff : ¬Γ.IsTautology ↔ ∃ v : Classical.Valuation α, ∀ φ ∈ Γ, ¬v ⊧ φ := by
  simp [Sequent.isTautology_iff]

end Propositional

end LO
