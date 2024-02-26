import Logic.AutoProver.Prover
import Logic.Propositional.Basic.Semantics
import Logic.Propositional.Basic.Calculus

namespace LO

namespace Propositional

variable {α : Type*} {Δ : Sequent α}

namespace Sequent

def complexity (Δ : Sequent α) : ℕ := (Δ.map Formula.complexity).sum

end Sequent

namespace Derivation

theorem sound : ⊢¹ Δ → Semantics.Valid Δ.disj := by
  intro d v
  induction d
  case axL Δ a =>
    simp[List.map_disj]
    by_cases v a <;> simp[*]
  case verum => simp[List.map_disj]
  case and Δ p q _ _ ihp ihq =>
    by_cases hv : v ⊧ Δ.disj
    · simp[hv]
    · have : v ⊧ p := by simpa[hv] using ihp
      have : v ⊧ q := by simpa[hv] using ihq
      simp[*]
  case or Δ p q d ih =>
    simpa[or_assoc] using ih
  case wk Δ Γ _ ss ih =>
    have : ∃ p ∈ Δ, v ⊧ p := by simpa [List.map_disj] using ih
    rcases this with ⟨p, hp, hvp⟩
    simp [List.map_disj]; exact ⟨p, ss hp, hvp⟩
  case cut Δ p _ _ ihp ihn =>
    by_cases hv : v ⊧ Δ.disj
    · simp[hv]
    · have : v ⊧ p := by simpa[hv] using ihp
      have : ¬v ⊧ p := by simpa[hv] using ihn
      contradiction

end Derivation


lemma soundness {T : Theory α} {p} : T ⊢ p → T ⊨ p := by
  rintro ⟨Γ, hΓ, d⟩ v hT
  by_contra hv
  have : ∀ v, v ⊧ p ∨ ∃ q ∈ Γ, ¬v ⊧ q := by
    simpa [Semantics.Valid, List.map_disj] using Derivation.sound (Tait.ofConsRight d)
  have : ∃ q ∈ Γ, ¬v ⊧ q := by simpa [hv] using this v
  rcases this with ⟨q, hqΓ, hq⟩
  have : v ⊧ q := hT (hΓ q hqΓ)
  contradiction

instance : Sound (Formula α) := ⟨soundness⟩

section complete

def consistentTheory : Set (Theory α) := { U : Theory α | System.Consistent U }

variable {T : Theory α} (consisT : Consistent T)
open System Gentzen

lemma _root_.Set.subset_mem_chain_of_finite (c : Set (Set α)) (hc : Set.Nonempty c) (hchain : IsChain (· ⊆ ·) c)
    {s} (hfin : Set.Finite s) : s ⊆ ⋃₀ c → ∃ t ∈ c, s ⊆ t :=
  Set.Finite.induction_on hfin
    (by rcases hc with ⟨t, ht⟩; intro; exact ⟨t, ht, by simp⟩)
    (by intro a s _ _ ih h
        have : ∃ t ∈ c, s ⊆ t := ih (subset_trans (Set.subset_insert a s) h)
        rcases this with ⟨t, htc, ht⟩
        have : ∃ u ∈ c, a ∈ u := by simp [Set.insert_subset_iff] at h; exact h.1
        rcases this with ⟨u, huc, hu⟩
        have : ∃ z ∈ c, t ⊆ z ∧ u ⊆ z := IsChain.directedOn hchain t htc u huc
        rcases this with ⟨z, hzc, htz, huz⟩
        exact ⟨z, hzc, Set.insert_subset (huz hu) (Set.Subset.trans ht htz)⟩)

lemma exists_maximal_consistent_theory :
    ∃ T', Consistent T' ∧ T ⊆ T' ∧ ∀ U, Consistent U → T' ⊆ U → U = T' :=
  zorn_subset_nonempty { U : Theory α | Consistent U }
    (fun c hc chain hnc ↦ ⟨⋃₀ c,
     by simp
        by_contra A
        rcases compact_inconsistent A with ⟨s, hs, s_consis⟩
        rcases Set.subset_mem_chain_of_finite c hnc chain (s := s) (Finset.finite_toSet s) hs with ⟨U, hUc, hsU⟩
        have : Consistent (s : Set (Formula α)) := Consistent.of_subset (hc hUc) hsU
        contradiction,
     fun s a => Set.subset_sUnion_of_mem a⟩) T consisT

noncomputable def maximalConsistentTheory : Theory α :=
  Classical.choose (exists_maximal_consistent_theory consisT)

variable {consisT}

@[simp] lemma maximalConsistentTheory_consistent : Consistent (maximalConsistentTheory consisT) :=
  (Classical.choose_spec (exists_maximal_consistent_theory consisT)).1

@[simp] lemma subset_maximalConsistentTheory : T ⊆ maximalConsistentTheory consisT :=
  (Classical.choose_spec (exists_maximal_consistent_theory consisT)).2.1

lemma maximalConsistentTheory_maximal :
    ∀ U, Consistent U → maximalConsistentTheory consisT ⊆ U → U = maximalConsistentTheory consisT :=
  (Classical.choose_spec (exists_maximal_consistent_theory consisT)).2.2

@[simp] lemma theory_maximalConsistentTheory_eq :
    theory (maximalConsistentTheory consisT) = maximalConsistentTheory consisT :=
  maximalConsistentTheory_maximal _ (by simp) (by simp)

lemma mem_or_neg_mem_maximalConsistentTheory (p) :
    p ∈ maximalConsistentTheory consisT ∨ ~p ∈ maximalConsistentTheory consisT := by
  by_contra A
  have hp : p ∉ maximalConsistentTheory consisT ∧ ~p ∉ maximalConsistentTheory consisT := by simpa [not_or] using A
  have : Consistent (insert p (maximalConsistentTheory consisT)) :=
    consistent_insert_iff_not_refutable.mpr
      (unprovable_iff_not_provable.mpr <|
        show ~p ∉ theory (maximalConsistentTheory consisT) from by simp[hp])
  have : insert p (maximalConsistentTheory consisT) ≠ maximalConsistentTheory consisT := by
    simp[hp]
  have : insert p (maximalConsistentTheory consisT) = maximalConsistentTheory consisT :=
    maximalConsistentTheory_maximal _ (by assumption) (by simp)
  contradiction

lemma mem_maximalConsistentTheory_iff :
    p ∈ maximalConsistentTheory consisT ↔ maximalConsistentTheory consisT ⊢! p :=
  ⟨fun h ↦ ⟨axm h⟩, fun h ↦ by have : p ∈ theory (maximalConsistentTheory consisT) := h; simpa using this⟩

lemma maximalConsistentTheory_consistent' {p} :
    p ∈ maximalConsistentTheory consisT → ~p ∉ maximalConsistentTheory consisT := by
  intro h hn
  have : ¬Consistent (maximalConsistentTheory consisT) :=
    inconsistent_of_provable
      (by prover [mem_maximalConsistentTheory_iff.mp h, mem_maximalConsistentTheory_iff.mp hn])
  simp_all

lemma not_mem_maximalConsistentTheory_iff :
    p ∉ maximalConsistentTheory consisT ↔ maximalConsistentTheory consisT ⊢! ~p := by
  by_cases hp : p ∈ maximalConsistentTheory consisT <;> simp[hp]
  · apply unprovable_iff_not_provable.mpr
    intro bnp
    have : ¬Consistent (maximalConsistentTheory consisT) :=
      inconsistent_of_provable (by prover [mem_maximalConsistentTheory_iff.mp hp, bnp])
    simp_all
  · exact mem_maximalConsistentTheory_iff.mp
      (by simpa [hp] using mem_or_neg_mem_maximalConsistentTheory (consisT := consisT) p)

lemma mem_maximalConsistentTheory_and {p q} (h : p ⋏ q ∈ maximalConsistentTheory consisT) :
    p ∈ maximalConsistentTheory consisT ∧ q ∈ maximalConsistentTheory consisT := by
  have : maximalConsistentTheory consisT ⊢! p ⋏ q := mem_maximalConsistentTheory_iff.mp h
  exact ⟨mem_maximalConsistentTheory_iff.mpr (by prover [this]),
         mem_maximalConsistentTheory_iff.mpr (by prover [this])⟩

lemma mem_maximalConsistentTheory_or {p q} (h : p ⋎ q ∈ maximalConsistentTheory consisT) :
    p ∈ maximalConsistentTheory consisT ∨ q ∈ maximalConsistentTheory consisT := by
  by_contra A
  have b : maximalConsistentTheory consisT ⊢! ~p ∧ maximalConsistentTheory consisT ⊢! ~q := by
    simpa [not_or, not_mem_maximalConsistentTheory_iff] using A
  have : ¬Consistent (maximalConsistentTheory consisT) :=
    inconsistent_of_provable (by prover [b.1, b.2, mem_maximalConsistentTheory_iff.mp h])
  simp_all

lemma maximalConsistentTheory_satisfiable :
    (Formula.atom · ∈ maximalConsistentTheory consisT) ⊧* maximalConsistentTheory consisT := by
  intro p hp
  induction p using Formula.rec' <;> simp
  case hatom => simpa
  case hnatom =>
    simpa using maximalConsistentTheory_consistent' hp
  case hfalsum =>
    have : ¬Consistent (maximalConsistentTheory consisT) := inconsistent_of_proof (axm hp)
    simp_all
  case hand p q ihp ihq =>
    exact ⟨ihp (mem_maximalConsistentTheory_and hp).1, ihq (mem_maximalConsistentTheory_and hp).2⟩
  case hor p q ihp ihq =>
    rcases mem_maximalConsistentTheory_or hp with (hp | hq)
    · left; exact ihp hp
    · right; exact ihq hq

lemma satisfiableTheory_of_consistent (consisT : Consistent T) : Semantics.SatisfiableTheory T :=
  ⟨(Formula.atom · ∈ maximalConsistentTheory consisT),
    Semantics.realizeTheory_of_subset maximalConsistentTheory_satisfiable (by simp)⟩

theorem completeness! : T ⊨ p → T ⊢! p := by
  suffices : Consistent (insert (~p) T) → Semantics.SatisfiableTheory (insert (~p) T)
  · contrapose
    simp; intro hp hs
    have : Semantics.SatisfiableTheory (insert (~p) T) :=
      this (consistent_insert_iff_not_refutable.mpr $ by simpa)
    rcases this with ⟨v, hv⟩
    have : v ⊧* T := Semantics.realizeTheory_of_subset hv (by simp)
    have : v ⊧ p := hs this
    have : ¬v ⊧ p := by simpa using hv (Set.mem_insert (~p) T)
    contradiction
  intro consis
  exact satisfiableTheory_of_consistent consis

noncomputable def completeness : T ⊨ p → T ⊢ p :=
  λ h ↦ (completeness! h).toProof

noncomputable instance : Complete (Formula α) where
  complete := completeness

end complete

end Propositional

end LO
