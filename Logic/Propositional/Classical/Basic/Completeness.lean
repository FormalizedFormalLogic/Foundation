import Logic.AutoProver.Prover
import Logic.Propositional.Classical.Basic.Semantics
import Logic.Propositional.Classical.Basic.Calculus

namespace LO

namespace Propositional.Classical

variable {α : Type*} {Δ : Sequent α}

namespace Derivation

theorem sound : ⊢¹ Δ → Semantics.Valid (Valuation α) Δ.disj := by
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

lemma soundness {T : Theory (Formula α)} {p} : T ⊢! p → T ⊨[Valuation α] p := by
  rintro ⟨Γ, hΓ, d⟩ v hT
  by_contra hv
  have : ∀ v, v ⊧ p ∨ ∃ q ∈ Γ, ¬v ⊧ q := by
    simpa [Semantics.Valid, List.map_disj] using Derivation.sound (Tait.ofConsRight d)
  have : ∃ q ∈ Γ, ¬v ⊧ q := by simpa [hv] using this v
  rcases this with ⟨q, hqΓ, hq⟩
  have : v ⊧ q := hT.realize (hΓ q hqΓ)
  contradiction

instance (T : Theory (Formula α)) : Sound T (Semantics.models (Valuation α) T.set)  := ⟨soundness⟩

section complete

def consistentTheory : Set (Theory (Formula α)) := { U : Theory (Formula α) | System.Consistent U }

variable {T : Theory (Formula α)} (consisT : Consistent T)
open System Gentzen

lemma exists_maximal_consistent_theory :
    ∃ Z, Consistent Z ∧ T ⊆ Z ∧ ∀ U, Consistent U → Z ⊆ U → U = Z :=
  have : ∃ Z : Set (Formula α), Consistent Z.theory ∧ T.set ⊆ Z ∧ ∀ U : Set (Formula α), Consistent U.theory → Z ⊆ U → U = Z :=
    zorn_subset_nonempty { U : Set (Formula α) | Consistent U.theory }
      (fun c hc chain hnc ↦ ⟨⋃₀ c,
       by simp
          by_contra A
          rcases System.inconsistent_compact.mp (System.not_consistent_iff_inconsistent.mp A) with ⟨𝓕, h𝓕, fin, 𝓕_consis⟩
          rcases Set.subset_mem_chain_of_finite c hnc chain (s := 𝓕) fin h𝓕 with ⟨U, hUc, hsU⟩
          have : Consistent U.theory := hc hUc
          have : ¬Consistent U.theory := (𝓕_consis.of_supset hsU).not_con
          contradiction,
       fun s a => Set.subset_sUnion_of_mem a⟩) T consisT
  by rcases this with ⟨Z, con, ss, hZ⟩
     exact ⟨Z, con, ss, by intro U conU ssU; apply Theory.setext; simpa using hZ U conU ssU⟩

noncomputable def maximalConsistentTheory : Theory (Formula α) :=
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
    Set.theory (theory (maximalConsistentTheory consisT)) = maximalConsistentTheory consisT :=
  maximalConsistentTheory_maximal (U := Set.theory <| theory (maximalConsistentTheory consisT)) (by simp)
    (by simpa [Theory.subset_def] using System.Axiomatized.axm_subset (maximalConsistentTheory consisT))

@[simp] lemma theory_maximalConsistentTheory_eq' :
    theory (maximalConsistentTheory consisT) = maximalConsistentTheory consisT :=
  congr_arg Theory.set <| theory_maximalConsistentTheory_eq (consisT := consisT)

lemma mem_or_neg_mem_maximalConsistentTheory (p) :
    p ∈ maximalConsistentTheory consisT ∨ ~p ∈ maximalConsistentTheory consisT := by
  by_contra A
  have hp : p ∉ maximalConsistentTheory consisT ∧ ~p ∉ maximalConsistentTheory consisT := by simpa [not_or] using A
  have : Consistent (insert p (maximalConsistentTheory consisT)) :=
    consistent_insert_iff_not_refutable.mpr
      (show ~p ∉ theory (maximalConsistentTheory consisT) from by simpa using hp.2)
  have : insert p (maximalConsistentTheory consisT) ≠ maximalConsistentTheory consisT := by
    simp [hp, Theory.setext_iff]
  have : insert p (maximalConsistentTheory consisT) = maximalConsistentTheory consisT :=
    maximalConsistentTheory_maximal _ (by assumption) (by simp)
  contradiction

lemma mem_maximalConsistentTheory_iff :
    p ∈ maximalConsistentTheory consisT ↔ maximalConsistentTheory consisT ⊢! p :=
  ⟨fun h ↦ ⟨System.Axiomatized.prfAxm _ h⟩, fun h ↦ by have : p ∈ theory (maximalConsistentTheory consisT) := h; simpa using this⟩

lemma maximalConsistentTheory_consistent' {p} :
    p ∈ maximalConsistentTheory consisT → ~p ∉ maximalConsistentTheory consisT := by
  intro h hn
  have : Inconsistent (maximalConsistentTheory consisT) :=
    System.inconsistent_iff_provable_bot.mpr
      (by prover [mem_maximalConsistentTheory_iff.mp h, mem_maximalConsistentTheory_iff.mp hn])
  have := this.not_con
  simp_all

lemma not_mem_maximalConsistentTheory_iff :
    p ∉ maximalConsistentTheory consisT ↔ maximalConsistentTheory consisT ⊢! ~p := by
  by_cases hp : p ∈ maximalConsistentTheory consisT <;> simp[hp]
  · intro bnp
    have : Inconsistent (maximalConsistentTheory consisT) :=
      System.inconsistent_of_provable (by prover [mem_maximalConsistentTheory_iff.mp hp, bnp])
    have := this.not_con
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
  have : Inconsistent (maximalConsistentTheory consisT) :=
    System.inconsistent_of_provable (by prover [b.1, b.2, mem_maximalConsistentTheory_iff.mp h])
  have := this.not_con
  simp_all

lemma maximalConsistentTheory_satisfiable :
    (⟨(Formula.atom · ∈ maximalConsistentTheory consisT)⟩ : Valuation α) ⊧* maximalConsistentTheory consisT := ⟨by
  intro p hp
  induction p using Formula.rec' <;> simp
  case hatom => simpa
  case hnatom =>
    simpa using maximalConsistentTheory_consistent' hp
  case hfalsum =>
    have : Inconsistent (maximalConsistentTheory consisT) := System.inconsistent_of_provable ⟨System.Axiomatized.prfAxm _ hp⟩
    have := this.not_con
    simp_all
  case hand p q ihp ihq =>
    exact ⟨ihp (mem_maximalConsistentTheory_and hp).1, ihq (mem_maximalConsistentTheory_and hp).2⟩
  case hor p q ihp ihq =>
    rcases mem_maximalConsistentTheory_or hp with (hp | hq)
    · left; exact ihp hp
    · right; exact ihq hq⟩

lemma satisfiableTheory_of_consistent (consisT : Consistent T) : Semantics.Satisfiable (Valuation α) T :=
  ⟨⟨(Formula.atom · ∈ maximalConsistentTheory consisT)⟩,
    Semantics.RealizeSet.of_subset maximalConsistentTheory_satisfiable (by simp [←Theory.subset_def])⟩

theorem completeness! : T ⊨[Valuation α] p → T ⊢! p := by
  suffices Consistent (insert (~p) T) → Semantics.Satisfiable (Valuation α) (insert (~p) T) by
    contrapose
    intro hp hs
    have : Semantics.Satisfiable (Valuation α) (insert (~p) T) :=
      this (consistent_insert_iff_not_refutable.mpr $ by simpa)
    rcases this with ⟨v, hv⟩
    have : v ⊧* T := Semantics.RealizeSet.of_subset hv (by simp)
    have : v ⊧ p := hs _ this
    have : ¬v ⊧ p := by simpa using hv.realize (Set.mem_insert (~p) T)
    contradiction
  intro consis
  exact satisfiableTheory_of_consistent consis

noncomputable def completeness : T ⊨[Valuation α] p → T ⊢ p :=
  λ h ↦ (completeness! h).prf

instance (T : Theory (Formula α)) : Complete T (Semantics.models (Valuation α) T.set)  where
  complete := completeness!

end complete

end Propositional.Classical

end LO
