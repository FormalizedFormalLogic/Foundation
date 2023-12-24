import Logic.FirstOrder.Completeness.SearchTree
import Logic.FirstOrder.Completeness.SubLanguage
import Logic.FirstOrder.Ultraproduct

namespace LO

namespace FirstOrder

open Semiformula Completeness

variable {L : Language} {T : Theory L}

section Encodable

variable [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]  [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)]

noncomputable def DerivationWA.completeness_of_encodable
  {Γ : List (Sentence L)} (h : ∀ M [Inhabited M] [Structure L M], M ⊧* T → ∃ σ ∈ Γ, M ⊧ σ) :
    T ⊢'' (Γ.map Rew.emb.hom : Sequent L) := by
  have : WellFounded (SearchTree.Lt T (Γ.map Rew.emb.hom : Sequent L)) := by
    by_contra nwf
    have : ∃ σ ∈ Γ, (Model T (Γ.map Rew.emb.hom : Sequent L)) ⊧ σ := h _ (Model.models nwf)
    rcases this with ⟨σ, hσ, h⟩
    have : ¬(Model T (Γ.map Rew.emb.hom : Sequent L)) ⊧ σ := by
      simpa using semanticMainLemmaTop nwf (p := Rew.emb.hom σ) (by simp; exact ⟨σ, hσ, rfl⟩)
    contradiction
  exact syntacticMainLemmaTop this

noncomputable def completeness_of_encodable {σ : Sentence L} :
    T ⊨ σ → T ⊢ σ := fun h ↦ by
  have : T ⊢'' [Rew.emb.hom σ] :=
    DerivationWA.completeness_of_encodable (T := T) (Γ := {σ}) (fun M i s hM ↦ ⟨σ, List.mem_of_mem_head? rfl, h M s hM⟩)
  exact toProof this

noncomputable instance : Complete (Sentence L) := ⟨completeness_of_encodable⟩

end Encodable

noncomputable def completeness {σ : Sentence L} :
    T ⊨ σ → T ⊢ σ := fun h ↦ by
  letI := Classical.typeDecidableEq
  have : ∃ u : Finset (Sentence L), ↑u ⊆ insert (~σ) T ∧ ¬Semantics.Satisfiableₛ (u : Theory L) := by
    simpa[Compact.compact (T := insert (~σ) T)] using Semantics.consequence_iff.mp h
  choose u hu using this; rcases hu with ⟨ssu, hu⟩
  haveI : ∀ k, Encodable ((languageFinset u).Func k) := fun _ ↦ Fintype.toEncodable _
  haveI : ∀ k, Encodable ((languageFinset u).Rel k) := fun _ ↦ Fintype.toEncodable _
  let u' : Finset (Sentence (languageFinset u)) := Finset.imageOfFinset u (fun _ hσ ↦ toSubLanguageFinsetSelf hσ)
  have image_u' : u'.image (Semiformula.lMap L.ofSubLanguage) = u := by
    { ext τ; simp[Finset.mem_imageOfFinset_iff]
      exact ⟨by rintro ⟨a, ⟨τ, hτ, rfl⟩, rfl⟩; simp[hτ],
        by intro hτ; exact ⟨toSubLanguageFinsetSelf hτ, ⟨τ, hτ, rfl⟩, Semiformula.lMap_toSubLanguageFinsetSelf hτ⟩⟩ }
  have : ¬Semantics.Satisfiableₛ (u' : Theory (languageFinset u))
  { intro h
    have : Semantics.Satisfiableₛ (u : Theory L) := by
      rw[←image_u']; simpa using (satisfiableₛ_lMap L.ofSubLanguage (fun k ↦ Subtype.val_injective) (fun _ ↦ Subtype.val_injective) h)
    contradiction }
  have : ¬System.Consistent (u' : Theory (languageFinset u)) := fun h ↦ this (Complete.satisfiableₛ_iff_consistent.mpr h)
  have : ¬System.Consistent (u : Theory L) := by rw[←image_u']; simpa using System.inconsistent_lMap L.ofSubLanguage this
  have : ¬System.Consistent (insert (~σ) T) := fun h ↦ this (h.of_subset ssu)
  have : Nonempty (T ⊢ σ) := Gentzen.provable_iff_inconsistent.mpr this
  choose b _ using exists_true_iff_nonempty.mpr this
  exact b

theorem completeness_iff : T ⊨ σ ↔ T ⊢! σ :=
  ⟨fun h ↦ ⟨completeness h⟩, soundness'⟩

noncomputable instance completeness.sentence : Complete (Sentence L) := ⟨completeness⟩

end FirstOrder
