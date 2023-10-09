import Logic.Predicate.FirstOrder.Completeness.SearchTree
import Logic.Predicate.FirstOrder.Completeness.SubLanguage
import Logic.Predicate.FirstOrder.Ultraproduct

namespace LO

namespace FirstOrder

open Logic Subformula Completeness

variable {L : Language.{u}} {T : Theory L}

attribute [local instance] Classical.decEq

section Encodable

variable [∀ k, Encodable (L.func k)] [∀ k, Encodable (L.rel k)]

noncomputable def DerivationWA.completeness_of_encodable
  {Γ : Finset (Sentence L)} (h : ∀ M [Inhabited M] [Structure L M], M ⊧* T → ∃ σ ∈ Γ, M ⊧ σ) :
    T ⊢ᵀ (Γ.image Rew.embl : Sequent L) := by
  have : WellFounded (SearchTree.Lt T (Γ.image Rew.embl : Sequent L)) := by
    by_contra nwf
    have : ∃ σ ∈ Γ, (Model T (Γ.image Rew.embl : Sequent L)) ⊧ σ := h _ (Model.models nwf)
    rcases this with ⟨σ, hσ, h⟩
    have : ¬(Model T (Γ.image Rew.embl : Sequent L)) ⊧ σ := by
      simpa using semanticMainLemmaTop nwf (p := Rew.embl σ) (by simp; exact ⟨σ, hσ, rfl⟩)
    contradiction
  exact syntacticMainLemmaTop this

noncomputable def completeness_of_encodable {σ : Sentence L} :
    T ⊨ σ → T ⊢ σ := fun h => by
  have : T ⊢ᵀ {Rew.embl σ} := DerivationWA.completeness_of_encodable (T := T) (Γ := {σ}) (fun M i s hM => ⟨σ, by simp, h M s hM⟩)
  exact this.toProof
  
noncomputable instance : Logic.Complete (Sentence L) := ⟨completeness_of_encodable⟩

end Encodable

noncomputable def completeness {σ : Sentence L} :
    T ⊨ σ → T ⊢ σ := fun h => by
  have : ∃ u : Finset (Sentence L), ↑u ⊆ insert (~σ) T ∧ ¬Semantics.Satisfiableₛ (u : Theory L) := by
    simpa[Compact.compact (T := insert (~σ) T)] using Semantics.consequence_iff.mp h
  choose u hu using this; rcases hu with ⟨ssu, hu⟩
  haveI : ∀ k, Encodable ((languageFinset u).func k) := fun _ => Fintype.toEncodable _
  haveI : ∀ k, Encodable ((languageFinset u).rel k) := fun _ => Fintype.toEncodable _
  let u' : Finset (Sentence (languageFinset u)) := Finset.imageOfFinset u (fun _ hσ => toSubLanguageFinsetSelf hσ)
  have image_u' : u'.image (Subformula.lMap L.ofSubLanguage) = u := by
    { ext τ; simp[Finset.mem_imageOfFinset_iff]
      exact ⟨by rintro ⟨a, ⟨τ, hτ, rfl⟩, rfl⟩; simp[hτ],
        by intro hτ; exact ⟨toSubLanguageFinsetSelf hτ, ⟨τ, hτ, rfl⟩, Subformula.lMap_toSubLanguageFinsetSelf hτ⟩⟩ }
  have : ¬Semantics.Satisfiableₛ (u' : Theory (languageFinset u))
  { intro h
    have : Semantics.Satisfiableₛ (u : Theory L) := by
      rw[←image_u']; simpa using (satisfiableₛ_lMap L.ofSubLanguage (fun k => Subtype.val_injective) (fun _ => Subtype.val_injective) h)
    contradiction }
  have : ¬Proof.Consistent (u' : Theory (languageFinset u)) := fun h => this (Logic.Complete.satisfiableₛ_iff_consistent.mpr h)
  have : ¬Proof.Consistent (u : Theory L) := by rw[←image_u']; simpa using inConsistent_lMap L.ofSubLanguage this
  have : ¬Proof.Consistent (insert (~σ) T) := fun h => this (h.of_subset ssu)
  have : Nonempty (T ⊢ σ) := provable_iff_inConsistent.mpr this
  choose b _ using exists_true_iff_nonempty.mpr this
  exact b

noncomputable instance : Logic.Complete (Sentence L) := ⟨completeness⟩

end FirstOrder

