import Logic.Predicate.FirstOrder.Completeness.SearchTree
import Logic.Predicate.FirstOrder.Ultraproduct

namespace FirstOrder

open SubFormula SearchTree

variable {L : Language.{u}}

attribute [local instance] Classical.decEq

noncomputable def completenessₙ_of_encodable [∀ k, Encodable (L.func k)] [∀ k, Encodable (L.rel k)]
  {Γ : Finset (Sentence L)} (h : ∀ M [Inhabited M] [Structure L M], ∃ σ ∈ Γ, M ⊧₁ σ) :
    ⊢ᵀ (Γ.image emb : Sequent L) := by
  have : WellFounded (SearchTree (Γ.image emb : Sequent L)) := by
    by_contra wf
    have : ∃ σ ∈ Γ, (SearchTree.model (Γ.image emb : Sequent L)) ⊧₁ σ := h _
    rcases this with ⟨σ, hσ, h⟩
    have : ¬(SearchTree.model (Γ.image emb : Sequent L)) ⊧₁ σ := by
      simpa using SearchTree.semanticMainLemma_top wf (p := emb σ) (by simp; exact ⟨σ, hσ, rfl⟩)
    contradiction
  exact SearchTree.syntacticMainLemma_top this

noncomputable def completenessₙ {Γ : Finset (Sentence L)}
  (h : ∀ (M : Type u) (hM : Inhabited M) (s : Structure L M), ∃ σ ∈ Γ, M ⊧₁ σ) :
    ⊢ᵀ (Γ.image emb : Sequent L) := by
  haveI : ∀ k, Encodable ((languageFinset Γ).func k) := fun _ => Fintype.toEncodable _
  haveI : ∀ k, Encodable ((languageFinset Γ).rel k) := fun _ => Fintype.toEncodable _
  have e : ∀ σ (hσ : σ ∈ Γ), L.ofSubLanguage.onSubFormula₁ (toSubLanguageFinsetSelf hσ) = σ := fun σ hσ =>
    ofSubFormula_toSubLanguageFinsetSelf hσ
  let Γ' : Finset (Sentence (languageFinset Γ)) := Finset.imageOfFinset Γ (fun _ hσ => toSubLanguageFinsetSelf hσ)
  have : ∀ (M : Type u) [Inhabited M] [Structure (languageFinset Γ) M], ∃ σ ∈ Γ', M ⊧₁ σ := fun M hM s => by
    have : ∃ σ ∈ Γ, Semantics.realize (self := semantics) (L.ofSubLanguage.extendStructure s) σ :=
      h M hM (L.ofSubLanguage.extendStructure s)
    rcases this with ⟨σ, hσΓ, hσ⟩
    exact ⟨toSubLanguageFinsetSelf hσΓ, by simp,
      (models_extendStructure_onSubFormula₁ (Φ := L.ofSubLanguage)
        (by simp[Function.Injective, Subtype.val_inj]) (by simp[Function.Injective, Subtype.val_inj])
        s (toSubLanguageFinsetSelf hσΓ)).mp
      (by simpa[e] using hσ)⟩
  have : ⊢ᵀ Γ'.image emb := completenessₙ_of_encodable this
  exact (this.lHom₀ L.ofSubLanguage).cast (by
    ext p; simp[Finset.mem_imageOfFinset_iff, onSubFormula₁_emb]; constructor
    · rintro ⟨_, ⟨τ, hτΓ, rfl⟩, rfl⟩; exact ⟨τ, hτΓ, by simp⟩
    · rintro ⟨σ, hσΓ, rfl⟩; exact ⟨toSubLanguageFinsetSelf hσΓ, ⟨σ, hσΓ, rfl⟩, by simp⟩)

noncomputable def completeness {T} {σ : Sentence L} : T ⊨ σ → T ⊢ σ := by
  intro h
  have : ¬Semantics.Satisfiableₛ (insert (~σ) T) := Semantics.consequence_iff.mp h
  have : ∃ T' : Finset (Sentence L), ↑T' ⊆ T ∧ ¬Semantics.Satisfiableₛ (insert (~σ) T' : Theory L) := by
    rw[compactness] at this; simp at this
    rcases this with ⟨T', hT', h⟩
    exact ⟨T' \ {~σ}, by simp[Set.subset_def]; intro τ hτ eτ; simpa[eτ] using hT' hτ, by
      simp; intro h
      have : Semantics.Satisfiableₛ (T' : Theory L) := Semantics.satisfiableₛ_of_subset h (by simp)
      contradiction⟩
  choose s hs using this
  have : ⊢ᵀ (insert σ (s.image HasNeg.neg)).image emb :=
    completenessₙ (Γ := insert σ (s.image HasNeg.neg))
      (fun M hM struc => by
        have := hs.2; simp[Semantics.Satisfiableₛ] at this
        have : Semantics.realize (self := semantics) struc σ ∨
            (∃ x ∈ s, ¬Semantics.realize (self := semantics) struc x) := by
          have := this M hM struc
          simp[Semantics.realizeTheory] at this
          by_cases c : Semantics.realize (self := semantics) struc σ
          · exact Or.inl c
          · exact Or.inr (this c)
        simpa using this)
  exact { leftHand := s.image HasNeg.neg,
          hleftHand := by rw[Finset.coe_image]; exact Set.image_subset _ hs.1,
          derivation := this.cutWeakeningCut }

end FirstOrder

