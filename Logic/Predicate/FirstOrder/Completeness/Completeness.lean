import Logic.Predicate.FirstOrder.Completeness.SearchTree

namespace FirstOrder

open SubFormula

variable {L : Language.{u}}

attribute [local instance] Classical.decEq

noncomputable def completenessₙ_of_encodable [∀ k, Encodable (L.func k)] [∀ k, Encodable (L.rel k)]
  {σ : Sentence L} (h : Semantics.Valid σ) :
    Derivation.Valid σ := by
  have : WellFounded (SearchTree {emb σ}) := by
    by_contra wf
    have : ¬Val (SearchTree.model {emb σ}) Empty.elim σ := by
      simpa using SearchTree.semanticMainLemma_top wf (p := emb σ) (by simp)
    have : Val (SearchTree.model {emb σ}) Empty.elim σ := h (SearchTree.model {emb σ})
    contradiction
  exact SearchTree.syntacticMainLemma_top this

noncomputable def completenessₙ {σ : Sentence L} (h : Semantics.Valid σ) :
    Derivation.Valid σ := by
  haveI : ∀ k, Encodable (σ.language.func k) := fun _ => Fintype.toEncodable _
  haveI : ∀ k, Encodable (σ.language.rel k) := fun _ => Fintype.toEncodable _
  have e : L.ofSubLanguage.onSubFormula₁ σ.toSubLanguageSelf = σ := ofSubFormula_toSubLanguageSelf σ 
  have : Semantics.Valid σ.toSubLanguageSelf :=
    SubFormula.valid_extendStructure_onSubFormula₁ (Φ := L.ofSubLanguage)
      (by simp[Function.Injective, Subtype.val_inj]) (by simp[Function.Injective, Subtype.val_inj])
      (by rw[←e] at h; exact h)
  have : Derivation.Valid σ.toSubLanguageSelf := completenessₙ_of_encodable this
  simpa[e] using Derivation.onValid L.ofSubLanguage this


end FirstOrder

