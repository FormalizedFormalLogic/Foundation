import Logic.FirstOrder.Completeness.SearchTree
import Logic.FirstOrder.Completeness.SubLanguage
import Logic.FirstOrder.Ultraproduct

namespace LO

namespace FirstOrder

open Semiformula Completeness

variable {L : Language.{u}} {T : Theory L}

section Encodable

variable [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]  [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)]

noncomputable def Disjconseq.completeness_of_encodable
  {Γ : List (Sentence L)} (h : ∀ M [Nonempty M] [Structure L M], M ⊧ₘ* T → ∃ σ ∈ Γ, M ⊧ₘ σ) :
    T ⊢'' (Γ.map Rew.emb.hom : Sequent L) := by
  have : WellFounded (SearchTree.Lt T (Γ.map Rew.emb.hom : Sequent L)) := by
    by_contra nwf
    have : ∃ σ ∈ Γ, (Model T (Γ.map Rew.emb.hom : Sequent L)) ⊧ₘ σ := h _ (Model.models nwf)
    rcases this with ⟨σ, hσ, h⟩
    have : ¬(Model T (Γ.map Rew.emb.hom : Sequent L)) ⊧ₘ σ := by
      simpa using semanticMainLemmaTop nwf (p := Rew.emb.hom σ) (by simp; exact ⟨σ, hσ, rfl⟩)
    contradiction
  exact syntacticMainLemmaTop this

lemma completeness_of_encodable {σ : Sentence L} :
    T ⊨ σ → T ⊢! σ := fun h ↦ by
  have : T ⊢'' [Rew.emb.hom σ] :=
    Disjconseq.completeness_of_encodable (T := T) (Γ := {σ}) (fun M i s hM ↦ ⟨σ, List.mem_of_mem_head? rfl, h hM⟩)
  exact ⟨toProof this⟩

instance : Complete T (Semantics.models (SmallStruc L) T):= ⟨completeness_of_encodable⟩

end Encodable

theorem complete {σ : Sentence L} :
    T ⊨ σ → T ⊢! σ := fun h ↦ by
  letI := Classical.typeDecidableEq
  have : ∃ u : Finset (Sentence L), ↑u ⊆ insert (~σ) T ∧ ¬Satisfiable (u : Theory L) := by
    simpa using (compact (T := insert (~σ) T)).not.mp (Semantics.consequence_iff_not_satisfiable.mp h)
  choose u hu using this; rcases hu with ⟨ssu, hu⟩
  haveI : ∀ k, Encodable ((languageFinset u).Func k) := fun _ ↦ Fintype.toEncodable _
  haveI : ∀ k, Encodable ((languageFinset u).Rel k) := fun _ ↦ Fintype.toEncodable _
  let u' : Finset (Sentence (languageFinset u)) := Finset.imageOfFinset u (fun _ hσ ↦ toSubLanguageFinsetSelf hσ)
  have image_u' : u'.image (Semiformula.lMap L.ofSubLanguage) = u := by
    ext τ; simp [u', Finset.mem_imageOfFinset_iff]
    exact ⟨by rintro ⟨a, ⟨τ, hτ, rfl⟩, rfl⟩; simp[hτ],
      by intro hτ; exact ⟨toSubLanguageFinsetSelf hτ, ⟨τ, hτ, rfl⟩, Semiformula.lMap_toSubLanguageFinsetSelf hτ⟩⟩
  have : ¬Satisfiable (u' : Theory (languageFinset u)) := by
    intro h
    have : Satisfiable (u : Theory L) := by
      rw[←image_u']
      simpa using (satisfiable_lMap L.ofSubLanguage (fun k ↦ Subtype.val_injective) (fun _ ↦ Subtype.val_injective) h)
    contradiction
  have : System.Inconsistent (u' : Theory (languageFinset u)) := Complete.inconsistent_of_unsatisfiable this
  have : System.Inconsistent (u : Theory L) := by rw[←image_u']; simpa using System.inconsistent_lMap L.ofSubLanguage this
  have : System.Inconsistent (insert (~σ) T) := this.of_supset ssu
  exact Gentzen.provable_iff_inconsistent.mpr this

theorem complete_iff : T ⊨ σ ↔ T ⊢! σ :=
  ⟨fun h ↦ complete h, sound!⟩

instance (T : Theory L) : Complete T (Semantics.models (SmallStruc L) T) := ⟨complete⟩

lemma satisfiable_of_consistent' (h : System.Consistent T) : Semantics.Satisfiable (SmallStruc L) T :=
  Complete.satisfiable_of_consistent h

lemma satisfiable_of_consistent (h : System.Consistent T) : Semantics.Satisfiable (Struc.{max u w} L) T := by
  let ⟨M, _, _, h⟩ := satisfiable_iff.mp (satisfiable_of_consistent' h)
  exact satisfiable_iff.mpr ⟨ULift.{w} M, inferInstance, inferInstance, ((uLift_elementaryEquiv L M).modelsTheory).mpr h⟩

lemma satisfiable_iff_consistent' : Semantics.Satisfiable (Struc.{max u w} L) T ↔ System.Consistent T :=
  ⟨consistent_of_satidfiable, satisfiable_of_consistent.{u, w}⟩

lemma satisfiable_iff_consistent : Satisfiable T ↔ System.Consistent T := satisfiable_iff_consistent'.{u, u}

lemma satidfiable_iff_satisfiable : Semantics.Satisfiable (Struc.{max u w} L) T ↔ Satisfiable T := by
  simp [satisfiable_iff_consistent'.{u, w}, satisfiable_iff_consistent]

lemma consequence_iff_consequence : T ⊨[Struc.{max u w} L] σ ↔ T ⊨ σ := by
  simp [Semantics.consequence_iff_not_satisfiable, satidfiable_iff_satisfiable.{u, w}]

instance (T : Theory L) : Complete T (Semantics.models (Struc.{max u w} L) T) :=
  ⟨fun h ↦ complete <| consequence_iff_consequence.{u, w}.mp h⟩

end FirstOrder
