import Foundation.FirstOrder.Completeness.SearchTree
import Foundation.FirstOrder.Completeness.SubLanguage
import Foundation.FirstOrder.Ultraproduct

namespace LO

namespace FirstOrder

open Semiformula Completeness

variable {L : Language.{u}} {T : Theory L}

section Encodable

variable [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]  [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)]

noncomputable def Derivation.completeness_of_encodable
  {Γ : Sequent L} (h : ∀ M [Nonempty M] [Structure L M], M ⊧ₘ* T → ∃ φ ∈ Γ, M ⊧ₘ φ) : T ⟹ Γ := by
  have : WellFounded (SearchTree.Lt T Γ) := by
    by_contra nwf
    have : ∃ φ ∈ Γ, (Model T Γ) ⊧ₘ φ := h _ (Model.models nwf)
    rcases this with ⟨φ, hp, h⟩
    have : Evalf (Model.structure T Γ) (&·) φ := h (&·)
    have : ¬Evalf (Model.structure T Γ) (&·) φ := by simpa using semanticMainLemmaTop nwf (φ := φ) hp
    contradiction
  exact syntacticMainLemmaTop this

lemma completeness_of_encodable {φ : SyntacticFormula L} :
    T ⊨ φ → T ⊢! φ := fun h ↦
  ⟨Derivation.completeness_of_encodable (T := T) (Γ := [φ]) (fun _ _ _ hM ↦ ⟨φ, List.mem_of_mem_head? rfl, h hM⟩)⟩

instance : Complete T (Semantics.models (SmallStruc L) T):= ⟨completeness_of_encodable⟩

end Encodable

open Classical

theorem complete {φ : SyntacticFormula L} :
    T ⊨ φ → T ⊢! φ := fun h ↦ by
  have : ∃ u : Finset (SyntacticFormula L), ↑u ⊆ insert (∼∀∀φ) T ∧ ¬Satisfiable (u : Theory L) := by
    simpa using compact.not.mp (consequence_iff_unsatisfiable.mp h)
  rcases this with ⟨u, ssu, hu⟩
  haveI : ∀ k, Encodable ((languageFinset u).Func k) := fun _ ↦ Fintype.toEncodable _
  haveI : ∀ k, Encodable ((languageFinset u).Rel k) := fun _ ↦ Fintype.toEncodable _
  let u' : Finset (SyntacticFormula (languageFinset u)) := Finset.imageOfFinset u (fun _ hp ↦ toSubLanguageFinsetSelf hp)
  have image_u' : u'.image (Semiformula.lMap L.ofSubLanguage) = u := by
    ext τ; simp [u', Finset.mem_imageOfFinset_iff]
    exact ⟨by rintro ⟨a, ⟨τ, hτ, rfl⟩, rfl⟩; simp [hτ],
      by intro hτ; exact ⟨toSubLanguageFinsetSelf hτ, ⟨τ, hτ, rfl⟩, Semiformula.lMap_toSubLanguageFinsetSelf hτ⟩⟩
  have : ¬Satisfiable (u' : Theory (languageFinset u)) := by
    intro h
    have : Satisfiable (u : Theory L) := by
      rw [←image_u']
      simpa using (satisfiable_lMap L.ofSubLanguage (fun k ↦ Subtype.val_injective) (fun _ ↦ Subtype.val_injective) h)
    contradiction
  have : Entailment.Inconsistent (u' : Theory (languageFinset u)) := Complete.inconsistent_of_unsatisfiable this
  have : Entailment.Inconsistent (u : Theory L) := by rw [←image_u']; simpa using Derivation.inconsistent_lMap L.ofSubLanguage this
  have : Entailment.Inconsistent (insert (∼∀∀φ) T) := this.of_supset ssu
  exact Derivation.provable_iff_inconsistent.mpr this

theorem complete_iff : T ⊨ φ ↔ T ⊢! φ :=
  ⟨fun h ↦ complete h, sound!⟩

instance (T : Theory L) : Complete T (Semantics.models (SmallStruc L) T) := ⟨complete⟩

lemma satisfiable_of_consistent' (h : Entailment.Consistent T) : Semantics.Satisfiable (SmallStruc L) T :=
  Complete.satisfiable_of_consistent h

lemma satisfiable_of_consistent (h : Entailment.Consistent T) : Semantics.Satisfiable (Struc.{max u w} L) T := by
  let ⟨M, _, _, h⟩ := satisfiable_iff.mp (satisfiable_of_consistent' h)
  exact satisfiable_iff.mpr ⟨ULift.{w} M, inferInstance, inferInstance, ((uLift_elementaryEquiv L M).modelsTheory).mpr h⟩

lemma satisfiable_iff_consistent' : Semantics.Satisfiable (Struc.{max u w} L) T ↔ Entailment.Consistent T :=
  ⟨consistent_of_satidfiable, satisfiable_of_consistent.{u, w}⟩

lemma satisfiable_iff_consistent : Satisfiable T ↔ Entailment.Consistent T := satisfiable_iff_consistent'.{u, u}

lemma satidfiable_iff_satisfiable : Semantics.Satisfiable (Struc.{max u w} L) T ↔ Satisfiable T := by
  simp [satisfiable_iff_consistent'.{u, w}, satisfiable_iff_consistent]

lemma consequence_iff_consequence : T ⊨[Struc.{max u w} L] φ ↔ T ⊨ φ := by
  simp [consequence_iff_unsatisfiable, satidfiable_iff_satisfiable.{u, w}]

theorem complete' {φ : SyntacticFormula L} :
    T ⊨[Struc.{max u w} L] φ → T ⊢! φ := fun h ↦ complete <| consequence_iff_consequence.{u, w}.mp h

instance (T : Theory L) : Complete T (Semantics.models (Struc.{max u w} L) T) := ⟨complete'.{u, w}⟩

end FirstOrder
