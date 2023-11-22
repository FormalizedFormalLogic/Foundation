import Logic.Logic.Semantics

namespace LO

variable {F : Type u} [LogicSymbol F]

/- Deduction System of F -/

class System (F : Type u) [LogicSymbol F] where
  Bew : Set F → F → Type u
  axm : ∀ {f}, f ∈ T → Bew T f
  weakening' : ∀ {T U f}, T ⊆ U → Bew T f → Bew U f

namespace System
variable [𝓑 : System F]

instance : HasTurnstile F (Type u) := ⟨𝓑.Bew⟩

def BewTheory (T U : Set F) : Type u := {f : F} → f ∈ U → T ⊢ f

infix:45 " ⊢* " => System.BewTheory

def BewTheoryEmpty (T : Set F) : T ⊢* ∅ := fun h => by contradiction

def BewTheory.ofSubset {T U : Set F} (h : U ⊆ T) : T ⊢* U := fun hf => axm (h hf)

def BewTheory.refl (T : Set F) : T ⊢* T := axm

def Consistent (T : Set F) : Prop := IsEmpty (T ⊢ ⊥)

lemma weakening {T U : Set F} {f : F} (b : T ⊢ f) (ss : T ⊆ U) : U ⊢ f := weakening' ss b

lemma Consistent.of_subset {T U : Set F} (h : Consistent U) (ss : T ⊆ U) : Consistent T := ⟨fun b => h.false (weakening b ss)⟩

lemma inConsistent_of_proof {T : Set F} (b : T ⊢ ⊥) : ¬Consistent T := by simp[Consistent]; exact ⟨b⟩

abbrev Provable (T : Set F) (f : F) : Prop := Nonempty (T ⊢ f)

infix:45 " ⊢! " => System.Provable

def Complete (T : Set F) : Prop := ∀ f, (T ⊢! f) ∨ (T ⊢! ~f)

def Independent (T : Set F) (f : F) : Prop := ¬T ⊢! f ∧ ¬T ⊢! ~f

lemma incomplete_iff_exists_independent {T : Set F} :
    ¬Complete T ↔ ∃ f, Independent T f := by simp[Complete, not_or, Independent]

end System

def System.hom [System F] {G : Type u} [LogicSymbol G] (F : G →L F) : System G where
  Bew := fun T g => F '' T ⊢ F g
  axm := fun h => System.axm (Set.mem_image_of_mem F h)
  weakening' := fun h => by simp; exact System.weakening' (Set.image_subset F h)

variable (F)
variable [LogicSymbol F] [𝓑 : System F] {Struc : Type w → Type v} [𝓢 : Semantics F Struc]

class Sound where
  sound : ∀ {T : Set F} {p : F}, T ⊢ p → T ⊨ p

class SoundOn (M : Type w) (s : Struc M) (H : Set F) where
  sound : ∀ {T : Set F} {p : F}, p ∈ H → T ⊢ p → s ⊧ₛ p

class Complete extends Sound F where
  complete : ∀ {T : Set F} {p : F}, T ⊨ p → T ⊢ p

variable {F}

namespace Sound

variable [Sound F]
variable {M : Type w} [Inhabited M] {s : Struc M}

lemma not_provable_of_countermodel {T : Set F} {p : F}
  (hT : s ⊧ₛ* T) (hp : ¬s ⊧ₛ p) : IsEmpty (T ⊢ p) :=
  ⟨fun b => by have : s ⊧ₛ p := Sound.sound b M s hT; contradiction⟩

lemma consistent_of_model {T : Set F}
  (hT : s ⊧ₛ* T) : System.Consistent T :=
  not_provable_of_countermodel (p := ⊥) hT (by simp)

lemma consistent_of_satisfiable {T : Set F} : Semantics.Satisfiableₛ T → System.Consistent T := by
  rintro ⟨M, _, s, h⟩; exact consistent_of_model h

lemma models_of_proof {T : Set F} {f} (h : s ⊧ₛ* T) (b : T ⊢ f) : s ⊧ₛ f :=
  Sound.sound b M s h

lemma modelsTheory_of_proofTheory {T U : Set F} (h : s ⊧ₛ* T) (b : T ⊢* U) : s ⊧ₛ* U :=
  fun _ hf => models_of_proof h (b hf)

end Sound

namespace Complete

variable [Complete F]

lemma satisfiableₛ_iff_consistent {T : Set F} : Semantics.Satisfiableₛ T ↔ System.Consistent T :=
  ⟨Sound.consistent_of_satisfiable,
   by contrapose; intro h
      have : T ⊨ ⊥
      { intro M i s hM; have : Semantics.Satisfiableₛ T := ⟨M, i, s, hM⟩; contradiction }
      have : T ⊢ ⊥ := complete this
      exact System.inConsistent_of_proof this⟩

lemma not_satisfiable_iff_inconsistent {T : Set F} : ¬Semantics.Satisfiableₛ T ↔ T ⊢! ⊥ := by
  simp[satisfiableₛ_iff_consistent, System.Consistent]

lemma consequence_iff_provable {T : Set F} {f : F} : T ⊨ f ↔ T ⊢! f :=
⟨fun h => ⟨complete h⟩, by rintro ⟨b⟩; exact Sound.sound b⟩

end Complete

end LO
