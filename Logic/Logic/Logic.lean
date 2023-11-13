import Logic.Logic.LogicSymbol

namespace LO

namespace Logic

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

end System

def System.hom [System F] {G : Type u} [LogicSymbol G] (F : G →L F) : System G where
  Bew := fun T g => F '' T ⊢ F g
  axm := fun h => System.axm (Set.mem_image_of_mem F h)
  weakening' := fun h => by simp; exact System.weakening' (Set.image_subset F h)

/- Semantics of F -/

class Semantics (F : Type u) [LogicSymbol F] (Struc : outParam (Type w → Type v)) where
  models : {M : Type w} → Struc M → F →L Prop

namespace Semantics
variable {Struc : Type w → Type v} [𝓢 : Semantics F Struc]

def modelsTheory {M : Type w} (s : Struc M) (T : Set F) : Prop :=
    ∀ ⦃f⦄, f ∈ T → models s f

postfix:max " ⊧ₛ " => models

infix:55 " ⊧ₛ* " => modelsTheory

def consequence (T : Set F) (f : F) : Prop :=
    ∀ (M : Type w) [Inhabited M] (s : Struc M), s ⊧ₛ* T → s ⊧ₛ f

-- note that ⊨ (\vDash) is *NOT* ⊧ (\models)
infix:55 " ⊨ " => consequence

def Valid (f : F) : Prop := ∀ ⦃M : Type w⦄ [Inhabited M] (s : Struc M), s ⊧ₛ f

def Validₛ (T : Set F) : Prop := ∀ ⦃M : Type w⦄ [Inhabited M] (s : Struc M), s ⊧ₛ* T

def Satisfiable (f : F) : Prop := ∃ (M : Type w) (_ : Inhabited M) (s : Struc M), s ⊧ₛ f

def Satisfiableₛ (T : Set F) : Prop := ∃ (M : Type w) (_ : Inhabited M) (s : Struc M), s ⊧ₛ* T

lemma valid_neg_iff (f : F) : Valid (~f) ↔ ¬Satisfiable f := by simp[Valid, Satisfiable]

lemma not_satisfiable_finset [DecidableEq F] (t : Finset F) :
    ¬Satisfiableₛ (t : Set F) ↔ Valid (t.image (~·)).disj :=
  by simp[Satisfiableₛ, modelsTheory, Valid, Finset.map_disj]

lemma modelsTheory_of_subset {T U : Set F} {s : Struc M} (h : s ⊧ₛ* U) (ss : T ⊆ U) : s ⊧ₛ* T :=
  fun _ hf => h (ss hf)

@[simp] lemma modelsTheoryEmpty {s : Struc M} : s ⊧ₛ* (∅ : Set F) := fun p => by simp

@[simp] lemma modelsTheory_insert {T : Set F} {f : F} {s : Struc M} :
    s ⊧ₛ* insert f T ↔ s ⊧ₛ f ∧ s ⊧ₛ* T := by
  simp[modelsTheory]

@[simp] lemma modelsTheory_union {T U : Set F} {s : Struc M} :
    s ⊧ₛ* T ∪ U ↔ s ⊧ₛ* T ∧ s ⊧ₛ* U := by
  simp[modelsTheory]
  exact
  ⟨fun h => ⟨fun f hf => h (Or.inl hf), fun f hf => h (Or.inr hf)⟩,
   by rintro ⟨h₁, h₂⟩ f (h | h); exact h₁ h; exact h₂ h⟩

@[simp] lemma modelsTheory_image {f : α → F} {A : Set α} {s : Struc M} :
    s ⊧ₛ* f '' A ↔ ∀ i ∈ A, s ⊧ₛ (f i) := by simp[modelsTheory]

@[simp] lemma modelsTheory_range {f : α → F} {s : Struc M} :
    s ⊧ₛ* Set.range f ↔ ∀ i, s ⊧ₛ (f i) := by simp[modelsTheory]

lemma satisfiableₛ_of_subset {T U : Set F} (h : Satisfiableₛ U) (ss : T ⊆ U) : Satisfiableₛ T :=
  by rcases h with ⟨M, i, s, h⟩; exact ⟨M, i, s, modelsTheory_of_subset h ss⟩

lemma consequence_iff {T : Set F} {f : F} : T ⊨ f ↔ ¬Satisfiableₛ (insert (~f) T) := by
  simp[consequence, Satisfiableₛ]; constructor
  · intro h M hM s hf hT; have : s ⊧ₛ f := h M s hT; contradiction
  · intro h M hM s; contrapose; exact h M hM s

end Semantics

variable (F)
variable [LogicSymbol F] [𝓑 : System F] {Struc : Type w → Type v} [𝓢 : Semantics F Struc]

class Sound where
  sound : ∀ {T : Set F} {p : F}, T ⊢ p → T ⊨ p

class SoundOn (M : Type w) (s : Struc M) (H : Set F) where
  sound : ∀ {T : Set F} {p : F}, p ∈ H → T ⊢ p → s ⊧ₛ p

class Compact where
  compact {T : Set F} : Semantics.Satisfiableₛ T ↔ (∀ u : Finset F, (u : Set F) ⊆ T → Semantics.Satisfiableₛ (u : Set F))

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

namespace Compact

variable [Compact F]
variable {M : Type w} [Inhabited M] {s : Struc M}

lemma conseq_compact [DecidableEq F] {f : F} :
    T ⊨ f ↔ ∃ u : Finset F, ↑u ⊆ T ∧ u ⊨ f := by
  simp[Semantics.consequence_iff, compact (T := insert (~f) T)]
  constructor
  · intro ⟨u, ss, hu⟩; exact ⟨Finset.erase u (~f), by simp[ss], by { simp; intro h; exact hu (Semantics.satisfiableₛ_of_subset h (by simp)) }⟩
  · intro ⟨u, ss, hu⟩; exact ⟨insert (~f) u, by simpa using Set.insert_subset_insert ss, by simpa using hu⟩

end Compact

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

end Logic

end LO
