import Logic.Vorspiel.Vorspiel

namespace Logic

variable (F : Type u) [HasLogicSymbols F]

/- Deduction System of F -/

class Calculus (F : Type u) [HasLogicSymbols F] where
  Bew : Set F → F → Type u
  axm : ∀ {T f}, f ∈ T → Bew T f

variable {F}

namespace Calculus
variable [𝓑 : Calculus F]

instance : HasTurnstile F (Type u) := ⟨𝓑.Bew⟩

def BewTheory (T U : Set F) : Type u := {f : F} → f ∈ U → T ⊢ f

infix:45 " ⊢* " => Calculus.BewTheory

def BewTheoryEmpty (T : Set F) : T ⊢* ∅ := fun h => by contradiction

def BewTheory.ofSubset {T U : Set F} (h : U ⊆ T) : T ⊢* U := fun hf => axm (h hf)

def BewTheory.refl (T : Set F) : T ⊢* T := axm

def IsConsistent (T : Set F) : Prop := IsEmpty (T ⊢ ⊥)

end Calculus

def Calculus.hom [Calculus F] {G : Type u} [HasLogicSymbols G] (F : G →L F) : Calculus G where
  Bew := fun T g => F '' T ⊢ F g
  axm := fun h => Calculus.axm (Set.mem_image_of_mem F h)

/- Semantics of F -/

class Semantics (F : Type u) [HasLogicSymbols F] where
  struc : Type w → Type v
  realize : {M : Type w} → struc M → F →L Prop

namespace Semantics
variable [𝓢 : Semantics.{u, v, w} F]

def realizeTheory {M : Type w} (s : struc F M) (T : Set F) : Prop :=
    ∀ ⦃f⦄, f ∈ T → realize s f

postfix:max " ⊧ₛ " => realize

infix:55 " ⊧ₛ* " => realizeTheory

def consequence (T : Set F) (f : F) : Prop :=
    ∀ (M : Type w) [Inhabited M] (s : struc F M), s ⊧ₛ* T → s ⊧ₛ f

-- note that ⊨ (\vDash) is *NOT* ⊧ (\models)
infix:55 " ⊨ " => consequence

def Valid (f : F) : Prop := ∀ ⦃M : Type w⦄ [Inhabited M] (s : struc F M), s ⊧ₛ f

def Validₛ (T : Set F) : Prop := ∀ ⦃M : Type w⦄ [Inhabited M] (s : struc F M), s ⊧ₛ* T

def Satisfiable (f : F) : Prop := ∃ (M : Type w) (_ : Inhabited M) (s : struc F M), s ⊧ₛ f

def Satisfiableₛ (T : Set F) : Prop := ∃ (M : Type w) (_ : Inhabited M) (s : struc F M), s ⊧ₛ* T

lemma valid_neg_iff (f : F) : Valid (~f) ↔ ¬Satisfiable f := by simp[Valid, Satisfiable]

lemma not_satisfiable_finset [DecidableEq F] (t : Finset F) :
    ¬Satisfiableₛ (t : Set F) ↔ Valid (t.image HasNeg.neg).disj :=
  by simp[Satisfiableₛ, realizeTheory, Valid, Finset.map_disj]

lemma realizeTheory_of_subset {T U : Set F} {s : struc F M} (h : s ⊧ₛ* U) (ss : T ⊆ U) : s ⊧ₛ* T :=
  fun _ hf => h (ss hf)

@[simp] lemma realizeTheoryEmpty {s : struc F M} : s ⊧ₛ* ∅ := fun p => by simp

@[simp] lemma realizeTheory_insert {T : Set F} {f : F} {s : struc F M} :
    s ⊧ₛ* insert f T ↔ s ⊧ₛ f ∧ s ⊧ₛ* T := by
  simp[realizeTheory]

@[simp] lemma realizeTheory_union {T U : Set F} {s : struc F M} :
    s ⊧ₛ* T ∪ U ↔ s ⊧ₛ* T ∧ s ⊧ₛ* U := by
  simp[realizeTheory]
  exact
  ⟨fun h => ⟨fun f hf => h (Or.inl hf), fun f hf => h (Or.inr hf)⟩,
   by rintro ⟨h₁, h₂⟩ f (h | h); exact h₁ h; exact h₂ h⟩

@[simp] lemma realizeTheory_image {f : α → F} {A : Set α} {s : struc F M} :
    s ⊧ₛ* f '' A ↔ ∀ i ∈ A, s ⊧ₛ (f i) := by simp[realizeTheory]

@[simp] lemma realizeTheory_range {f : α → F} {s : struc F M} :
    s ⊧ₛ* Set.range f ↔ ∀ i, s ⊧ₛ (f i) := by simp[realizeTheory]

lemma satisfiableₛ_of_subset {T U : Set F} (h : Satisfiableₛ U) (ss : T ⊆ U) : Satisfiableₛ T :=
  by rcases h with ⟨M, i, s, h⟩; exact ⟨M, i, s, realizeTheory_of_subset h ss⟩

lemma consequence_iff {T : Set F} {f : F} : T ⊨ f ↔ ¬Satisfiableₛ (insert (~f) T) := by
  simp[consequence, Satisfiableₛ]; constructor
  · intro h M hM s hf hT; have : s ⊧ₛ f := h M s hT; contradiction
  · intro h M hM s; contrapose; exact h M hM s

end Semantics

variable (F)
variable [HasLogicSymbols F] [𝓑 : Calculus F] [𝓢 : Semantics.{u, v, w} F]

class Sound where
  sound : ∀ {T : Set F} {p : F}, T ⊢ p → T ⊨ p

class Complete extends Sound F where
  complete : ∀ {T : Set F} {p : F}, T ⊨ p → T ⊢ p

variable {F}

namespace Sound
variable [Sound F]
variable {M : Type w} [Inhabited M] {s : Semantics.struc F M}

lemma not_provable_of_countermodel {T : Set F} {p : F}
  (hT : s ⊧ₛ* T) (hp : ¬s ⊧ₛ p) : IsEmpty (T ⊢ p) :=
  ⟨fun b => by have : s ⊧ₛ p := Sound.sound b M s hT; contradiction⟩

lemma consistent_of_model {T : Set F}
  (hT : s ⊧ₛ* T) : Calculus.IsConsistent T :=
  not_provable_of_countermodel (p := ⊥) hT (by simp)

lemma realize_of_proof {T : Set F} {f} (h : s ⊧ₛ* T) (b : T ⊢ f) : s ⊧ₛ f :=
  Sound.sound b M s h

lemma realizeTheory_of_proofTheory {T U : Set F} (h : s ⊧ₛ* T) (b : T ⊢* U) : s ⊧ₛ* U :=
  fun _ hf => realize_of_proof h (b hf)

end Sound

end Logic
