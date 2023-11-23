import Logic.Logic.LogicSymbol

namespace LO

variable {F : Type u} [LogicSymbol F]

class Semantics (F : Type u) [LogicSymbol F] (Struc : outParam (Type w → Type v)) where
  models : {M : Type w} → Struc M → F →L Prop

class Vocabulary (F : Type u) [LogicSymbol F] (V : outParam (Type v)) where
  voc    : F → Set V
  verum  : voc ⊤ = ∅
  falsum : voc ⊥ = ∅
  neg    : (f : F) → voc (~f) = voc f
  and    : (f g : F) → voc (f ⋏ g) = voc f ∪ voc g
  or     : (f g : F) → voc (f ⋎ g) = voc f ∪ voc g
  imp    : (f g : F) → voc (f ⟶ g) = voc f ∪ voc g

class Logic (F : Type u) [LogicSymbol F] (Struc : outParam (Type w → Type v)) (V : outParam (Type v'))
  extends Semantics F Struc, Vocabulary F V

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

lemma weakening {T U : Set F} {f} (h : T ⊨ f) (ss : T ⊆ U) : U ⊨ f :=
  fun M _ s hs => h M s (modelsTheory_of_subset hs ss)

lemma of_mem {T : Set F} {f} (h : f ∈ T) : T ⊨ f := fun _ _ _ hs => hs h

lemma consequence_iff {T : Set F} {f : F} : T ⊨ f ↔ ¬Satisfiableₛ (insert (~f) T) := by
  simp[consequence, Satisfiableₛ]; constructor
  · intro h M hM s hf hT; have : s ⊧ₛ f := h M s hT; contradiction
  · intro h M hM s; contrapose; exact h M hM s

def Subtheory (T U : Set F) : Prop := ∀ {f}, T ⊨ f → U ⊨ f

def Equivalent (T U : Set F) : Prop := {f : F} → T ⊨ f ↔ U ⊨ f

namespace Subtheory

variable (T U T₁ T₂ T₃ : Set F)

@[refl] lemma refl : Subtheory T T := id

@[trans] protected lemma trans (h₁ : Subtheory T₁ T₂) (h₂ : Subtheory T₂ T₃) : Subtheory T₁ T₃ :=
  fun {f} b => h₂ (h₁ b : T₂ ⊨ f)

def ofSubset (h : T ⊆ U) : Subtheory T U := fun b => weakening b h

end Subtheory

lemma modelsTheory_of_subtheory [Inhabited M] {s : Struc M} {T U : Set F} (h : s ⊧ₛ* U) (ss : Subtheory T U) :
    s ⊧ₛ* T :=
  fun _ hf => (ss (of_mem hf)) _ s h

namespace Equivalent

variable (T U T₁ T₂ T₃ : Set F)

@[refl] protected lemma refl : Equivalent T T := ⟨id, id⟩

@[symm] protected lemma symm (h : Equivalent T U) : Equivalent U T := Iff.symm h

@[trans] protected lemma trans (h₁ : Equivalent T₁ T₂) (h₂ : Equivalent T₂ T₃) : Equivalent T₁ T₃ :=
  Iff.trans h₁ h₂

end Equivalent

class Mod {M : Type w} (s : Struc M) (T : Set F) :=
  modelsTheory : s ⊧ₛ* T

namespace Mod

variable (M : Type w) [Inhabited M] (s : Struc M) { T : Set F} [Mod s T]

lemma models {f : F} (hf : f ∈ T) : s ⊧ₛ f :=
  Mod.modelsTheory hf

def of_ss {T₁ T₂ : Set F} [Mod s T₁] (ss : T₂ ⊆ T₁) : Mod s T₂ :=
  ⟨modelsTheory_of_subset modelsTheory ss⟩

def of_subtheory {T₁ T₂ : Set F} [Mod s T₁] (h : Subtheory T₂ T₁) : Mod s T₂ :=
  ⟨modelsTheory_of_subtheory modelsTheory h⟩

end Mod

lemma consequence_iff' {T : Set F} {σ : F} :
    T ⊨ σ ↔ (∀ (M : Type w) [Inhabited M] (s : Struc M) [Mod s T], s ⊧ₛ σ) :=
  ⟨fun h M _ s hM => h M s hM.modelsTheory, fun H M i s hs => @H M i s ⟨hs⟩⟩

end Semantics

variable (F)
variable {Struc : Type w → Type v} [𝓢 : Semantics F Struc]

class Compact where
  compact {T : Set F} : Semantics.Satisfiableₛ T ↔ (∀ u : Finset F, (u : Set F) ⊆ T → Semantics.Satisfiableₛ (u : Set F))

variable {F}

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

end LO
