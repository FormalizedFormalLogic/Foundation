import Logic.Vorspiel.Vorspiel

@[reducible]
class Semantics (F : Type u) [HasLogicSymbols F] where
  struc : Type w → Type v
  realize : {M : Type w} → outParam (struc M) → F →L Prop

namespace Semantics
variable {F : Type u} [HasLogicSymbols F] [s : Semantics.{u, v, w} F]

def realizeTheory {M : Type w} (s : struc F M) (T : Set F) : Prop :=
    ∀ ⦃f⦄, f ∈ T → realize s f

@[reducible] class CStruc (F : Type u) [HasLogicSymbols F] [s : Semantics.{u, v, w} F] (M : Type w) where
  out : s.struc M

lemma CStruc.out_mk (x : s.struc M) : CStruc.out (self := CStruc.mk x) = x := rfl

lemma CStruc.mk_out (x : CStruc F M) : CStruc.mk (CStruc.out (self :=  x)) = x := rfl

instance : Coe (struc F M) (CStruc F M) := ⟨CStruc.mk⟩

def models (M : Type w) [c : CStruc F M] : F →L Prop := realize (CStruc.out : s.struc M)

postfix:max " ⊧ " => models

def modelsTheory (M : Type w) [CStruc F M] (T : Set F) : Prop :=
    ∀ ⦃f⦄, f ∈ T → M ⊧ f

infix:55 " ⊧* " => modelsTheory

def consequence (T : Set F) (f : F) : Prop :=
    ∀ (M : Type w) [Inhabited M] [CStruc F M], M ⊧* T → M ⊧ f

-- note that ⊨ (\vDash) is *NOT* ⊧ (\models)
infix:55 " ⊨ " => consequence

def Valid (f : F) : Prop := ∀ (M : Type w) [Inhabited M] (_ : CStruc F M), M ⊧ f

def Validₛ (T : Set F) : Prop := ∀ (M : Type w) (_ : Inhabited M) (_ : CStruc F M), M ⊧* T

def Satisfiable (f : F) : Prop := ∃ (M : Type w) (_ : Inhabited M) (_ : CStruc F M), M ⊧ f

def Satisfiableₛ (T : Set F) : Prop := ∃ (M : Type w) (_ : Inhabited M) (_ : CStruc F M), M ⊧* T

lemma models_iff_models {M : Type w} [CStruc F M] (f : F) :
    M ⊧ f ↔ realize (CStruc.out : s.struc M) f := of_eq rfl

lemma modelsTheory_def {M : Type w} [CStruc F M] (T : Set F) :
    M ⊧* T ↔ ∀ ⦃f⦄, f ∈ T → realize (CStruc.out : s.struc M) f := of_eq rfl

lemma consequence_iff {T : Set F} {f : F} :
    T ⊨ f ↔ ∀ (M : Type w) [Inhabited M] (s : struc F M), realizeTheory s T → realize s f := by
  simp[consequence, models, modelsTheory]; constructor
  · intro H M i s h; exact @H M i ⟨s⟩ h
  · intro H M i ⟨s⟩ h; exact @H M i s h 

lemma satisfiableₛ_iff {T : Set F} :
    Satisfiableₛ T ↔ ∃ (M : Type w) (_ : Inhabited M) (s : struc F M), realizeTheory s T := by
  simp[Satisfiableₛ, models, modelsTheory]; constructor
  · intro ⟨M, i, ⟨s⟩, h⟩; exact ⟨M, i, s, h⟩
  · intro ⟨M, i, s, h⟩; exact ⟨M, i, ⟨s⟩, h⟩

lemma outid_neg (f : F) : Valid (~f) ↔ ¬Satisfiable f := by simp[Valid, Satisfiable]

lemma modelsTheoryₛ_of_subset {T U : Set F} [CStruc F M] (h : M ⊧* U) (ss : T ⊆ U) : M ⊧* T :=
  fun _ hf => h (ss hf)

lemma satisfiableₛ_intro {T : Set F} (M : Type w) [i : Inhabited M] [s : CStruc F M] (h : M ⊧* T) : Satisfiableₛ T :=
  ⟨M, i, s, h⟩

lemma satisfiableₛ_of_subset {T U : Set F} (h : Satisfiableₛ U) (ss : T ⊆ U) : Satisfiableₛ T :=
  by rcases h with ⟨M, i, s, h⟩; exact ⟨M, i, s, modelsTheoryₛ_of_subset h ss⟩

end Semantics