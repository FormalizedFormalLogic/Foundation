import Logic.Vorspiel.Vorspiel

class Semantics (F : Type u) [HasLogicSymbols F] where
  struc : Type w → Type v
  models : {M : Type w} → struc M → F →L Prop

namespace Semantics
variable {F : Type u} [HasLogicSymbols F] [s : Semantics.{u, v, w} F]
   
postfix:max " ⊧ₛ " => models

def modelsTheory {M : Type w} (s : struc F M) (T : Set F) : Prop :=
    ∀ ⦃f⦄, f ∈ T → s ⊧ₛ f

infix:55 " ⊧ₛ* " => modelsTheory

class CStruc (F : Type u) [HasLogicSymbols F] [s : Semantics.{u, v, w} F] (M : Type w) where
  val : s.struc M

instance : Coe (struc F M) (CStruc F M) := ⟨CStruc.mk⟩

def cmodels (M : Type w) [CStruc F M] : F →L Prop := models (CStruc.val : s.struc M)

postfix:max " ⊧ " => cmodels

def cmodelsTheory (M : Type w) [CStruc F M] (T : Set F) : Prop :=
    ∀ ⦃f⦄, f ∈ T → M ⊧ f

infix:55 " ⊧* " => cmodelsTheory

def consequence (T : Set F) (f : F) : Prop :=
    ∀ (M : Type w) [Inhabited M] [CStruc F M], M ⊧* T → M ⊧ f

-- note that ⊨ (\vDash) is *NOT* ⊧ (\models)
infix:55 " ⊨ " => consequence

def Valid (f : F) : Prop := ∀ (M : Type w) [Inhabited M] (_ : CStruc F M), M ⊧ f

def Validₛ (T : Set F) : Prop := ∀ (M : Type w) (_ : Inhabited M) (_ : CStruc F M), M ⊧* T

def Satisfiable (f : F) : Prop := ∃ (M : Type w) (_ : Inhabited M) (_ : CStruc F M), M ⊧ f

def Satisfiableₛ (T : Set F) : Prop := ∃ (M : Type w) (_ : Inhabited M) (_ : CStruc F M), M ⊧* T

lemma cmodels_iff_models {M : Type w} [CStruc F M] (f : F) :
    M ⊧ f ↔ (CStruc.val : s.struc M) ⊧ₛ f := of_eq rfl

lemma cmodelsTheory_def {M : Type w} [CStruc F M] (T : Set F) :
    M ⊧* T ↔ ∀ ⦃f⦄, f ∈ T → (CStruc.val : s.struc M) ⊧ₛ f := of_eq rfl

lemma consequence_iff {T : Set F} {f : F} :
    T ⊨ f ↔ ∀ (M : Type w) [Inhabited M] (s : struc F M), s ⊧ₛ* T → s ⊧ₛ f := by
  simp[consequence, cmodels, cmodelsTheory]; constructor
  · intro H M i s h; exact @H M i ⟨s⟩ h
  · intro H M i ⟨s⟩ h; exact @H M i s h 

lemma satisfiableₛ_iff {T : Set F} :
    Satisfiableₛ T ↔ ∃ (M : Type w) (_ : Inhabited M) (s : struc F M), s ⊧ₛ* T := by
  simp[Satisfiableₛ, cmodels, cmodelsTheory]; constructor
  · intro ⟨M, i, ⟨s⟩, h⟩; exact ⟨M, i, s, h⟩
  · intro ⟨M, i, s, h⟩; exact ⟨M, i, ⟨s⟩, h⟩

lemma valid_neg (f : F) : Valid (~f) ↔ ¬Satisfiable f := by simp[Valid, Satisfiable]

lemma cmodelsTheoryₛ_of_subset {T U : Set F} [CStruc F M] (h : M ⊧* U) (ss : T ⊆ U) : M ⊧* T :=
  fun _ hf => h (ss hf)

lemma satisfiableₛ_intro {T : Set F} (M : Type w) [i : Inhabited M] [s : CStruc F M] (h : M ⊧* T) : Satisfiableₛ T :=
  ⟨M, i, s, h⟩

lemma satisfiableₛ_of_subset {T U : Set F} (h : Satisfiableₛ U) (ss : T ⊆ U) : Satisfiableₛ T :=
  by rcases h with ⟨M, i, s, h⟩; exact ⟨M, i, s, cmodelsTheoryₛ_of_subset h ss⟩

end Semantics