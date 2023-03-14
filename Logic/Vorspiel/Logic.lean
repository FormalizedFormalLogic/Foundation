import Logic.Vorspiel.Vorspiel

@[reducible]
class Semantics (F : Type u) [HasLogicSymbols F] where
  struc : Type w → Type v
  realize : {M : Type w} → struc M → F →L Prop

namespace Semantics
variable {F : Type u} [HasLogicSymbols F] [s : Semantics.{u, v, w} F]

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

lemma modelsTheoryₛ_of_subset {T U : Set F} {s : struc F M} (h : s ⊧ₛ* U) (ss : T ⊆ U) : s ⊧ₛ* T :=
  fun _ hf => h (ss hf)

lemma satisfiableₛ_of_subset {T U : Set F} (h : Satisfiableₛ U) (ss : T ⊆ U) : Satisfiableₛ T :=
  by rcases h with ⟨M, i, s, h⟩; exact ⟨M, i, s, modelsTheoryₛ_of_subset h ss⟩

end Semantics