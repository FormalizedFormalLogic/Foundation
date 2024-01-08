import Arithmetization.Vorspiel.Vorspiel

namespace LO.FirstOrder

namespace Arith

section definability

variable {M} [Structure ℒₒᵣ M]

protected abbrev Definable (b : VType) (s : ℕ) {k} (t : (Fin k → M) → Prop) : Prop :=
  FirstOrder.Definable (Hierarchy b s : Semisentence ℒₒᵣ k → Prop) t

abbrev DefinablePred (b : VType) (s : ℕ) (P : M → Prop) : Prop :=
  Arith.Definable b s (k := 1) λ v ↦ P (Matrix.vecHead v)

abbrev DefinableRel (b : VType) (s : ℕ) (R : M → M → Prop) : Prop :=
  Arith.Definable b s (k := 2) λ v ↦ R (v 0) (v 1)

abbrev SigmaDefinablePred (s : ℕ) (P : M → Prop) : Prop := DefinablePred Σ s P

notation "Σᴬ[" s "]-Predicate" => SigmaDefinablePred s

abbrev PiDefinablePred (s : ℕ) (t : Set M) : Prop := DefinablePred Π s t

notation "Πᴬ[" s "]-Predicate" => PiDefinablePred s

abbrev SigmaDefinableRel (s : ℕ) (P : M → M → Prop) : Prop := DefinableRel Σ s P

notation "Σᴬ[" s "]-Relation" => SigmaDefinableRel s

abbrev PiDefinableRel (s : ℕ) (t : Set M) : Prop := DefinablePred Π s t

notation "Πᴬ[" s "]-Relation" => PiDefinableRel s

abbrev DefinableFunction (b : VType) (s : ℕ) {k} (f : (Fin k → M) → M) : Prop :=
  FirstOrder.DefinableFunction (Hierarchy b s : Semisentence ℒₒᵣ (k + 1) → Prop) f

abbrev DefinableFunction₁ (b : VType) (s : ℕ) (f : M → M) : Prop :=
  DefinableFunction b s (k := 1) (fun v => f (Matrix.vecHead v))

abbrev DefinableFunction₂ (b : VType) (s : ℕ) (f : M → M → M) : Prop :=
  DefinableFunction b s (k := 2) (fun v => f (v 0) (v 1))

abbrev SigmaDefinableFunction₁ (s : ℕ) (f : M → M) : Prop := DefinableFunction₁ Σ s f

notation "Σᴬ[" s "]-Function₁" => SigmaDefinableFunction₁ s

abbrev PiDefinableFunction₁ (s : ℕ) (f : M → M) : Prop := DefinableFunction₁ Π s f

notation "Πᴬ[" s "]-Function₁" => PiDefinableFunction₁ s

abbrev SigmaDefinableFunction₂ (s : ℕ) (f : M → M → M) : Prop := DefinableFunction₂ Σ s f

notation "Σᴬ[" s "]-Function₂" => SigmaDefinableFunction₂ s

abbrev PiDefinableFunction₂ (s : ℕ) (f : M → M → M) : Prop := DefinableFunction₂ Π s f

notation "Πᴬ[" s "]-Function₂" => PiDefinableFunction₂ s

variable {f : M → M}

end definability

section

variable {M : Type} [LE M] [Structure ℒₒᵣ M]

def PolyBounded {k} (f : (Fin k → M) → M) : Prop :=
  ∃ t : Polynomial k, ∀ v : Fin k → M, f v ≤ t.bVal! M v

abbrev PolyBounded₁ (f : M → M) : Prop :=
  PolyBounded (k := 1) (fun v => f (Matrix.vecHead v))

abbrev PolyBounded₂ (f : M → M → M) : Prop :=
  PolyBounded (k := 2) (fun v => f (v 0) (v 1))

end

end Arith


end LO.FirstOrder
