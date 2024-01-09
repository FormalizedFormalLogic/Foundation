import Arithmetization.Vorspiel.Vorspiel

namespace LO.FirstOrder

def Defined {k} (R : (Fin k → M) → Prop) [Structure L M] (p : LO.FirstOrder.Semisentence L k) : Prop :=
  ∀ v, R v ↔ Semiformula.PVal! M v p

namespace Defined

variable [Structure L M]

lemma pval {k} {R : (Fin k → M) → Prop} {p : LO.FirstOrder.Semisentence L k} (h : Defined R p) (v) :
    Semiformula.PVal! M v p ↔ R v := (h v).symm

end Defined

namespace Arith

section definability

variable {M} [Structure ℒₒᵣ M]

abbrev FormulaHierarchy (b : VType) (s : ℕ) (L : Language) [L.LT] (n) :=
  { p : Semisentence L n // Hierarchy b s p }

abbrev SigmaFormula (s : ℕ) (L : Language) [L.LT] (n) := FormulaHierarchy Σ s L n

abbrev PiFormula (s : ℕ) (L : Language) [L.LT] (n) := FormulaHierarchy Π s L n

notation "Σᴬ[" s "]" => SigmaFormula s ℒₒᵣ

notation "Πᴬ[" s "]" => PiFormula s ℒₒᵣ

namespace FormulaHierarchy

variable (b : VType) (s : ℕ) (L : Language) [L.LT] (n)

@[simp] lemma hierarchy (p : FormulaHierarchy b s L n) : Hierarchy b s p.val := p.prop

@[simp] lemma hierarchy_zero (p : FormulaHierarchy b 0 L n) : Hierarchy b' s p.val :=
  Hierarchy.of_zero p.hierarchy

end FormulaHierarchy

protected abbrev Defined (b s) {k} (R : (Fin k → M) → Prop) (p : FormulaHierarchy b s ℒₒᵣ k) : Prop :=
  Defined R p.val

abbrev DefinedPred (b : VType) (s : ℕ) (P : M → Prop) (p : FormulaHierarchy b s ℒₒᵣ 1) : Prop :=
  Arith.Defined b s (λ v ↦ P (v 0)) p

abbrev DefinedRel (b : VType) (s : ℕ) (R : M → M → Prop) (p : FormulaHierarchy b s ℒₒᵣ 2) : Prop :=
  Arith.Defined b s (λ v ↦ R (v 0) (v 1)) p

abbrev SigmaDefinedPred (s : ℕ) (P : M → Prop) (p : Σᴬ[s] 1) : Prop := DefinedPred Σ s P p

notation "Σᴬ[" s "]-Predicate" => SigmaDefinedPred s

abbrev PiDefinedPred (s : ℕ) (t : Set M) (p : Πᴬ[s] 1) : Prop := DefinedPred Π s t p

notation "Πᴬ[" s "]-Predicate" => PiDefinedPred s

abbrev SigmaDefinedRel (s : ℕ) (R : M → M → Prop) (p : Σᴬ[s] 2) : Prop := DefinedRel Σ s R p

notation "Σᴬ[" s "]-Relation" => SigmaDefinedRel s

abbrev PiDefinedRel (s : ℕ) (R : M → M → Prop) (p : Πᴬ[s] 2) : Prop := DefinedRel Π s R p

notation "Πᴬ[" s "]-Relation" => PiDefinedRel s

abbrev DefinedFunction (b : VType) (s : ℕ) {k} (f : (Fin k → M) → M) (p : FormulaHierarchy b s ℒₒᵣ (k + 1)) : Prop :=
  Arith.Defined b s (fun v => v 0 = f (v ·.succ)) p

abbrev DefinedFunction₁ (b : VType) (s : ℕ) (f : M → M) (p : FormulaHierarchy b s ℒₒᵣ 2) : Prop :=
  DefinedFunction b s (fun v => f (v 0)) p

abbrev DefinedFunction₂ (b : VType) (s : ℕ) (f : M → M → M) (p : FormulaHierarchy b s ℒₒᵣ 3) : Prop :=
  DefinedFunction b s (fun v => f (v 0) (v 1)) p

abbrev SigmaDefinedFunction₁ (s : ℕ) (f : M → M) (p : Σᴬ[s] 2) : Prop := DefinedFunction₁ Σ s f p

notation "Σᴬ[" s "]-Function₁" => SigmaDefinedFunction₁ s

abbrev PiDefinedFunction₁ (s : ℕ) (f : M → M) (p : Πᴬ[s] 2) : Prop := DefinedFunction₁ Π s f p

notation "Πᴬ[" s "]-Function₁" => PiDefinedFunction₁ s

abbrev SigmaDefinedFunction₂ (s : ℕ) (f : M → M → M) (p : Σᴬ[s] 3) : Prop := DefinedFunction₂ Σ s f p

notation "Σᴬ[" s "]-Function₂" => SigmaDefinedFunction₂ s

abbrev PiDefinedFunction₂ (s : ℕ) (f : M → M → M) (p : Πᴬ[s] 3) : Prop := DefinedFunction₂ Π s f p

notation "Πᴬ[" s "]-Function₂" => PiDefinedFunction₂ s

variable {f : M → M}

end definability

section

variable {M : Type} [LE M] [Structure ℒₒᵣ M]

def PolyBounded {k} (f : (Fin k → M) → M) (t : Polynomial k) : Prop :=
  ∀ v : Fin k → M, f v ≤ t.bVal! M v

abbrev PolyBounded₁ (f : M → M) (t : Polynomial 1) : Prop :=
  PolyBounded (k := 1) (fun v => f (Matrix.vecHead v)) t

abbrev PolyBounded₂ (f : M → M → M) (t : Polynomial 2) : Prop :=
  PolyBounded (k := 2) (fun v => f (v 0) (v 1)) t

end

end Arith


end LO.FirstOrder
