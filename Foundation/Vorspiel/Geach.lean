import Foundation.Vorspiel.RelItr
import Foundation.Vorspiel.BinaryRelations

structure GeachConfluent.Taple where
  i : ℕ
  j : ℕ
  m : ℕ
  n : ℕ

def GeachConfluent (t : GeachConfluent.Taple) (R : Rel α α) := ∀ {x y z : α}, (R.Iterate t.i x y) ∧ (R.Iterate t.j x z) → ∃ u, (R.Iterate t.m y u) ∧ (R.Iterate t.n z u)


namespace GeachConfluent

variable {rel : Rel α α}

lemma serial_def : Serial rel ↔ (GeachConfluent ⟨0, 0, 1, 1⟩ rel) := by simp [GeachConfluent, Serial];

lemma reflexive_def : Reflexive rel ↔ (GeachConfluent ⟨0, 0, 1, 0⟩ rel) := by simp [GeachConfluent, Reflexive];

lemma symmetric_def : Symmetric rel ↔ (GeachConfluent ⟨0, 1, 0, 1⟩ rel) := by
  simp [GeachConfluent, Symmetric];
  constructor;
  . rintro h x y z rfl Rxz; exact h Rxz;
  . intro h x y Rxy; exact h rfl Rxy;

lemma transitive_def : Transitive rel ↔ (GeachConfluent ⟨0, 2, 1, 0⟩ rel) := by
  simp [GeachConfluent, Transitive];
  constructor;
  . rintro h x y z rfl w Rxw Rwz; exact h Rxw Rwz;
  . intro h x y z Rxy Ryz; exact h rfl y Rxy Ryz

lemma euclidean_def : Euclidean rel ↔ (GeachConfluent ⟨1, 1, 0, 1⟩ rel) := by simp [GeachConfluent, Euclidean];

lemma confluent_def : Confluent rel ↔ (GeachConfluent ⟨1, 1, 1, 1⟩ rel) := by simp [GeachConfluent, Confluent];

lemma extensive_def : Coreflexive rel ↔ (GeachConfluent ⟨0, 1, 0, 0⟩ rel) := by
  simp [GeachConfluent, Coreflexive];
  constructor;
  . rintro h x y z rfl Rxz; have := h Rxz; tauto;
  . intro h x y Rxy; have := h rfl Rxy; tauto;

lemma functional_def : Functional rel ↔ (GeachConfluent ⟨1, 1, 0, 0⟩ rel) := by
  simp [GeachConfluent, Functional];
  constructor <;> tauto;

lemma dense_def : Dense rel ↔ (GeachConfluent ⟨0, 1, 2, 0⟩ rel) := by
  simp [GeachConfluent, Dense];
  constructor;
  . rintro h x y z rfl Rxz; exact h Rxz;
  . intro h x y Rxy; exact h rfl Rxy;

@[simp]
lemma satisfies_eq : GeachConfluent (α := α) t (· = ·) := by simp [GeachConfluent];

end GeachConfluent


def MultiGeachConfluent (ts : List GeachConfluent.Taple) (rel : Rel α α) : Prop :=
  match ts with
  | [] => True
  | [t] => (GeachConfluent t rel)
  | t :: ts => (GeachConfluent t rel) ∧ (MultiGeachConfluent ts rel)

namespace MultiGeachConfluent

variable {rel : Rel α α}

@[simp] lemma iff_nil : MultiGeachConfluent [] rel := by simp [MultiGeachConfluent];

@[simp] lemma iff_singleton : MultiGeachConfluent [t] rel ↔ (GeachConfluent t rel) := by simp [MultiGeachConfluent];

lemma iff_cons (h : ts ≠ []) : MultiGeachConfluent (t :: ts) rel ↔ (GeachConfluent t rel) ∧ (MultiGeachConfluent ts rel) := by simp [MultiGeachConfluent];

@[simp]
lemma satisfies_eq : MultiGeachConfluent (α := α) ts (· = ·) := by induction ts using List.induction_with_singleton <;> simp_all [MultiGeachConfluent];

end MultiGeachConfluent
