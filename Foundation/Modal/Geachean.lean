import Foundation.Vorspiel.RelItr
import Foundation.Vorspiel.BinaryRelations

structure Geachean.Taple where
  i : ℕ
  j : ℕ
  m : ℕ
  n : ℕ

def Geachean (t : Geachean.Taple) (R : Rel α α) := ∀ {x y z : α}, (R.iterate t.i x y) ∧ (R.iterate t.j x z) → ∃ u, (R.iterate t.m y u) ∧ (R.iterate t.n z u)


namespace Geachean

variable {rel : Rel α α}

lemma serial_def : Serial rel ↔ (Geachean ⟨0, 0, 1, 1⟩ rel) := by simp [Geachean, Serial];

lemma reflexive_def : Reflexive rel ↔ (Geachean ⟨0, 0, 1, 0⟩ rel) := by simp [Geachean, Reflexive];

lemma symmetric_def : Symmetric rel ↔ (Geachean ⟨0, 1, 0, 1⟩ rel) := by
  simp [Geachean, Symmetric];
  constructor;
  . rintro h x y z rfl Rxz; exact h Rxz;
  . intro h x y Rxy; exact h rfl Rxy;

lemma transitive_def : Transitive rel ↔ (Geachean ⟨0, 2, 1, 0⟩ rel) := by
  simp [Geachean, Transitive];
  constructor;
  . rintro h x y z rfl w Rxw Rwz; exact h Rxw Rwz;
  . intro h x y z Rxy Ryz; exact h rfl y Rxy Ryz

lemma euclidean_def : Euclidean rel ↔ (Geachean ⟨1, 1, 0, 1⟩ rel) := by simp [Geachean, Euclidean];

lemma confluent_def : Confluent rel ↔ (Geachean ⟨1, 1, 1, 1⟩ rel) := by simp [Geachean, Confluent];

lemma coreflexive_def : Coreflexive rel ↔ (Geachean ⟨0, 1, 0, 0⟩ rel) := by
  simp [Geachean, Coreflexive];
  constructor;
  . rintro h x y z rfl Rxz; have := h Rxz; tauto;
  . intro h x y Rxy; have := h rfl Rxy; tauto;

lemma functional_def : Functional rel ↔ (Geachean ⟨1, 1, 0, 0⟩ rel) := by
  simp [Geachean, Functional];
  constructor <;> tauto;

lemma dense_def : Dense rel ↔ (Geachean ⟨0, 1, 2, 0⟩ rel) := by
  simp [Geachean, Dense];
  constructor;
  . rintro h x y z rfl Rxz; exact h Rxz;
  . intro h x y Rxy; exact h rfl Rxy;

@[simp]
lemma satisfies_eq : Geachean (α := α) t (· = ·) := by simp [Geachean];

end Geachean


def MultiGeachean (G : Set Geachean.Taple) (R : Rel α α) := ∀ g ∈ G, Geachean g R
