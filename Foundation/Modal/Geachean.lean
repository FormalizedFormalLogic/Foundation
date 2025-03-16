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


class IsGeachean (g : Geachean.Taple) (α) (R : Rel α α) where
  geachean : ∀ {x y z : α}, (R.iterate g.i x y) ∧ (R.iterate g.j x z) → ∃ u, (R.iterate g.m y u) ∧ (R.iterate g.n z u)

section

variable {R : Rel α α}

instance [IsGeachean ⟨0, 2, 1, 0⟩ _ R] : IsTrans _ R := ⟨by
  intro a b c Rab Rac;
  apply @Geachean.transitive_def α R |>.mpr IsGeachean.geachean Rab Rac;
⟩
instance [IsTrans _ R] : IsGeachean ⟨0, 2, 1, 0⟩ _ R := ⟨by
  apply @Geachean.transitive_def α R |>.mp;
  exact IsTrans.trans;
⟩


instance [IsGeachean ⟨0, 0, 1, 0⟩ _ R] : IsRefl _ R := ⟨by
  intro a;
  apply @Geachean.reflexive_def α R |>.mpr IsGeachean.geachean;
⟩

instance [IsRefl _ R] : IsGeachean ⟨0, 0, 1, 0⟩ _ R := ⟨by
  apply @Geachean.reflexive_def α R |>.mp;
  exact IsRefl.refl;
⟩


instance [IsGeachean ⟨0, 1, 0, 1⟩ _ R] : IsSymm _ R := ⟨by
  intro a b Rab;
  apply @Geachean.symmetric_def α R |>.mpr IsGeachean.geachean;
  exact Rab;
⟩

instance [IsSymm _ R] : IsGeachean ⟨0, 1, 0, 1⟩ _ R := ⟨by
  apply @Geachean.symmetric_def α R |>.mp;
  exact IsSymm.symm;
⟩


instance [IsGeachean ⟨0, 0, 1, 1⟩ _ R] : IsSerial _ R := ⟨by
  intro a;
  apply @Geachean.serial_def α R |>.mpr IsGeachean.geachean;
⟩

instance [IsSerial _ R] : IsGeachean ⟨0, 0, 1, 1⟩ _ R := ⟨by
  apply @Geachean.serial_def α R |>.mp;
  exact IsSerial.serial;
⟩


instance [IsGeachean ⟨1, 1, 0, 1⟩ _ R] : IsEuclidean _ R := ⟨by
  intro a b c Rab Rac;
  apply @Geachean.euclidean_def α R |>.mpr IsGeachean.geachean Rab Rac;
⟩

instance [IsEuclidean _ R] : IsGeachean ⟨1, 1, 0, 1⟩ _ R := ⟨by
  apply @Geachean.euclidean_def α R |>.mp;
  exact IsEuclidean.eucl;
⟩


instance [IsGeachean ⟨1, 1, 1, 1⟩ _ R] : IsConfluent _ R := ⟨by
  rintro a b c ⟨Rab, Rba⟩;
  apply @Geachean.confluent_def α R |>.mpr IsGeachean.geachean;
  exact ⟨Rab, Rba⟩;
⟩

instance [IsConfluent _ R] : IsGeachean ⟨1, 1, 1, 1⟩ _ R := ⟨by
  apply @Geachean.confluent_def α R |>.mp;
  exact IsConfluent.confl;
⟩


instance [IsGeachean ⟨0, 1, 0, 0⟩ _ R] : IsCoreflexive _ R := ⟨by
  intro a b Rab;
  apply @Geachean.coreflexive_def α R |>.mpr IsGeachean.geachean;
  exact Rab;
⟩

instance [IsCoreflexive _ R] : IsGeachean ⟨0, 1, 0, 0⟩ _ R := ⟨by
  apply @Geachean.coreflexive_def α R |>.mp;
  exact IsCoreflexive.corefl;
⟩

end


def MultiGeachean (G : Set Geachean.Taple) (R : Rel α α) := ∀ g ∈ G, Geachean g R
