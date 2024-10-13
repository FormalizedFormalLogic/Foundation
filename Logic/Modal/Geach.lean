import Logic.Modal.Hilbert
import Logic.Logic.Kripke.RelItr
import Logic.Vorspiel.BinaryRelations

structure GeachTaple where
  i : ℕ
  j : ℕ
  m : ℕ
  n : ℕ

def GeachConfluent (t : GeachTaple) (R : Rel α α) := ∀ {x y z : α}, (R.iterate t.i x y) ∧ (R.iterate t.j x z) → ∃ u, (R.iterate t.m y u) ∧ (R.iterate t.n z u)

namespace GeachConfluent

variable {R : Rel α α}

lemma serial_def : Serial R ↔ (GeachConfluent ⟨0, 0, 1, 1⟩ R) := by simp [GeachConfluent, Serial];

lemma reflexive_def : Reflexive R ↔ (GeachConfluent ⟨0, 0, 1, 0⟩ R) := by simp [GeachConfluent, Reflexive];

lemma symmetric_def : Symmetric R ↔ (GeachConfluent ⟨0, 1, 0, 1⟩ R) := by
  simp [GeachConfluent, Symmetric];
  constructor;
  . rintro h x y z rfl Rxz; exact h Rxz;
  . intro h x y Rxy; exact h rfl Rxy;

lemma transitive_def : Transitive R ↔ (GeachConfluent ⟨0, 2, 1, 0⟩ R) := by
  simp [GeachConfluent, Transitive];
  constructor;
  . rintro h x y z rfl w Rxw Rwz; exact h Rxw Rwz;
  . intro h x y z Rxy Ryz; exact h rfl y Rxy Ryz

lemma euclidean_def : Euclidean R ↔ (GeachConfluent ⟨1, 1, 0, 1⟩ R) := by simp [GeachConfluent, Euclidean];

lemma confluent_def : Confluent R ↔ (GeachConfluent ⟨1, 1, 1, 1⟩ R) := by simp [GeachConfluent, Confluent];

lemma extensive_def : Extensive R ↔ (GeachConfluent ⟨0, 1, 0, 0⟩ R) := by
  simp [GeachConfluent, Extensive];
  constructor;
  . rintro h x y z rfl Rxz; have := h Rxz; tauto;
  . intro h x y Rxy; have := h rfl Rxy; tauto;

lemma functional_def : Functional R ↔ (GeachConfluent ⟨1, 1, 0, 0⟩ R) := by
  simp [GeachConfluent, Functional];
  constructor <;> tauto;

lemma dense_def : Dense R ↔ (GeachConfluent ⟨0, 1, 2, 0⟩ R) := by
  simp [GeachConfluent, Dense];
  constructor;
  . rintro h x y z rfl Rxz; exact h Rxz;
  . intro h x y Rxy; exact h rfl Rxy;

@[simp]
lemma satisfies_eq : GeachConfluent (α := α) t (· = ·) := by simp [GeachConfluent];

end GeachConfluent


def MultiGeachConfluent (ts : List GeachTaple) (R : Rel α α) : Prop :=
  match ts with
  | [] => True
  | [t] => (GeachConfluent t R)
  | t :: ts => (GeachConfluent t R) ∧ (MultiGeachConfluent ts R)

namespace MultiGeachConfluent

@[simp] lemma iff_nil : MultiGeachConfluent [] R := by simp [MultiGeachConfluent];

@[simp] lemma iff_singleton : MultiGeachConfluent [t] R ↔ (GeachConfluent t R) := by simp [MultiGeachConfluent];

lemma iff_cons (h : ts ≠ []) : MultiGeachConfluent (t :: ts) R ↔ (GeachConfluent t R) ∧ (MultiGeachConfluent ts R) := by simp [MultiGeachConfluent];

@[simp]
lemma satisfies_eq : MultiGeachConfluent (α := α) ts (· = ·) := by induction ts using List.induction_with_singleton <;> simp_all [MultiGeachConfluent];

end MultiGeachConfluent



namespace LO.Axioms

variable {F : Type*} [LogicalConnective F] [BasicModalLogicalConnective F]

protected abbrev Geach (t : GeachTaple) (p : F) := ◇^[t.i](□^[t.m]p) ➝ □^[t.j](◇^[t.n]p)
abbrev Geach.set (t : GeachTaple) : Set F := { Axioms.Geach t p | (p) }
notation:max "𝗴𝗲(" t ")" => Geach.set t

namespace Geach

lemma T_def    : 𝗴𝗲(⟨0, 0, 1, 0⟩) = (𝗧 : Set F) := rfl
lemma B_def    : 𝗴𝗲(⟨0, 1, 0, 1⟩) = (𝗕 : Set F) := rfl
lemma D_def    : 𝗴𝗲(⟨0, 0, 1, 1⟩) = (𝗗 : Set F) := rfl
lemma Four_def : 𝗴𝗲(⟨0, 2, 1, 0⟩) = (𝟰 : Set F) := rfl
lemma Five_def : 𝗴𝗲(⟨1, 1, 0, 1⟩) = (𝟱 : Set F) := rfl
lemma Dot2_def : 𝗴𝗲(⟨1, 1, 1, 1⟩) = (.𝟮 : Set F) := rfl
lemma C4_def   : 𝗴𝗲(⟨0, 1, 2, 0⟩) = (𝗖𝟰 : Set F) := rfl
lemma CD_def   : 𝗴𝗲(⟨1, 1, 0, 0⟩) = (𝗖𝗗 : Set F) := rfl
lemma Tc_def   : 𝗴𝗲(⟨0, 1, 0, 0⟩) = (𝗧𝗰 : Set F) := rfl

end Geach

class IsGeach (Ax : Set F) where
  taple : GeachTaple
  char : Ax = 𝗴𝗲(taple) := by rfl

instance : IsGeach (𝗧 : Set F)  where taple := ⟨0, 0, 1, 0⟩;
instance : IsGeach (𝗕 : Set F)  where taple := ⟨0, 1, 0, 1⟩;
instance : IsGeach (𝗗 : Set F)  where taple := ⟨0, 0, 1, 1⟩;
instance : IsGeach (𝟰 : Set F)  where taple := ⟨0, 2, 1, 0⟩;
instance : IsGeach (𝟱 : Set F)  where taple := ⟨1, 1, 0, 1⟩;
instance : IsGeach (.𝟮 : Set F) where taple := ⟨1, 1, 1, 1⟩;
instance : IsGeach (𝗖𝟰 : Set F) where taple := ⟨0, 1, 2, 0⟩;
instance : IsGeach (𝗖𝗗 : Set F) where taple := ⟨1, 1, 0, 0⟩;
instance : IsGeach (𝗧𝗰 : Set F) where taple := ⟨0, 1, 0, 0⟩;

def MultiGeach : List GeachTaple → Set F
  | [] => ∅
  | t :: ts => 𝗴𝗲(t) ∪ (MultiGeach ts)
notation:max "𝗚𝗲(" ts ")" => MultiGeach ts

namespace MultiGeach

@[simp] lemma def_nil : 𝗚𝗲([]) = (∅ : Set F) := by simp [MultiGeach]

@[simp] lemma iff_cons : 𝗚𝗲(x :: l) = (𝗴𝗲(x) : Set F) ∪ 𝗚𝗲(l) := by simp only [MultiGeach];

lemma mem (h : x ∈ l) : (𝗴𝗲(x) : Set F) ⊆ 𝗚𝗲(l) := by
  induction l with
  | nil => contradiction;
  | cons a as ih =>
    simp_all;
    cases h;
    . subst_vars; tauto;
    . apply Set.subset_union_of_subset_right $ ih (by assumption);

end MultiGeach

end LO.Axioms


namespace LO.Modal

variable {Ax : Theory α}

open System

protected abbrev Geach (l : List GeachTaple) : Hilbert α := 𝜿(𝗚𝗲(l))
notation "𝐆𝐞(" l ")" => Modal.Geach l

namespace Geach

end Geach

protected class Hilbert.IsGeach (L : Hilbert α) (ts : List GeachTaple) where
  char : L = 𝐆𝐞(ts) := by aesop;

attribute [simp] Hilbert.IsGeach.char

namespace IsGeach

lemma ax {Λ : Hilbert α} [geach : Λ.IsGeach ts] : Ax(Λ) = (𝗞 ∪ 𝗚𝗲(ts)) := by
  have e := geach.char;
  simp [Modal.Geach] at e;
  simp_all;

instance : 𝐊.IsGeach (α := α) [] where

instance : 𝐊𝐃.IsGeach (α := α) [⟨0, 0, 1, 1⟩] where

instance : 𝐊𝐓.IsGeach (α := α) [⟨0, 0, 1, 0⟩] where

instance : 𝐊𝐓𝐁.IsGeach (α := α) [⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩] where

instance : 𝐊𝟒.IsGeach (α := α) [⟨0, 2, 1, 0⟩] where

instance : 𝐒𝟒.IsGeach (α := α) [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩] where

instance : 𝐒𝟒.𝟐.IsGeach (α := α) [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩] where

instance : 𝐒𝟓.IsGeach (α := α) [⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩] where

instance : 𝐊𝐓𝟒𝐁.IsGeach (α := α) [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩] where

instance : 𝐓𝐫𝐢𝐯.IsGeach (α := α) [⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩] where

end IsGeach

end LO.Modal
