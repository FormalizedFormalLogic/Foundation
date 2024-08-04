import Mathlib.Data.Rel

def Rel.iterate (R : Rel α α) : ℕ → α → α → Prop
  | 0 => (· = ·)
  | n + 1 => fun x y ↦ ∃ z, R x z ∧ R.iterate n z y

namespace Rel.iterate

variable {R : Rel α α} {n : ℕ}

@[simp]
lemma iff_zero {x y : α} : R.iterate 0 x y ↔ x = y := iff_of_eq rfl

@[simp]
lemma iff_succ {x y : α} : R.iterate (n + 1) x y ↔ ∃ z, R x z ∧ R.iterate n z y := iff_of_eq rfl

@[simp]
lemma eq : Rel.iterate (α := α) (· = ·) n = (· = ·) := by
  induction n with
  | zero => rfl;
  | succ n ih => aesop

lemma forward : (R.iterate (n + 1) x y) ↔ ∃ z, R.iterate n x z ∧ R z y := by
  induction n generalizing x y with
  | zero => simp_all;
  | succ n ih =>
    constructor;
    . rintro ⟨z, Rxz, Rzy⟩;
      obtain ⟨w, Rzw, Rwy⟩ := ih.mp Rzy;
      use w;
      constructor;
      . use z;
      . assumption;
    . rintro ⟨z, ⟨w, Rxw, Rwz⟩, Rzy⟩;
      use w;
      constructor;
      . assumption;
      . apply ih.mpr;
        use z;

end Rel.iterate
