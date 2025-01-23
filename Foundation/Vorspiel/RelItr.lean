import Foundation.Vorspiel.Vorspiel

def Rel.Iterate (R : Rel α α) : ℕ → α → α → Prop
  | 0 => (· = ·)
  | n + 1 => fun x y ↦ ∃ z, R x z ∧ R.Iterate n z y

namespace Rel.Iterate

variable {R : Rel α α} {n m : ℕ}

@[simp]
lemma iff_zero {x y : α} : R.Iterate 0 x y ↔ x = y := iff_of_eq rfl

@[simp]
lemma iff_succ {x y : α} : R.Iterate (n + 1) x y ↔ ∃ z, R x z ∧ R.Iterate n z y := iff_of_eq rfl

@[simp]
lemma eq : Rel.Iterate (α := α) (· = ·) n = (· = ·) := by
  induction n with
  | zero => rfl;
  | succ n ih => aesop

lemma forward : (R.Iterate (n + 1) x y) ↔ ∃ z, R.Iterate n x z ∧ R z y := by
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

lemma true_any (h : x = y) : Rel.Iterate (λ _ _ => True) n x y := by
  induction n with
  | zero => simpa;
  | succ n ih => use x;

lemma congr (h : R.Iterate n x y) (he : n = m) : R.Iterate m x y := by
  subst he;
  exact h;

lemma comp : (∃ z, R.Iterate n x z ∧ R.Iterate m z y) ↔ R.Iterate (n + m) x y := by
  constructor;
  . rintro ⟨z, hzx, hzy⟩;
    induction n generalizing x with
    | zero => simp_all;
    | succ n ih =>
      suffices R.Iterate (n + m + 1) x y by apply congr this (by omega);
      obtain ⟨w, hxw, hwz⟩ := hzx;
      use w;
      constructor;
      . exact hxw;
      . exact @ih w hwz;
  . rintro h;
    induction n generalizing x with
    | zero => simp_all;
    | succ n ih =>
      have rxy : R.Iterate (n + m + 1) x y := congr h (by omega);
      obtain ⟨w, rxw, rwy⟩ := rxy;
      obtain ⟨u, rwu, ruy⟩ := @ih w rwy;
      use u;
      constructor;
      . use w;
      . assumption;

end Rel.Iterate
