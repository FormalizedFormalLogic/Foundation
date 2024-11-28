import Mathlib.Data.Rel

def Rel.iterate (R : Rel α α) : ℕ → α → α → Prop
  | 0 => (· = ·)
  | n + 1 => fun x y ↦ ∃ z, R x z ∧ R.iterate n z y

namespace Rel.iterate

variable {R : Rel α α} {n m : ℕ}

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

lemma true_any (h : x = y) : Rel.iterate (λ _ _ => True) n x y := by
  induction n with
  | zero => simpa;
  | succ n ih => use x;

lemma congr (h : R.iterate n x y) (he : n = m) : R.iterate m x y := by
  subst he;
  exact h;

lemma comp : (∃ z, R.iterate n x z ∧ R.iterate m z y) ↔ R.iterate (n + m) x y := by
  constructor;
  . rintro ⟨z, hzx, hzy⟩;
    induction n generalizing x with
    | zero => simp_all;
    | succ n ih =>
      suffices R.iterate (n + m + 1) x y by apply congr this (by omega);
      obtain ⟨w, hxw, hwz⟩ := hzx;
      use w;
      constructor;
      . exact hxw;
      . exact @ih w hwz;
  . rintro h;
    induction n generalizing x with
    | zero => simp_all;
    | succ n ih =>
      have rxy : R.iterate (n + m + 1) x y := congr h (by omega);
      obtain ⟨w, rxw, rwy⟩ := rxy;
      obtain ⟨u, rwu, ruy⟩ := @ih w rwy;
      use u;
      constructor;
      . use w;
      . assumption;


-- lemma comp' {n m : ℕ+} : (∃ z, x ≺^[n] z ∧ z ≺^[m] y) ↔ x ≺^[n + m] y := comp

end Rel.iterate
