import Mathlib.Data.Rel
import Mathlib.Data.PNat.Basic
import Foundation.Vorspiel.Relation.Supplemental

def Rel.iterate (R : Rel α α) : ℕ → Rel α α
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

lemma unwrap_of_trans' {n : ℕ+} [IsTrans _ R] (Rxy : R.iterate n x y) : R x y := by
  induction n using PNat.recOn generalizing x with
  | one => simpa using Rxy;
  | succ n ih =>
    obtain ⟨z, Rxz, Rzy⟩ := Rxy;
    exact IsTrans.trans _ _ _ Rxz (ih Rzy);

lemma unwrap_of_trans {x y} {n : ℕ} (hn : n > 0) [IsTrans _ R] (Rxy : R.iterate n x y) : R x y := by
  apply unwrap_of_trans' (n := ⟨n, hn⟩) Rxy;

lemma unwrap_of_refl_trans {x y} {n : ℕ} [IsRefl _ R] [IsTrans _ R] (Rxy : R.iterate n x y) : R x y := by
  induction n generalizing x with
  | zero => subst Rxy; apply IsRefl.refl;
  | succ n ih =>
    obtain ⟨z, Rxz, Rzy⟩ := Rxy;
    exact IsTrans.trans _ _ _ Rxz (ih Rzy);

end Rel.iterate



namespace Relation

variable {R : Rel α α} {x y : α}

open Rel.iterate

lemma ReflTransGen.exists_iterate : ReflTransGen R x y ↔ ∃ n, R.iterate n x y := by
  constructor;
  . intro h;
    induction h with
    | refl => use 0;  simp;
    | tail Rxy Ryz ih =>
      obtain ⟨n, Rxy⟩ := ih;
      use n + 1;
      apply Rel.iterate.forward.mpr;
      exact ⟨_, Rxy, Ryz⟩;
  . rintro ⟨n, h⟩;
    induction n generalizing x y with
    | zero => subst h; apply ReflTransGen.refl;
    | succ n ih =>
      obtain ⟨z, Rxz, Rzy⟩ := h;
      apply ReflTransGen.head;
      . exact Rxz;
      . apply ih;
        exact Rzy;

lemma ReflTransGen.remove_iterate (Rxy : Rel.iterate (ReflTransGen R) n x y) : (ReflTransGen R) x y := by
  apply unwrap_of_refl_trans (n := n) Rxy;

lemma ReflTransGen.unwrap [IsRefl _ R] [IsTrans _ R] (Rxy : (ReflTransGen R) x y) : R x y := by
  obtain ⟨n, Rxy⟩ := ReflTransGen.exists_iterate.mp Rxy;
  exact unwrap_of_refl_trans Rxy;

lemma TransGen.exists_iterate' : TransGen R x y ↔ ∃ n : ℕ+, R.iterate n x y := by
  constructor;
  . intro h;
    induction h with
    | single h => use 1; simpa;
    | tail Rxy Ryz ih =>
      obtain ⟨⟨n, hn⟩, Rxy⟩ := ih;
      use ⟨n + 1, by omega⟩;
      apply Rel.iterate.forward.mpr;
      refine ⟨_, Rxy, Ryz⟩;
  . rintro ⟨n, Rxy⟩;
    induction n using PNat.recOn generalizing x with
    | one =>
      apply TransGen.single;
      simpa using Rxy;
    | succ n ih =>
      obtain ⟨z, Rxz, Rzy⟩ := Rxy;
      apply TransGen.head;
      . exact Rxz;
      . apply ih;
        exact Rzy;

lemma TransGen.exists_iterate : TransGen R x y ↔ ∃ n > 0, R.iterate n x y := by
  constructor;
  . intro h;
    obtain ⟨⟨n, hn⟩, h⟩ := TransGen.exists_iterate'.mp h;
    exact ⟨n, ⟨by omega, h⟩⟩;
  . rintro ⟨n, ⟨_, Rxy⟩⟩;
    apply TransGen.exists_iterate'.mpr;
    exact ⟨⟨n, by omega⟩, Rxy⟩;

lemma TransGen.remove_iterate (hn : n > 0) (Rxy : Rel.iterate (TransGen R) n x y) : (TransGen R) x y := by
  apply unwrap_of_trans hn Rxy;

lemma TransGen.unwrap [IsTrans _ R] (Rxy : (TransGen R) x y) : R x y := by
  have ⟨n, hn, Rxy⟩ := TransGen.exists_iterate.mp Rxy;
  exact unwrap_of_trans hn Rxy;

instance TransGen.antisymm [IsTrans _ R] [IsAntisymm _ R] : IsAntisymm _ (TransGen R) := by
  apply isAntisymm_iff _ _ |>.mpr;
  intro x y Rxy Ryx;
  exact IsAntisymm.antisymm _ _ Rxy.unwrap Ryx.unwrap;

end Relation
