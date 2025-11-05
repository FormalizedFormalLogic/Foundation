import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rel

def HRel (α : Type*) := α → α → Prop


namespace HRel

variable {α} {R : HRel α} {x y z : α}

local infix:50 " ≺ " => R

def Iterate (R : HRel α) : ℕ → HRel α
  | 0 => (· = ·)
  | n + 1 => fun x y ↦ ∃ z, R x z ∧ R.Iterate n z y

namespace Iterate

@[simp]
lemma iff_zero {x y : α} : R.Iterate 0 x y ↔ x = y := iff_of_eq rfl

@[simp]
lemma iff_succ {x y : α} : R.Iterate (n + 1) x y ↔ ∃ z, R x z ∧ R.Iterate n z y := iff_of_eq rfl

lemma pos_succ_iff (pos : n > 0) {x y : α} : R.Iterate n x y ↔ ∃ z, R x z ∧ R.Iterate n.pred z y := by
  have : n.pred + 1 = n := Nat.sub_one_add_one_eq_of_pos pos
  simpa only [this] using iff_succ (n := n.pred)

lemma succ_left (Rxz : R x z) (Rzy : R.Iterate n z y) : R.Iterate (n + 1) x y := iff_succ.mp ⟨z, Rxz, Rzy⟩

@[simp]
lemma eq : HRel.Iterate (α := α) (· = ·) n = (· = ·) := by
  induction n with
  | zero => rfl;
  | succ n ih => simp [Iterate]; aesop

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

lemma true_any (h : x = y) : HRel.Iterate (λ _ _ => True) n x y := by
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

lemma unwrap_of_trans {n : ℕ+} [IsTrans _ R] (Rxy : R.Iterate n x y) : R x y := by
  induction n using PNat.recOn generalizing x with
  | one => simpa using Rxy;
  | succ n ih =>
    obtain ⟨z, Rxz, Rzy⟩ := Rxy;
    exact IsTrans.trans _ _ _ Rxz (ih Rzy);

lemma unwrap_of_trans_of_pos {n : ℕ} (h : 0 < n) [IsTrans _ R] (Rxy : R.Iterate n x y) : R x y := by
  have : ∃ m : ℕ+, n = m := ⟨⟨n, h⟩, by simp⟩
  rcases this with ⟨n, rfl⟩
  exact unwrap_of_trans Rxy

lemma unwrap_of_refl_trans {n : ℕ} [IsRefl _ R] [IsTrans _ R] (Rxy : R.Iterate n x y) : R x y := by
  induction n generalizing x with
  | zero => subst Rxy; apply IsRefl.refl;
  | succ n ih =>
    obtain ⟨z, Rxz, Rzy⟩ := Rxy;
    exact IsTrans.trans _ _ _ Rxz (ih Rzy);

lemma constant_trans_of_pos {n : ℕ} (pos : 0 < n) [IsTrans _ R] (Rzx : R z x) (Rxy : R.Iterate n x y) : R.Iterate n z y := by
  rcases (pos_succ_iff pos).mp Rxy with ⟨w, Rxw, hwy⟩
  have : R z w := IsTrans.trans _ _ _ Rzx Rxw
  have := succ_left this hwy
  simpa [Nat.sub_one_add_one_eq_of_pos pos] using this

end Iterate


open Iterate


def ReflGen (R : HRel α) : HRel α := Relation.ReflGen R

namespace ReflGen

instance : IsRefl α (R.ReflGen) := ⟨by apply Relation.ReflGen.refl⟩

instance [IsTrans _ R] : IsTrans α (R.ReflGen) := ⟨by
  rintro a b c (rfl | Rab) (rfl | Rbc);
  . exact Relation.ReflGen.refl;
  . exact Relation.ReflGen.single Rbc;
  . exact Relation.ReflGen.single Rab;
  . exact Relation.ReflGen.single $ IsTrans.trans a b c Rab Rbc;
⟩

instance [IsSymm _ R] : IsSymm α (ReflGen R) := ⟨by
  rintro a b (rfl | Rab);
  . exact Relation.ReflGen.refl;
  . exact Relation.ReflGen.single $ IsSymm.symm _ _ Rab;
⟩

instance [IsIrrefl _ R] [IsTrans _ R] : IsAntisymm α (ReflGen R) := ⟨by
  rintro a b (rfl | Rab) (rfl | Rba);
  . trivial;
  . trivial;
  . trivial;
  . exfalso;
    exact IsIrrefl.irrefl a $ IsTrans.trans a b a Rab Rba
⟩

instance [IsTrans _ R] [IsIrrefl _ R] : IsPartialOrder α (ReflGen R) where

end ReflGen


def TransGen (R : HRel α) : HRel α := Relation.TransGen R

local infix:50 " ≺^+ " => TransGen R

namespace TransGen

instance : IsTrans α R.TransGen := ⟨by apply Relation.TransGen.trans⟩

lemma trans {x y z : α} (Rxy : x ≺^+ y) (Ryz : y ≺^+ z) : x ≺^+ z := Relation.TransGen.trans Rxy Ryz

lemma single (Rxy : x ≺ y) : x ≺^+ y := Relation.TransGen.single Rxy

lemma head (Rxy : x ≺ y) (Ryz : y ≺^+ z) : x ≺^+ z := Relation.TransGen.head Rxy Ryz

lemma tail (Rxy : x ≺^+ y) (Ryz : y ≺ z) : x ≺^+ z := Relation.TransGen.tail Rxy Ryz

lemma exists_iterate : TransGen R x y ↔ ∃ n : ℕ+, R.Iterate n x y := by
  constructor;
  . intro h;
    induction h with
    | single h => use 1; simpa;
    | tail Rxy Ryz ih =>
      obtain ⟨⟨n, hn⟩, Rxy⟩ := ih;
      use ⟨n + 1, by omega⟩;
      apply HRel.Iterate.forward.mpr;
      refine ⟨_, Rxy, Ryz⟩;
  . rintro ⟨n, Rxy⟩;
    induction n using PNat.recOn generalizing x with
    | one =>
      apply single;
      simpa using Rxy;
    | succ n ih =>
      obtain ⟨z, Rxz, Rzy⟩ := Rxy;
      apply head;
      . exact Rxz;
      . apply ih;
        exact Rzy;

lemma remove_iterate {n : ℕ+} (Rxy : R.TransGen.Iterate n x y) : R.TransGen x y := by
  apply unwrap_of_trans (n := n) Rxy;

lemma unwrap [IsTrans _ R] (Rxy : R.TransGen x y) : R x y := by
  have ⟨n, Rxy⟩ := TransGen.exists_iterate.mp Rxy;
  exact unwrap_of_trans (n := n) Rxy;

@[simp] lemma unwrap_iff [IsTrans _ R] : R.TransGen x y ↔ R x y :=
  ⟨unwrap, single⟩

instance [IsRefl _ R] : IsRefl α R.TransGen := ⟨fun x ↦ Relation.TransGen.single (IsRefl.refl x)⟩

instance [IsSymm _ R] : IsSymm α R.TransGen := ⟨by
  rintro x y Rxy;
  induction Rxy with
  | single Rxy =>
    apply single;
    apply IsSymm.symm _ _ Rxy;
  | tail _ hyz ih =>
    exact trans (Relation.TransGen.single $ (IsSymm.symm _ _) hyz) ih
⟩

instance [IsTrans _ R] [IsAntisymm _ R] : IsAntisymm α R.TransGen := ⟨by
  rintro x y Rxy Ryx;
  exact IsAntisymm.antisymm _ _ Rxy.unwrap Ryx.unwrap;
⟩

end TransGen

def ReflTransGen (R : HRel α) : HRel α := Relation.ReflTransGen R

namespace ReflTransGen

instance : IsRefl _ (R.ReflTransGen) := ⟨by apply Relation.ReflTransGen.refl⟩
instance : IsTrans _ (R.ReflTransGen) := ⟨by apply Relation.ReflTransGen.trans⟩

lemma exists_iterate : R.ReflTransGen x y ↔ ∃ n : ℕ, R.Iterate n x y := by
  constructor;
  . intro h;
    induction h with
    | refl => use 0;  simp;
    | tail Rxy Ryz ih =>
      obtain ⟨n, Rxy⟩ := ih;
      use n + 1;
      apply HRel.Iterate.forward.mpr;
      exact ⟨_, Rxy, Ryz⟩;
  . rintro ⟨n, h⟩;
    induction n generalizing x y with
    | zero => subst h; apply Relation.ReflTransGen.refl;
    | succ n ih =>
      obtain ⟨z, Rxz, Rzy⟩ := h;
      apply Relation.ReflTransGen.head;
      . exact Rxz;
      . apply ih;
        exact Rzy;

lemma remove_iterate (Rxy : (ReflTransGen R).Iterate n x y) : (R.ReflTransGen) x y := by
  apply unwrap_of_refl_trans (n := n) Rxy;

lemma unwrap [IsRefl _ R] [IsTrans _ R] (Rxy : (R.ReflTransGen) x y) : R x y := by
  obtain ⟨n, Rxy⟩ := ReflTransGen.exists_iterate.mp Rxy;
  exact unwrap_of_refl_trans Rxy;

instance [IsSymm _ R] : IsSymm _ (R.ReflTransGen) := ⟨by
  rintro x y Rxy;
  induction Rxy with
  | refl => apply Relation.ReflTransGen.refl;
  | @tail y z Rxy Ryz Ryx => exact Relation.ReflTransGen.head (IsSymm.symm _ _ Ryz) Ryx;
⟩

end ReflTransGen


def IrreflGen (r : HRel α) : HRel α := λ x y => r x y ∧ x ≠ y

namespace IrreflGen

instance : IsIrrefl α (R.IrreflGen) := ⟨by simp [IrreflGen]⟩

instance [IsTrans _ R] [IsAntisymm _ R] : IsTrans _ (R.IrreflGen) := ⟨by
  rintro a b c ⟨Rab, hne⟩ ⟨Rbc, _⟩;
  constructor;
  . exact IsTrans.trans a b c Rab Rbc;
  . by_contra hC;
    subst hC;
    exact hne $ IsAntisymm.antisymm a b Rab Rbc;
⟩

instance [IsPartialOrder _ R] : IsStrictOrder _ (R.IrreflGen) where

end IrreflGen


def CovBy (R : HRel α) : HRel α := fun x y ↦ R x y ∧ ∀ z, ¬R x z ∨ ¬R z y

namespace CovBy

@[grind] lemma rel (h : R.CovBy x y) : R x y := h.1

lemma no_intermediate (h : R.CovBy x y) : ∀ z, ¬R x z ∨ ¬R z y := h.2

lemma no_intermediate' (h : R.CovBy x y) : ∀ z, R x z → ¬R z y :=
  fun z ↦ imp_iff_not_or.mpr (h.no_intermediate z)

@[simp] lemma irrefl (x : α) : ¬R.CovBy x x := fun h ↦ by
  have : R x x := h.rel
  rcases h.no_intermediate x <;> contradiction

instance : IsIrrefl α R.CovBy := ⟨irrefl⟩

lemma not_covby_iff {x y : α} : ¬R.CovBy x y ↔ R x y → ∃ z, R x z ∧ R z y := by simp [CovBy]

lemma antitrans (hxy : R x y) (hyz : R y z) : ¬R.CovBy x z :=
  not_covby_iff.mpr fun _ ↦ ⟨y, hxy, hyz⟩

lemma off (hab : R.CovBy a b) (hac : R a c) : R b c := by { 
  
 }

end CovBy

def Rightmost (R : HRel α) (a : α) : Prop := ∀ b, ¬R a b

namespace Rightmost

@[simp] lemma not_iff : ¬R.Rightmost a ↔ ∃ b, R a b := by simp [Rightmost]

end Rightmost

def Leftmost (R : HRel α) (a : α) : Prop := ∀ b, ¬R b a

namespace Leftmost

@[simp] lemma not_iff : ¬R.Leftmost a ↔ ∃ b, R b a := by simp [Leftmost]

end Leftmost

end HRel
