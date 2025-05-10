import Foundation.Vorspiel.Vorspiel
import Foundation.Vorspiel.List.Vector
import Mathlib.Computability.Halting
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Godel.GodelBetaFunction

open Mathlib List.Vector Part

namespace Nat

lemma pos_of_eq_one (h : n = 1) : 0 < n := by simp[h]

def isEqNat (n m : ℕ) : ℕ := if n = m then 1 else 0

def isLtNat (n m : ℕ) : ℕ := if n < m then 1 else 0

def isLeNat (n m : ℕ) : ℕ := if n ≤ m then 1 else 0

def isDvdNat (n m : ℕ) : ℕ := if n ∣ m then 1 else 0

@[simp] lemma isEqNat_pos_iff : 0 < isEqNat n m ↔ n = m := by simp[isEqNat]; by_cases n = m <;> simp[*]

@[simp] lemma isLtNat_pos_iff : 0 < isLtNat n m ↔ n < m := by simp[isLtNat]; by_cases n < m <;> simp[*]

@[simp] lemma isLeNat_pos_iff : 0 < isLeNat n m ↔ n ≤ m := by simp[isLeNat]; by_cases n ≤ m <;> simp[*]

@[simp] lemma isDvdNat_pos_iff : 0 < isDvdNat n m ↔ n ∣ m := by simp[isDvdNat]; by_cases n ∣ m <;> simp[*]

def inv (n : ℕ) : ℕ := isEqNat n 0

def pos (n : ℕ) : ℕ := isLtNat 0 n

@[simp] lemma inv_zero : inv 0 = 1 := rfl

@[simp] lemma inv_iff_ne_zero : inv n = 0 ↔ 0 < n := by simp[inv, isEqNat, zero_lt_iff]

@[simp] lemma inv_ne_zero (h : n ≠ 0) : inv n = 0 := by simp[inv, isEqNat, h]

@[simp] lemma pos_zero : pos 0 = 0 := rfl

@[simp] lemma pos_ne_zero (h : n ≠ 0) : pos n = 1 := by simp[pos, isLtNat, h]

def and (n m : ℕ) : ℕ := isLtNat 0 (n * m)

def or (n m : ℕ) : ℕ := isLtNat 0 (n + m)

lemma and_eq (n m : ℕ) : and n m = if 0 < n ∧ 0 < m then 1 else 0 := by simp [mul_pos_iff, and, isLtNat]

lemma and_eq_one (n m : ℕ) : and n m = 1 ↔ 0 < n ∧ 0 < m := by simp[and_eq, imp_false, Nat.pos_iff_ne_zero]

lemma or_eq (n m : ℕ) : or n m = if 0 < n ∨ 0 < m then 1 else 0 := by simp[or, isLtNat]

@[simp] lemma and_pos_iff (n m : ℕ) : 0 < and n m ↔ 0 < n ∧ 0 < m := by simp[and_eq]; by_cases 0 < n ∧ 0 < m <;> simp[*]

@[simp] lemma or_pos_iff (n m : ℕ) : 0 < or n m ↔ 0 < n ∨ 0 < m := by simp[or_eq]; by_cases 0 < n ∨ 0 < m <;> simp[*]

@[simp] lemma inv_pos_iff (n : ℕ) : 0 < inv n ↔ ¬0 < n := by simp[inv]

@[simp] lemma pos_pos_iff (n : ℕ) : 0 < pos n ↔ 0 < n := by simp[pos]

def ball (n : ℕ) (φ : ℕ → ℕ) : ℕ := n.rec 1 (fun n ih => (φ n).pos.and ih)

@[simp] lemma ball_pos_iff {φ : ℕ → ℕ} {n : ℕ} : 0 < ball n φ ↔ ∀ m < n, 0 < φ m := by
  induction' n with n ih <;> simp[ball, Nat.lt_succ_iff] at*
  · simp[ih]; exact ⟨
    by rintro ⟨hn, hp⟩ m hm; rcases lt_or_eq_of_le hm with (hm | rfl); { exact hp _ hm }; { exact hn },
    by intro h; exact ⟨h n (Nat.le_refl n), fun m hm => h m (le_of_lt hm)⟩⟩

@[simp] lemma ball_eq_zero_iff {φ : ℕ → ℕ} {n : ℕ} : ball n φ = 0 ↔ ∃ m < n, φ m = 0 := by
  simpa[-ball_pos_iff] using not_iff_not.mpr (ball_pos_iff (φ := φ) (n := n))

lemma ball_pos_iff_eq_one {φ : ℕ → ℕ} {n : ℕ} : ball n φ = 1 ↔ 0 < ball n φ := by
  induction' n with n _ <;> simp[ball, Nat.lt_succ_iff] at*
  · constructor
    · intro h; simpa using pos_of_eq_one h
    · intro h; simpa[and_eq_one] using h

inductive ArithPart₁ : ∀ {n}, (List.Vector ℕ n →. ℕ) → Prop
  | zero {n} : @ArithPart₁ n (fun _ => 0)
  | one {n} : @ArithPart₁ n (fun _ => 1)
  | add {n} (i j : Fin n) : @ArithPart₁ n (fun v => v.get i + v.get j : List.Vector ℕ n → ℕ)
  | mul {n} (i j : Fin n) : @ArithPart₁ n (fun v => v.get i * v.get j : List.Vector ℕ n → ℕ)
  | proj {n} (i : Fin n) : @ArithPart₁ n (fun v => v.get i : List.Vector ℕ n → ℕ)
  | equal {n} (i j : Fin n) : @ArithPart₁ n (fun v => isEqNat (v.get i) (v.get j) : List.Vector ℕ n → ℕ)
  | lt {n} (i j : Fin n) : @ArithPart₁ n (fun v => isLtNat (v.get i) (v.get j) : List.Vector ℕ n → ℕ)
  | comp {m n f} (g : Fin n → List.Vector ℕ m →. ℕ) :
    ArithPart₁ f → (∀ i, ArithPart₁ (g i)) → ArithPart₁ fun v => (List.Vector.mOfFn fun i => g i v) >>= f
  | rfind {n} {f : List.Vector ℕ (n + 1) → ℕ} :
    ArithPart₁ (n := n + 1) f → ArithPart₁ (fun v => rfind fun n => Part.some (f (n ::ᵥ v) = 0))

def Arith₁ (f : List.Vector ℕ n → ℕ) := ArithPart₁ (n := n) f

end Nat

namespace Nat.ArithPart₁

open Primrec

lemma to_partrec' {n} {f : List.Vector ℕ n →. ℕ} (hf : ArithPart₁ f) : Partrec' f := by
  induction hf
  case zero => exact Partrec'.of_part (Partrec.const' 0)
  case one  => exact Partrec'.of_part (Partrec.const' 1)
  case add n i j =>
    exact (Partrec'.of_part ((Primrec.nat_add.comp
      (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const i))
      (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const j))).to_comp.partrec))
  case mul n i j =>
    exact (Partrec'.of_part ((Primrec.nat_mul.comp
      (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const i))
      (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const j))).to_comp.partrec))
  case proj n i =>
    exact Partrec'.of_part
      (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const i)).to_comp.partrec
  case equal n i j =>
    have : Primrec (fun (v : List.Vector ℕ n) => if v.get i = v.get j then 1 else 0) :=
      Primrec.ite
        (Primrec.eq.comp
          (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const i))
          (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const j)))
        (_root_.Primrec.const 1)
        (_root_.Primrec.const 0)
    exact Partrec'.of_part this.to_comp.partrec
  case lt n i j =>
    have : Primrec (fun (v : List.Vector ℕ n) => if v.get i < v.get j then 1 else 0) :=
      Primrec.ite
        (Primrec.nat_lt.comp
          (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const i))
          (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const j)))
        (_root_.Primrec.const 1)
        (_root_.Primrec.const 0)
    exact Partrec'.of_part this.to_comp.partrec
  case comp m n f g _ _ hf hg =>
    exact Partrec'.comp g hf hg
  case rfind f _ hf =>
    exact Partrec'.rfind hf

lemma of_eq {n} {f g : List.Vector ℕ n →. ℕ} (hf : ArithPart₁ f) (H : ∀ i, f i = g i) : ArithPart₁ g :=
  (funext H : f = g) ▸ hf

lemma bind (f : List.Vector ℕ n → ℕ →. ℕ) (hf : @ArithPart₁ (n + 1) fun v => f v.tail v.head) {g} (hg : @ArithPart₁ n g) :
    @ArithPart₁ n fun v => (g v).bind (f v) :=
  (hf.comp (g :> fun i v => v.get i) (fun i => by cases i using Fin.cases <;> simp[*]; exact proj _)).of_eq (by
    intro v; simp
    rcases Part.eq_none_or_eq_some (g v) with (hgv | ⟨x, hgv⟩)
    · simp[hgv, List.Vector.mOfFn]
    · simp[hgv, Matrix.comp_vecCons']
      have : List.Vector.mOfFn (fun i => (g :> fun j v => Part.some $ v.get j) i v) = pure (List.Vector.ofFn (x :> fun j => v.get j)) := by
        rw[←List.Vector.mOfFn_pure]; apply congr_arg
        funext i; cases i using Fin.cases <;> simp[hgv]
      simp[this])

lemma map (f : List.Vector ℕ n → ℕ → ℕ) (hf : @Arith₁ (n + 1) fun v => f v.tail v.head) {g} (hg : @ArithPart₁ n g) :
    @ArithPart₁ n fun v => (g v).map (f v) :=
  (bind (Part.some $ f · ·) (hf.of_eq <| by simp) hg).of_eq <| by
  intro v; rcases Part.eq_none_or_eq_some (g v) with (_ | ⟨x, _⟩) <;> simp[*]

lemma comp₁ (f : ℕ →. ℕ) (hf : @ArithPart₁ 1 fun v => f (v.get 0)) {n g} (hg : @Arith₁ n g) :
    @ArithPart₁ n fun v => f (g v) :=
  (hf.comp _ fun _ => hg).of_eq (by simp)

lemma comp₂ (f : ℕ → ℕ →. ℕ) (hf : @ArithPart₁ 2 fun v => f (v.get 0) (v.get 1)) {n g h} (hg : @Arith₁ n g) (hh : @Arith₁ n h) :
    @ArithPart₁ n fun v => f (g v) (h v) :=
  (hf.comp ![g, h] (fun i => i.cases hg (fun i => by simpa using hh))).of_eq
    (by intro i
        have : (fun j => (![↑g, h] : Fin 2 → List.Vector ℕ n →. ℕ) j i) = (fun j => pure (![g i, h i] j)) := by
          funext j; cases j using Fin.cases <;> simp[Fin.eq_zero]
        simp[Matrix.comp_vecCons']; simp[this] )

lemma rfind' {n} {f : ℕ → List.Vector ℕ n → ℕ} (h : Arith₁ (n := n + 1) (fun v => f v.head v.tail)) :
    ArithPart₁ (fun v => Nat.rfind fun n => Part.some (f n v = 0)) := rfind h

lemma rfind'₁ {n} (i : Fin n) {f : ℕ → ℕ → ℕ} (h : Arith₁ (n := 2) (fun v => f (v.get 0) (v.get 1))) :
    ArithPart₁ (fun v => Nat.rfind fun n => Part.some (f n (v.get i) = 0)) :=
  (rfind h).comp₁ (fun m => Nat.rfind fun n => Part.some (f n m = 0)) (proj i)

end Nat.ArithPart₁

namespace Nat.Arith₁

lemma of_eq {n} {f g : List.Vector ℕ n → ℕ} (hf : Arith₁ f) (H : ∀ i, f i = g i) : Arith₁ g :=
  (funext H : f = g) ▸ hf

lemma zero {n} : @Arith₁ n (fun _ => 0 : List.Vector ℕ n → ℕ) := Nat.ArithPart₁.zero

lemma one {n} : @Arith₁ n (fun _ => 1 : List.Vector ℕ n → ℕ) := Nat.ArithPart₁.one

lemma add {n} (i j : Fin n) : @Arith₁ n (fun v => v.get i + v.get j) := Nat.ArithPart₁.add i j

lemma mul {n} (i j : Fin n) : @Arith₁ n (fun v => v.get i * v.get j) := Nat.ArithPart₁.mul i j

lemma proj {n} (i : Fin n) : @Arith₁ n (fun v => v.get i) := Nat.ArithPart₁.proj i

lemma head {n} : @Arith₁ (n + 1) (fun v => v.head) := (Nat.ArithPart₁.proj 0).of_eq <| by simp

lemma equal {n} (i j : Fin n) : @Arith₁ n (fun v => isEqNat (v.get i) (v.get j)) := Nat.ArithPart₁.equal i j

lemma lt {n} (i j : Fin n) : @Arith₁ n (fun v => isLtNat (v.get i) (v.get j)) := Nat.ArithPart₁.lt i j

lemma comp {m n f} (g : Fin n → List.Vector ℕ m → ℕ) (hf : Arith₁ f) (hg : ∀ i, Arith₁ (g i)) :
    Arith₁ fun v => f (List.Vector.ofFn fun i => g i v) :=
  (Nat.ArithPart₁.comp (fun i => g i : Fin n → List.Vector ℕ m →. ℕ) hf hg).of_eq <| by simp

def Vec {n m} (f : List.Vector ℕ n → List.Vector ℕ m) : Prop := ∀ i, Arith₁ fun v => (f v).get i

protected lemma nil {n} : @Vec n 0 (fun _ => nil) := fun i => i.elim0

protected lemma cons {n m f g} (hf : @Arith₁ n f) (hg : @Vec n m g) :
    Vec (fun v => f v ::ᵥ g v) := fun i => Fin.cases (by simp [*]) (fun i => by simp [hg i]) i

lemma tail {n f} (hf : @Arith₁ n f) : @Arith₁ n.succ fun v => f v.tail :=
  (hf.comp _ fun i => @proj _ i.succ).of_eq fun v => by
    rw[←ofFn_get v.tail]; congr; funext i; simp

lemma comp' {n m f g} (hf : @Arith₁ m f) (hg : @Vec n m g) : Arith₁ fun v => f (g v) :=
  (hf.comp _ hg).of_eq fun v => by simp

lemma comp₁ (f : ℕ → ℕ) (hf : @Arith₁ 1 fun v => f (v.get 0)) {n g} (hg : @Arith₁ n g) :
    @Arith₁ n fun v => f (g v) :=
  (hf.comp _ fun _ => hg).of_eq (by simp)

lemma comp₂ (f : ℕ → ℕ → ℕ) (hf : @Arith₁ 2 fun v => f (v.get 0) (v.get 1)) {n g h} (hg : @Arith₁ n g) (hh : @Arith₁ n h) :
    @Arith₁ n fun v => f (g v) (h v) :=
  (hf.comp ![g, h] (fun i => i.cases hg (fun i => by simpa using hh))).of_eq (by intro i; simp[Matrix.comp_vecCons'])

lemma succ {n} (i : Fin n) : Arith₁ (fun v => v.get i + 1) := (add 0 1).comp₂ _ (proj i) one

lemma const {n} : ∀ m, @Arith₁ n fun _ => m
  | 0     => zero
  | m + 1 => (succ 0).comp₁ _ (const m)

lemma inv {n} (i : Fin n) : Arith₁ (fun v => inv (v.get i)) := (equal 0 1).comp₂ _ (proj i) zero

lemma pos {n} (i : Fin n) : Arith₁ (fun v => pos (v.get i)) := (lt 0 1).comp₂ _ zero (proj i)

lemma and {n} (i j : Fin n) : Arith₁ (fun v => and (v.get i) (v.get j)) := (lt 0 1).comp₂ _ zero (mul i j)

lemma or {n} (i j : Fin n) : Arith₁ (fun v => or (v.get i) (v.get j)) := (lt 0 1).comp₂ _ zero (add i j)

lemma le {n} (i j : Fin n) : @Arith₁ n (fun v => isLeNat (v.get i) (v.get j)) :=
  ((or 0 1).comp₂ _ (lt i j) (equal i j)).of_eq <| by simp[Nat.or_eq, Nat.le_iff_lt_or_eq, isLeNat]

lemma if_pos {n} {f g h : List.Vector ℕ n → ℕ} (hf : Arith₁ f) (hg : Arith₁ g) (hh : Arith₁ h) :
    Arith₁ (fun v => if 0 < f v then g v else h v) := by
  have : Arith₁ (fun v => (f v).pos * (g v) + (f v).inv * (h v)) :=
    (add 0 1).comp₂ _
      ((mul 0 1).comp₂ _ ((pos 0).comp₁ _ hf) hg)
      ((mul 0 1).comp₂ _ ((inv 0).comp₁ _ hf) hh)
  exact this.of_eq <| by
    intro i; by_cases hf : f i = 0 <;> simp[hf, zero_lt_iff]

lemma to_arith₁ {f : List.Vector ℕ n → ℕ} (h : Arith₁ f) : @ArithPart₁ n (fun x => f x) := h

end Nat.Arith₁

namespace Nat.ArithPart₁

lemma rfindPos {n} {f : List.Vector ℕ (n + 1) → ℕ} (h : Arith₁ f) :
    ArithPart₁ (fun v => Nat.rfind fun n => Part.some (0 < f (n ::ᵥ v))) :=
  (ArithPart₁.rfind ((Arith₁.inv 0).comp₁ _ ((Arith₁.lt 0 1).comp₂ _ zero h))).of_eq <| by simp

lemma rfindPos₁ {n} (i : Fin n) {f : ℕ → ℕ → ℕ} (h : Arith₁ (n := 2) (fun v => f (v.get 0) (v.get 1))) :
    ArithPart₁ (fun v => Nat.rfind fun n => Part.some (0 < f n (v.get i))) :=
  (rfindPos h).comp₁ (fun m => Nat.rfind fun n => Part.some (0 < f n m)) (proj i)

lemma inv_fun {n} (i : Fin n) (f : ℕ → ℕ) (hf : Arith₁ (n := 1) (fun v => f (v.get 0))) :
    ArithPart₁ (fun v => Nat.rfind (fun x => Part.some (f x ≤ v.get i ∧ v.get i < f (x + 1)))) := by
  let F : ℕ → ℕ → ℕ := fun x y => (isLeNat (f x) y).and (isLtNat y (f (x + 1)))
  have := rfindPos₁ i (f := F) <| (Arith₁.and 0 1).comp₂ _
      ((Arith₁.le 0 1).comp₂ _ (hf.comp₁ _ (proj 0)) (proj 1))
      ((Arith₁.lt 0 1).comp₂ _ (proj 1) (hf.comp₁ _ $ (Arith₁.succ 0).comp₁ _ $ proj 0))
  exact this.of_eq <| by intro v; simp [F]

lemma implicit_fun {n} (i : Fin n) (f : List.Vector ℕ n → ℕ → ℕ)
  (hf : Arith₁ (n := n + 1) (fun v => f v.tail v.head)) :
    ArithPart₁ (fun v => Nat.rfind (fun x => Part.some (f v x ≤ v.get i ∧ v.get i < f v (x + 1)))) := by
  let F : List.Vector ℕ (n + 1) → ℕ :=
    fun v => (isLeNat (f v.tail v.head) (v.get i.succ)).and (isLtNat (v.get i.succ) (f v.tail (v.head + 1)))
  have : Arith₁ F :=
    (Arith₁.and 0 1).comp₂ _
      ((Arith₁.le 0 1).comp₂ _ hf (proj i.succ))
      ((Arith₁.lt 0 1).comp₂ _ (proj i.succ)
        (Arith₁.comp' hf (Arith₁.cons
          ((Arith₁.add 0 1).comp₂ _ Arith₁.head one) (fun i => Arith₁.tail (proj i)))))
  have := rfindPos this
  exact this.of_eq <| by intro v; simp [F]

end Nat.ArithPart₁

namespace Nat.Arith₁

protected lemma sqrt {n} (i : Fin n) : Arith₁ (fun v => sqrt (v.get i)) := by
  have := ArithPart₁.implicit_fun i (fun _ x => x * x) ((mul 0 1).comp₂ _ head head)
  exact this.of_eq <| by
    intro v; simp only [Bool.decide_and, PFun.coe_val, eq_some_iff, mem_rfind, mem_some_iff]
    constructor
    · symm; simp; constructor
      · exact sqrt_le (List.Vector.get v i)
      · exact lt_succ_sqrt (List.Vector.get v i)
    · intro m hm; symm
      simp only [Bool.and_eq_false_eq_eq_false_or_eq_false, decide_eq_false_iff_not, not_le, not_lt]
      right; exact Iff.mp le_sqrt hm

lemma sub {n} (i j : Fin n) : Arith₁ (fun v => v.get i - v.get j) := by
  let F : List.Vector ℕ (n + 1) → ℕ := fun v =>
    (isEqNat (v.head + v.get j.succ) (v.get i.succ)).or
    ((isLtNat (v.get i.succ) (v.get j.succ)).and (isEqNat v.head 0))
  have : Arith₁ F :=
    (or 0 1).comp₂ _
      ((equal 0 1).comp₂ _ ((add 0 1).comp₂ _ head (proj j.succ)) (proj i.succ))
      ((and 0 1).comp₂ _ ((lt 0 1).comp₂ _ (proj i.succ) (proj j.succ)) ((equal 0 1).comp₂ _ head zero))
  exact (ArithPart₁.rfindPos this).of_eq <| by
    intro v
    simp only [head_cons, get_cons_succ, or_pos_iff, isEqNat_pos_iff, and_pos_iff,
      isLtNat_pos_iff, Bool.decide_or, Bool.decide_and, PFun.coe_val, eq_some_iff, mem_rfind,
      mem_some_iff, F]
    constructor
    · symm; simp
      have : v.get i < v.get j ∨ v.get j ≤ v.get i := Nat.lt_or_ge _ _
      rcases this with (hv | hv)
      · right; exact ⟨hv, Nat.sub_eq_zero_of_le (Nat.le_of_lt hv)⟩
      · left; exact Nat.sub_add_cancel hv
    · intro m hm; symm
      simp only [Bool.or_eq_false_eq_eq_false_and_eq_false,
        decide_eq_false_iff_not, Bool.and_eq_false_eq_eq_false_or_eq_false, not_lt]
      have : m + v.get j < v.get i := add_lt_of_lt_sub hm
      exact ⟨ne_of_lt this, by left; exact le_trans le_add_self (le_of_lt this)⟩

protected lemma pair {n} (i j : Fin n) : Arith₁ (fun v => (v.get i).pair (v.get j)) := by
  have := if_pos (lt i j)
    ((add 0 1).comp₂ _ (mul j j) (proj i))
    ((add 0 1).comp₂ _ ((add 0 1).comp₂ _ (mul i i) (proj i)) (proj j))
  exact this.of_eq <| by
    intro v; simp[pair]

lemma unpair₁ {n} (i : Fin n) : Arith₁ (fun v => (v.get i).unpair.1) := by
  have hf : Arith₁ (fun v => isLtNat (v.get i - (v.get i).sqrt * (v.get i).sqrt) (v.get i).sqrt) :=
    (lt 0 1).comp₂ _
      ((Arith₁.sub 0 1).comp₂ _ (proj i) ((mul 0 1).comp₂ _ (Arith₁.sqrt i) (Arith₁.sqrt i)))
      (Arith₁.sqrt i)
  have hg : Arith₁ (fun v => v.get i - (v.get i).sqrt * (v.get i).sqrt) :=
    (sub 0 1).comp₂ _ (proj i) ((mul 0 1).comp₂ _ (Arith₁.sqrt i) (Arith₁.sqrt i))
  have hh : Arith₁ (fun v => sqrt (v.get i)) := Arith₁.sqrt i
  have := if_pos hf hg hh
  exact this.of_eq <| by
    intro v; simp[unpair]
    by_cases v.get i - (v.get i).sqrt * (v.get i).sqrt < sqrt (v.get i) <;> simp[*]

lemma unpair₂ {n} (i : Fin n) : Arith₁ (fun v => (v.get i).unpair.2) := by
  have hf : Arith₁ (fun v => isLtNat (v.get i - (v.get i).sqrt * (v.get i).sqrt) (v.get i).sqrt) :=
    (lt 0 1).comp₂ _
      ((Arith₁.sub 0 1).comp₂ _ (proj i) ((mul 0 1).comp₂ _ (Arith₁.sqrt i) (Arith₁.sqrt i)))
      (Arith₁.sqrt i)
  have hg : Arith₁ (fun v => sqrt (v.get i)) := Arith₁.sqrt i
  have hh : Arith₁ (fun v => v.get i - (v.get i).sqrt * (v.get i).sqrt - (v.get i).sqrt) :=
    (sub 0 1).comp₂ _ ((sub 0 1).comp₂ _ (proj i) ((mul 0 1).comp₂ _ (Arith₁.sqrt i) (Arith₁.sqrt i))) (Arith₁.sqrt i)
  have := if_pos hf hg hh
  exact this.of_eq <| by
    intro v; simp[unpair]
    by_cases v.get i - (v.get i).sqrt * (v.get i).sqrt < sqrt (v.get i) <;> simp[*]

lemma dvd (i j : Fin n) : Arith₁ (fun v => isDvdNat (v.get i) (v.get j)) := by
  have hr : @Arith₁ (n + 1) (fun v =>
    (isEqNat (v.head * (v.get i.succ)) (v.get j.succ)).or (isLtNat (v.get j.succ) v.head)) :=
    (or 0 1).comp₂ _
      ((equal 0 1).comp₂ _ ((mul 0 1).comp₂ _ head (proj i.succ)) (proj j.succ))
      ((lt 0 1).comp₂ _ (proj j.succ) head)
  have : @Arith₁ (n + 1) (fun v => isLeNat v.head (v.tail.get j)) :=
    (le 0 1).comp₂ _ head ((proj j.succ).of_eq <| by simp)
  have := ArithPart₁.map (fun v x => isLeNat x (v.get j)) this (ArithPart₁.rfindPos hr)
  exact this.of_eq <| by
    intro v
    simp only [head_cons, get_cons_succ, or_pos_iff, isEqNat_pos_iff, isLtNat_pos_iff,
      Bool.decide_or, isDvdNat, PFun.coe_val, eq_some_iff, mem_map_iff, mem_rfind, mem_some_iff]
    by_cases hv : v.get i ∣ v.get j
    · simp only [hv, ↓reduceIte]
      rcases least_number _ hv with ⟨k, hk, hkm⟩
      have hkvj : k ≤ v.get j := by
        by_cases hkz : k = 0
        · simp[hkz]
        · rw[hk]; exact Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_ne_zero $ fun hvi => by
            simp[hvi] at hk
            have : v.get j ≠ 0 := hkm 0 (Nat.pos_of_ne_zero hkz)
            contradiction)
      refine ⟨k,
        ⟨by symm; simp; left; simp[hk, mul_comm],
         by intro m hm; symm; simp[mul_comm m, Ne.symm (hkm m hm), le_of_lt (lt_of_lt_of_le hm hkvj)]⟩,
        by simp[isLeNat, hkvj]⟩
    · simp only [hv, ↓reduceIte]
      exact ⟨v.get j + 1, ⟨by symm; simp, by
        intro m hm; symm; simp[lt_succ.mp hm]; intro A
        have : v.get i ∣ v.get j := by rw[←A]; exact Nat.dvd_mul_left (List.Vector.get v i) m
        contradiction⟩, by simp [isLeNat]⟩

lemma rem (i j : Fin n) : Arith₁ (fun v => v.get i % v.get j) := by
  let F : List.Vector ℕ (n + 1) → ℕ := fun v => isDvdNat (v.get j.succ) (v.get i.succ - v.head)
  have : Arith₁ F :=
    (dvd 0 1).comp₂ _ (proj j.succ) ((sub 0 1).comp₂ _ (proj i.succ) head)
  exact (ArithPart₁.rfindPos this).of_eq <| by
    intro v; simp [F, Part.eq_some_iff, Nat.dvd_sub_mod]
    intro m hm A
    have hmvi : m < v.get i := lt_of_lt_of_le hm <| Nat.mod_le (v.get i) (v.get j)
    have hsub : v.get j ∣ v.get i % v.get j - m := by
      have : v.get i - m - (v.get i - v.get i % v.get j) = v.get i % v.get j - m := by
        rw[Nat.sub_eq_iff_eq_add (Nat.sub_le_sub_left (le_of_lt hm) _), Nat.sub_eq_iff_eq_add (le_of_lt hmvi),
          ←Nat.sub_add_comm (le_of_lt hm), Nat.add_sub_of_le (Nat.mod_le (v.get i) (v.get j)),
          Nat.sub_add_cancel (le_of_lt hmvi)]
      rw[←this]
      exact Nat.dvd_sub (Nat.sub_le_sub_left (le_of_lt hm) _) A (@Nat.dvd_sub_mod (v.get j) (v.get i))
    have hpos : 0 < v.get i % v.get j - m := Nat.lt_sub_of_add_lt (by simpa using hm)
    have : v.get i % v.get j - m < v.get j := by
      have : v.get i % v.get j < v.get j :=
        Nat.mod_lt _ (Nat.pos_of_ne_zero $ fun h => (Nat.not_lt.mpr (by simpa [Nat.sub_eq_zero_iff_le, h] using hsub)) hmvi)
      exact lt_of_le_of_lt (sub_le _ _) this
    have : ¬v.get j ∣ v.get i % v.get j - m := Nat.not_dvd_of_pos_of_lt hpos this
    contradiction

lemma beta (i j : Fin n) : Arith₁ (fun v => Nat.beta (v.get i) (v.get j)) :=
  (rem 0 1).comp₂ _ ((unpair₁ 0).comp₁ (·.unpair.1) (proj i))
    ((succ 0).comp₁ _ $ (mul 0 1).comp₂ _ (succ j) ((unpair₂ 0).comp₁ (·.unpair.2) (proj i)))

lemma ball {φ : List.Vector ℕ n → ℕ → ℕ} (hp : @Arith₁ (n + 1) (fun v => φ v.tail v.head)) (i) :
    Arith₁ (fun v => ball (v.get i) (φ v)) := by
  let F : List.Vector ℕ (n + 1) → ℕ := fun v => (φ v.tail v.head).inv.or (isLeNat (v.get i.succ) v.head)
  have hF : Arith₁ F := (or 0 1).comp₂ _ ((inv 0).comp₁ _ hp) ((le 0 1).comp₂ _ (proj i.succ) head)
  have : @Arith₁ (n + 1) (fun v => isEqNat v.head (v.get i.succ)) :=
    (equal 0 1).comp₂ _ head (proj i.succ)
  have := ArithPart₁.map (fun v x => isEqNat x (v.get i)) (this.of_eq $ by simp) (ArithPart₁.rfindPos hF)
  exact this.of_eq <| by
    intro v
    simp only [tail_cons, head_cons, get_cons_succ, or_pos_iff, inv_pos_iff, not_lt,
      nonpos_iff_eq_zero, isLeNat_pos_iff, Bool.decide_or, PFun.coe_val, eq_some_iff, mem_map_iff,
      mem_rfind, mem_some_iff, F]
    by_cases H : ∀ m < v.get i, 0 < φ v m
    · exact ⟨v.get i,
        ⟨by symm; simp, by intro m hm; symm; simp[hm]; exact Nat.ne_zero_of_lt (H m hm)⟩,
        by { simp[isEqNat]; symm; exact ball_pos_iff_eq_one.mpr (by simpa) }⟩
    · have : ∃ x < List.Vector.get v i, φ v x = 0 ∧ ∀ y < x, φ v y ≠ 0 := by
        simp at H; rcases least_number _ H with ⟨x, hx, hxl⟩
        exact ⟨x, hx.1, hx.2, by
          intro y hy; have : y < v.get i → φ v y ≠ 0 := by simpa using hxl y hy
          exact this (lt_trans hy hx.1)⟩
      rcases this with ⟨x, hx, hpx, hlx⟩
      exact ⟨x, ⟨by symm; simp[hpx], by intro m hm; symm; simp[hlx m hm, lt_trans hm hx]⟩, by
        have : isEqNat x (v.get i) = 0 := by simp[isEqNat, imp_false]; exact ne_of_lt hx
        simp[this]; symm; simp; exact ⟨x, hx, hpx⟩⟩

def recSequence (f : List.Vector ℕ n → ℕ) (g : List.Vector ℕ (n + 2) → ℕ) (z : ℕ) (v : List.Vector ℕ n) : List ℕ :=
  List.ofFn fun i : Fin (z + 1) => Nat.recOn i (f v) (fun y IH => g (y ::ᵥ IH ::ᵥ v))

lemma beta_unbeta_recSequence_eq (f : List.Vector ℕ n → ℕ) (g : List.Vector ℕ (n + 2) → ℕ) (z : ℕ) (v : List.Vector ℕ n)
  (m : ℕ) (hm : m < z + 1) :
    Nat.beta (unbeta (recSequence f g z v)) m = m.rec (f v) (fun y IH => g (y ::ᵥ IH ::ᵥ v)) := by
  have : (unbeta (recSequence f g z v)).beta m = (recSequence f g z v).get ⟨m, _⟩ :=
    Nat.beta_unbeta_coe (recSequence f g z v) ⟨m, by simp[recSequence, hm]⟩
  rw [this]; simp [List.get_ofFn, recSequence, -List.get_eq_getElem]

lemma beta_unbeta_recSequence_zero (f : List.Vector ℕ n → ℕ) (g : List.Vector ℕ (n + 2) → ℕ) (z : ℕ) (v : List.Vector ℕ n) :
    Nat.beta (unbeta (recSequence f g z v)) 0 = f v := by
  simpa using beta_unbeta_recSequence_eq f g z v 0 (inv_iff_ne_zero.mp rfl)

lemma beta_unbeta_recSequence_succ (f : List.Vector ℕ n → ℕ) (g : List.Vector ℕ (n + 2) → ℕ) (z : ℕ) (v : List.Vector ℕ n)
  {m : ℕ} (hm : m < z) :
    Nat.beta (unbeta (recSequence f g z v)) (m + 1) = g (m ::ᵥ Nat.beta (unbeta (recSequence f g z v)) m ::ᵥ v) := by
  rw [beta_unbeta_recSequence_eq f g z v m (Nat.lt_add_right 1 hm),
    beta_unbeta_recSequence_eq f g z v (m + 1) (Nat.add_lt_add_right hm 1)]

lemma beta_eq_rec (f : List.Vector ℕ n → ℕ) (g : List.Vector ℕ (n + 2) → ℕ) {z : ℕ} {v}
  (h0 : z.beta 0 = f v) (hs : ∀ i < m, z.beta (i + 1) = g (i ::ᵥ z.beta i ::ᵥ v)) :
    z.beta m = m.rec (f v) (fun y IH => g (y ::ᵥ IH ::ᵥ v)) := by
  induction' m with m ih <;> simp[h0]
  · rw[hs m (lt.base m), ←ih (fun i hi => hs i (lt.step hi))]

lemma prec {n f g} (hf : @Arith₁ n f) (hg : @Arith₁ (n + 2) g) :
    @Arith₁ (n + 1) (fun v => v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) := by
  let F : List.Vector ℕ (n + 2) → ℕ := fun v =>
    (isEqNat (Nat.beta v.head 0) (f v.tail.tail)).and
    (Nat.ball v.tail.head $ fun i => isEqNat (Nat.beta v.head (i + 1)) (g (i ::ᵥ Nat.beta v.head i ::ᵥ v.tail.tail)))
  have hp : @Arith₁ (n + 3) (fun v =>
    isEqNat (Nat.beta v.tail.head (v.head + 1))
    (g (v.head ::ᵥ Nat.beta v.tail.head v.head ::ᵥ v.tail.tail.tail))) :=
    (equal 0 1).comp₂ _
      ((beta 0 1).comp₂ _ head.tail ((succ 0).comp₁ _ head))
      (hg.comp' $ head.cons $ ((beta 0 1).comp₂ _ head.tail head).cons $ by intro i; simp; exact proj _)
  have hF : Arith₁ F := (and 0 1).comp₂ _
    ((equal 0 1).comp₂ _ ((beta 0 1).comp₂ _ head zero) hf.tail.tail)
    ((@ball (n + 2) (fun v i =>
      isEqNat (Nat.beta v.head (i + 1)) (g (i ::ᵥ Nat.beta v.head i ::ᵥ v.tail.tail))) hp 1).of_eq $ by
        simp[List.Vector.get_one])
  have : @Arith₁ (n + 2) (fun v => Nat.beta v.head v.tail.head) :=
    (beta 0 1).of_eq (by simp [List.Vector.get_one])
  exact (ArithPart₁.map (fun v x => Nat.beta x v.head) this (ArithPart₁.rfindPos hF)).of_eq <| by
    intro v
    simp only [add_succ_sub_one, head_cons, tail_cons, and_pos_iff, isEqNat_pos_iff,
      ball_pos_iff, Bool.decide_and, PFun.coe_val, eq_some_iff, mem_map_iff, mem_rfind,
      mem_some_iff, F]
    suffices ∃ z : ℕ, z.beta 0 = f v.tail ∧ ∀ i < v.head, z.beta (i + 1) = g (i ::ᵥ z.beta i ::ᵥ v.tail) by
      rcases least_number _ this with ⟨z, ⟨hz0, hzs⟩, hzm⟩
      exact ⟨z, ⟨by symm; simp[hz0]; exact hzs,
        by intro m hm; symm; simpa[imp_iff_not_or, not_or] using hzm m hm⟩,
        beta_eq_rec f g hz0 hzs⟩
    let l : List ℕ := recSequence f g v.head v.tail
    exact ⟨unbeta l,
      beta_unbeta_recSequence_zero f g v.head v.tail,
      fun i hi => beta_unbeta_recSequence_succ f g v.head v.tail hi⟩

lemma of_primrec {f : List.Vector ℕ n → ℕ} (hf : Primrec' f) : Arith₁ f := by
  induction hf
  case zero               => exact zero
  case succ               => exact (@succ 1 0).of_eq (by simp)
  case get i              => exact proj i
  case comp f g _ _ hf hg => exact hf.comp _ hg
  case prec f g _ _ hf hg => exact hf.prec hg

lemma _root_.Nat.ArithPart₁.of_partrec {f : List.Vector ℕ n →. ℕ} (hf : Partrec' f) : ArithPart₁ f := by
  induction hf
  case prim f hf          => exact of_primrec hf
  case comp f g _ _ hf hg => exact hf.comp _ hg
  case rfind f _ hf       => exact ArithPart₁.rfind hf

end Nat.Arith₁

namespace Nat.ArithPart₁

inductive Code : ℕ → Type
  | zero (n) : Code n
  | one (n) : Code n
  | add {n} (i j : Fin n) : Code n
  | mul {n} (i j : Fin n) : Code n
  | proj {n} (i : Fin n) : Code n
  | equal {n} (i j : Fin n) : Code n
  | lt {n} (i j : Fin n) : Code n
  | comp {m n} : Code n → (Fin n → Code m) → Code m
  | rfind {n} : Code (n + 1) → Code n

instance (k) : Inhabited (Code k) := ⟨Code.zero k⟩

inductive Code.eval : {n : ℕ} → Code n → (List.Vector ℕ n →. ℕ) → Prop
  | zero {n} : Code.eval (Code.zero n) (fun _ => 0)
  | one  {n} : Code.eval (Code.one n)  (fun _ => 1)
  | add  {n} (i j : Fin n) : Code.eval (Code.add i j) (fun v => ↑(v.get i + v.get j))
  | mul  {n} (i j : Fin n) : Code.eval (Code.mul i j) (fun v => ↑(v.get i * v.get j))
  | proj {n} (i : Fin n)   : Code.eval (Code.proj i) (fun v => v.get i)
  | equal {n} (i j : Fin n)   : Code.eval (Code.equal i j) (fun v => isEqNat (v.get i) (v.get j))
  | lt {n} (i j : Fin n) : Code.eval (Code.lt i j) (fun v => isLtNat (v.get i) (v.get j))
  | comp {m n} (c : Code n) (d : Fin n → Code m) (f : List.Vector ℕ n →. ℕ) (g : Fin n → (List.Vector ℕ m →. ℕ)) :
      Code.eval c f → (∀ i, Code.eval (d i) (g i)) →
      Code.eval (c.comp d) (fun v => (List.Vector.mOfFn fun i => g i v) >>= f)
  | rfind {n} (c : Code (n + 1)) (f : List.Vector ℕ (n + 1) → ℕ) :
      Code.eval c f → Code.eval c.rfind (fun v => Nat.rfind fun n => Part.some (f (n ::ᵥ v) = 0))

lemma exists_code : ∀ {n : ℕ} {f : List.Vector ℕ n →. ℕ}, ArithPart₁ f → ∃ c : Code n, c.eval f
  | n, _, ArithPart₁.zero                => ⟨Code.zero n, Code.eval.zero⟩
  | n, _, ArithPart₁.one                 => ⟨Code.one n, Code.eval.one⟩
  | _, _, ArithPart₁.add i j             => ⟨Code.add i j, Code.eval.add i j⟩
  | _, _, ArithPart₁.mul i j             => ⟨Code.mul i j, Code.eval.mul i j⟩
  | _, _, ArithPart₁.proj i              => ⟨Code.proj i, Code.eval.proj i⟩
  | _, _, ArithPart₁.equal i j           => ⟨Code.equal i j, Code.eval.equal i j⟩
  | _, _, ArithPart₁.lt i j              => ⟨Code.lt i j, Code.eval.lt i j⟩
  | _, _, @ArithPart₁.comp _ _ f g hf hg => by
    rcases exists_code hf with ⟨cf, hcf⟩
    choose cg hcg using fun i            => exists_code (hg i)
    exact ⟨cf.comp cg, Code.eval.comp cf cg f g hcf hcg⟩
  | _, _, @ArithPart₁.rfind _ f hf       => by
    rcases exists_code hf with ⟨cf, hcf⟩
    exact ⟨cf.rfind, Code.eval.rfind cf f hcf⟩

end Nat.ArithPart₁
