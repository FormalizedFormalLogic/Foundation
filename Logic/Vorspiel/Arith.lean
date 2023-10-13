import Logic.Vorspiel.Vorspiel
import Mathlib.Computability.Halting

open Vector Part

namespace Nat

def beta (n m i : ℕ) := n % ((i + 1) * m + 1)

end Nat

namespace Nat

def isEqNat (n m : ℕ) : ℕ := if n = m then 1 else 0

def isLtNat (n m : ℕ) : ℕ := if n < m then 1 else 0

def isLeNat (n m : ℕ) : ℕ := if n ≤ m then 1 else 0

@[simp] lemma isEqNat_pos_iff : 0 < isEqNat n m ↔ n = m := by simp[isEqNat]; by_cases n = m <;> simp[*]

@[simp] lemma isLtNat_pos_iff : 0 < isLtNat n m ↔ n < m := by simp[isLtNat]; by_cases n < m <;> simp[*]

@[simp] lemma isLeNat_pos_iff : 0 < isLeNat n m ↔ n ≤ m := by simp[isLeNat]; by_cases n ≤ m <;> simp[*]

def inv (n : ℕ) : ℕ := isEqNat n 0

def pos (n : ℕ) : ℕ := isLtNat 0 n

@[simp] lemma inv_zero : inv 0 = 1 := rfl

@[simp] lemma inv_iff_ne_zero : inv n = 0 ↔ 0 < n := by simp[inv, isEqNat, zero_lt_iff]

@[simp] lemma inv_ne_zero (h : n ≠ 0) : inv n = 0 := by simp[inv, isEqNat, h]

@[simp] lemma pos_zero : pos 0 = 0 := rfl

@[simp] lemma pos_ne_zero (h : n ≠ 0) : pos n = 1 := by simp[pos, isLtNat, h]

def and (n m : ℕ) : ℕ := isLtNat 0 (n * m)

def or (n m : ℕ) : ℕ := isLtNat 0 (n + m)

lemma and_eq (n m : ℕ) : and n m = if 0 < n ∧ 0 < m then 1 else 0 := by simp[and, isLtNat]

lemma or_eq (n m : ℕ) : or n m = if 0 < n ∨ 0 < m then 1 else 0 := by simp[or, isLtNat]

@[simp] lemma and_pos_iff (n m : ℕ) : 0 < and n m ↔ 0 < n ∧ 0 < m := by simp[and_eq]; by_cases 0 < n ∧ 0 < m <;> simp[*]

@[simp] lemma or_pos_iff (n m : ℕ) : 0 < or n m ↔ 0 < n ∨ 0 < m := by simp[or_eq]; by_cases 0 < n ∨ 0 < m <;> simp[*]

@[simp] lemma inv_pos_iff (n : ℕ) : 0 < inv n ↔ ¬0 < n := by simp[inv]

@[simp] lemma pos_pos_iff (n : ℕ) : 0 < pos n ↔ 0 < n := by simp[pos]

inductive ArithPart₁ : ∀ {n}, (Vector ℕ n →. ℕ) → Prop
  | zero {n} : @ArithPart₁ n (fun _ => 0)
  | one {n} : @ArithPart₁ n (fun _ => 1)
  | add {n} (i j : Fin n) : @ArithPart₁ n (fun v => v.get i + v.get j : Vector ℕ n → ℕ)
  | mul {n} (i j : Fin n) : @ArithPart₁ n (fun v => v.get i * v.get j : Vector ℕ n → ℕ)
  | proj {n} (i : Fin n) : @ArithPart₁ n (fun v => v.get i : Vector ℕ n → ℕ)
  | equal {n} (i j : Fin n) : @ArithPart₁ n (fun v => isEqNat (v.get i) (v.get j) : Vector ℕ n → ℕ)
  | lt {n} (i j : Fin n) : @ArithPart₁ n (fun v => isLtNat (v.get i) (v.get j) : Vector ℕ n → ℕ)
  | comp {m n f} (g : Fin n → Vector ℕ m →. ℕ) :
    ArithPart₁ f → (∀ i, ArithPart₁ (g i)) → ArithPart₁ fun v => (mOfFn fun i => g i v) >>= f
  | rfind {n} {f : Vector ℕ (n + 1) → ℕ} :
    ArithPart₁ (n := n + 1) f → ArithPart₁ (fun v => rfind fun n => some (f (n ::ᵥ v) = 0))

def Arith₁ (f : Vector ℕ n → ℕ) := ArithPart₁ (n := n) f

end Nat

namespace Nat.ArithPart₁

open Primrec

lemma to_partrec' {n} {f : Vector ℕ n →. ℕ} (hf : ArithPart₁ f) : Partrec' f := by
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
    have : Primrec (fun (v : Vector ℕ n) => if v.get i = v.get j then 1 else 0) :=
      Primrec.ite
        (Primrec.eq.comp
          (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const i))
          (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const j)))
        (_root_.Primrec.const 1)
        (_root_.Primrec.const 0)
    exact Partrec'.of_part this.to_comp.partrec
  case lt n i j =>
    have : Primrec (fun (v : Vector ℕ n) => if v.get i < v.get j then 1 else 0) :=
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

lemma of_eq {n} {f g : Vector ℕ n →. ℕ} (hf : ArithPart₁ f) (H : ∀ i, f i = g i) : ArithPart₁ g :=
  (funext H : f = g) ▸ hf

lemma comp₁ (f : ℕ →. ℕ) (hf : @ArithPart₁ 1 fun v => f (v.get 0)) {n g} (hg : @Arith₁ n g) :
    @ArithPart₁ n fun v => f (g v) :=
  (hf.comp _ fun _ => hg).of_eq (by simp)

lemma comp₂ (f : ℕ → ℕ →. ℕ) (hf : @ArithPart₁ 2 fun v => f (v.get 0) (v.get 1)) {n g h} (hg : @Arith₁ n g) (hh : @Arith₁ n h) :
    @ArithPart₁ n fun v => f (g v) (h v) :=
  (hf.comp ![g, h] (fun i => i.cases hg (fun i => by simpa using hh))).of_eq
    (by intro i
        have : (fun j => (![↑g, h] : Fin 2 → Vector ℕ n →. ℕ) j i) = (fun j => pure (![g i, h i] j)) := by
          funext j; cases j using Fin.cases <;> simp[Fin.eq_zero]
        simp[Matrix.comp_vecCons']; simp[this] )

lemma rfind' {n} {f : ℕ → Vector ℕ n → ℕ} (h : Arith₁ (n := n + 1) (fun v => f v.head v.tail)) :
    ArithPart₁ (fun v => Nat.rfind fun n => Part.some (f n v = 0)) := rfind h

lemma rfind'₁ {n} (i : Fin n) {f : ℕ → ℕ → ℕ} (h : Arith₁ (n := 2) (fun v => f (v.get 0) (v.get 1))) :
    ArithPart₁ (fun v => Nat.rfind fun n => Part.some (f n (v.get i) = 0)) :=
  (rfind h).comp₁ (fun m => Nat.rfind fun n => Part.some (f n m = 0)) (proj i)

end Nat.ArithPart₁

namespace Nat.Arith₁

lemma of_eq {n} {f g : Vector ℕ n → ℕ} (hf : Arith₁ f) (H : ∀ i, f i = g i) : Arith₁ g :=
  (funext H : f = g) ▸ hf

lemma zero {n} : @Arith₁ n (fun _ => 0 : Vector ℕ n → ℕ) := Nat.ArithPart₁.zero

lemma one {n} : @Arith₁ n (fun _ => 1 : Vector ℕ n → ℕ) := Nat.ArithPart₁.one

lemma add {n} (i j : Fin n) : @Arith₁ n (fun v => v.get i + v.get j) := Nat.ArithPart₁.add i j

lemma mul {n} (i j : Fin n) : @Arith₁ n (fun v => v.get i * v.get j) := Nat.ArithPart₁.mul i j

lemma proj {n} (i : Fin n) : @Arith₁ n (fun v => v.get i) := Nat.ArithPart₁.proj i

lemma head {n} : @Arith₁ (n + 1) (fun v => v.head) := (Nat.ArithPart₁.proj 0).of_eq <| by simp

lemma equal {n} (i j : Fin n) : @Arith₁ n (fun v => isEqNat (v.get i) (v.get j)) := Nat.ArithPart₁.equal i j

lemma lt {n} (i j : Fin n) : @Arith₁ n (fun v => isLtNat (v.get i) (v.get j)) := Nat.ArithPart₁.lt i j

lemma comp {m n f} (g : Fin n → Vector ℕ m → ℕ) (hf : Arith₁ f) (hg : ∀ i, Arith₁ (g i)) :
    Arith₁ fun v => f (Vector.ofFn fun i => g i v) :=
  (Nat.ArithPart₁.comp (fun i => g i : Fin n → Vector ℕ m →. ℕ) hf hg).of_eq <| by simp
  
def Vec {n m} (f : Vector ℕ n → Vector ℕ m) : Prop := ∀ i, Arith₁ fun v => (f v).get i

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

lemma if_pos {n} {f g h : Vector ℕ n → ℕ} (hf : Arith₁ f) (hg : Arith₁ g) (hh : Arith₁ h) :
    Arith₁ (fun v => if 0 < f v then g v else h v) := by
  have : Arith₁ (fun v => (f v).pos * (g v) + (f v).inv * (h v)) :=
    (add 0 1).comp₂ _
      ((mul 0 1).comp₂ _ ((pos 0).comp₁ _ hf) hg)
      ((mul 0 1).comp₂ _ ((inv 0).comp₁ _ hf) hh)
  exact this.of_eq <| by
    intro i; by_cases hf : f i = 0 <;> simp[hf, zero_lt_iff]

lemma to_arith₁ {f : Vector ℕ n → ℕ} (h : Arith₁ f) : @ArithPart₁ n (fun x => f x) := h

end Nat.Arith₁

namespace Nat.ArithPart₁

lemma rfindPos {n} {f : Vector ℕ (n + 1) → ℕ} (h : Arith₁ f) :
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
  exact this.of_eq <| by intro v; simp

lemma implicit_fun {n} (i : Fin n) (f : Vector ℕ n → ℕ → ℕ)
  (hf : Arith₁ (n := n + 1) (fun v => f v.tail v.head)) :
    ArithPart₁ (fun v => Nat.rfind (fun x => Part.some (f v x ≤ v.get i ∧ v.get i < f v (x + 1)))) := by
  let F : Vector ℕ (n + 1) → ℕ :=
    fun v => (isLeNat (f v.tail v.head) (v.get i.succ)).and (isLtNat (v.get i.succ) (f v.tail (v.head + 1)))
  have : Arith₁ F :=
    (Arith₁.and 0 1).comp₂ _
      ((Arith₁.le 0 1).comp₂ _ hf (proj i.succ))
      ((Arith₁.lt 0 1).comp₂ _ (proj i.succ)
        (Arith₁.comp' hf (Arith₁.cons
          ((Arith₁.add 0 1).comp₂ _ Arith₁.head one) (fun i => Arith₁.tail (proj i)))))
  have := rfindPos this
  exact this.of_eq <| by { intro v; simp }

end Nat.ArithPart₁

namespace Nat.Arith₁

protected lemma sqrt {n} (i : Fin n) : Arith₁ (fun v => sqrt (v.get i)) := by
  have := ArithPart₁.implicit_fun i (fun _ x => x * x) ((mul 0 1).comp₂ _ head head)
  exact this.of_eq <| by
    intro v; simp[Part.eq_some_iff]
    constructor
    · symm; simp; constructor
      · exact sqrt_le (Vector.get v i)
      · exact lt_succ_sqrt (Vector.get v i)
    · intro m hm; symm; simp
      right; exact Iff.mp le_sqrt hm

lemma sub {n} (i j : Fin n) : Arith₁ (fun v => v.get i - v.get j) := by
  let F : Vector ℕ (n + 1) → ℕ := fun v =>
    (isEqNat (v.head + v.get j.succ) (v.get i.succ)).or
    ((isLtNat (v.get i.succ) (v.get j.succ)).and (isEqNat v.head 0))
  have : Arith₁ F :=
    (or 0 1).comp₂ _
      ((equal 0 1).comp₂ _ ((add 0 1).comp₂ _ head (proj j.succ)) (proj i.succ))
      ((and 0 1).comp₂ _ ((lt 0 1).comp₂ _ (proj i.succ) (proj j.succ)) ((equal 0 1).comp₂ _ head zero))
  exact (ArithPart₁.rfindPos this).of_eq <| by
    intro v; simp[Part.eq_some_iff]
    constructor
    · symm; simp
      have : v.get i < v.get j ∨ v.get j ≤ v.get i := Nat.lt_or_ge _ _
      rcases this with (hv | hv)
      · right; exact ⟨hv, Nat.le_of_lt hv⟩
      · left; exact Nat.sub_add_cancel hv
    · intro m hm; symm; simp
      have : m + v.get j < v.get i := add_lt_of_lt_sub hm
      exact ⟨ne_of_lt this, by left; exact le_trans le_add_self (le_of_lt this)⟩

protected lemma pair {n} (i j : Fin n) : Arith₁ (fun v => (v.get i).pair (v.get j)) := by
  have := if_pos (lt i j)
    ((add 0 1).comp₂ _ (mul j j) (proj i))
    ((add 0 1).comp₂ _ ((add 0 1).comp₂ _ (mul i i) (proj i)) (proj j))
  exact this.of_eq <| by
    intro v; simp[pair]

lemma nat_unpair₁ {n} (i : Fin n) : Arith₁ (fun v => (v.get i).unpair.1) := by
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

lemma nat_unpair₂ {n} (i : Fin n) : Arith₁ (fun v => (v.get i).unpair.2) := by
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

end Nat.Arith₁