import Logic.Vorspiel.Vorspiel
import Mathlib.Computability.Halting
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime

open Vector Part

namespace Nat

lemma mod_eq_of_modEq {a b n} (h : a ≡ b [MOD n]) (hb : b < n) : a % n = b := by
  have : a % n = b % n := h
  simp[this]; exact mod_eq_of_lt hb

lemma coprime_list_prod_iff_right {k} {l : List ℕ} :
    coprime k l.prod ↔ ∀ n ∈ l, coprime k n := by
  induction' l with m l ih <;> simp[Nat.coprime_mul_iff_right, *]

inductive Coprimes : List ℕ → Prop
  | nil : Coprimes []
  | cons {n : ℕ} {l : List ℕ} : (∀ m ∈ l, coprime n m) → Coprimes l → Coprimes (n :: l)

lemma coprimes_of_nodup {l : List ℕ} (hl : l.Nodup) (H : ∀ n ∈ l, ∀ m ∈ l, n ≠ m → coprime n m) :
    Coprimes l := by
  induction' l with n l ih
  · exact Coprimes.nil
  · have : Coprimes l := ih (List.Nodup.of_cons hl) (fun m hm k hk => H m (by simp[hm]) k (by simp[hk]))
    exact Coprimes.cons (fun m hm => coprime_comm.mp
      (H m (by simp[hm]) n (by simp) (by rintro rfl; exact (List.nodup_cons.mp hl).1 hm))) this

lemma coprimes_cons_iff_coprimes_coprime_prod {n} {l : List ℕ} :
    Coprimes (n :: l) ↔ Coprimes l ∧ coprime n l.prod := by
  simp[coprime_list_prod_iff_right]; constructor
  · rintro ⟨⟩ ; simpa[*]
  · rintro ⟨hl, hn⟩; exact Coprimes.cons hn hl

lemma modEq_iff_modEq_list_prod {a b} {l : List ℕ} (co : Coprimes l) :
    (∀ i, a ≡ b [MOD l.get i]) ↔ a ≡ b [MOD l.prod] := by
  induction' l with m l ih <;> simp[Nat.modEq_one]
  · intro i; exact Fin.elim0 i
  · rcases co with (_ | ⟨hm, hl⟩)
    have : a ≡ b [MOD m] ∧ a ≡ b [MOD l.prod] ↔ a ≡ b [MOD m * l.prod] :=
      Nat.modEq_and_modEq_iff_modEq_mul (coprime_list_prod_iff_right.mpr hm)
    simp[←this, ←ih hl]
    constructor
    · intro h; exact ⟨by simpa using h ⟨0, by simp⟩, fun i => by simpa using h i.succ⟩
    · intro h i
      cases i using Fin.cases
      · simpa using h.1
      · simpa using h.2 _

def chineseRemainderList : (l : List (ℕ × ℕ)) → (H : Coprimes (l.map Prod.snd)) →
    { k // ∀ i, k ≡ (l.get i).1 [MOD (l.get i).2] }
  | [],          _ => ⟨0, by simp⟩
  | (a, m) :: l, H => by
    have hl : Coprimes (l.map Prod.snd) ∧ coprime m (l.map Prod.snd).prod :=
      coprimes_cons_iff_coprimes_coprime_prod.mp H
    let ih : { k // ∀ i, k ≡ (l.get i).1 [MOD (l.get i).2] } := chineseRemainderList l hl.1
    let z := Nat.chineseRemainder hl.2 a ih
    exact ⟨z, by
      intro i; cases' i using Fin.cases with i <;> simp
      · exact z.prop.1
      · have : z ≡ ih [MOD (l.get i).2] := by
          simpa using (modEq_iff_modEq_list_prod hl.1).mpr z.prop.2 (i.cast $ by simp)
        have : z ≡ (l.get i).1 [MOD (l.get i).2] := Nat.ModEq.trans this (ih.prop i)
        exact this⟩

def listSup (l : List ℕ) := max l.length l.sup + 1

def coprimeList (l : List ℕ) : List (ℕ × ℕ) :=
  List.ofFn (fun i : Fin l.length => (l.get i, (i + 1) * (listSup l)! + 1))

@[simp] lemma coprimeList_length (l : List ℕ) : (coprimeList l).length = l.length := by simp[coprimeList]

private lemma coprimeList_lt (l : List ℕ) (i) : ((coprimeList l).get i).1 < ((coprimeList l).get i).2 := by
  have h₁ : l.get (i.cast $ by simp[coprimeList]) < listSup l :=
    Nat.lt_add_one_iff.mpr (by simp; right; exact List.le_sup (by apply List.get_mem))
  have h₂ : Nat.listSup l ≤ (i + 1) * (Nat.listSup l)! + 1 := calc
    Nat.listSup l ≤ (Nat.listSup l)!               := self_le_factorial _
    _             ≤ (i + 1) * (Nat.listSup l)!     := Nat.le_mul_of_pos_left (succ_pos _)
    _             ≤ (i + 1) * (Nat.listSup l)! + 1 := le_add_right _ _
  simpa only [coprimeList, List.get_ofFn] using lt_of_lt_of_le h₁ h₂

lemma coprime_mul_succ {n m a} (h : n ≤ m) (ha : m - n ∣ a) : coprime (n * a + 1) (m * a + 1) :=
  Nat.coprime_of_dvd (by
    intro p pp hn hm
    have : p ∣ (m - n) * a := by
      simpa [Nat.succ_sub_succ, ←Nat.mul_sub_right_distrib] using
        Nat.dvd_sub (Nat.succ_le_succ $ Nat.mul_le_mul_right a h) hm hn
    have : p ∣ a := by
      rcases (Nat.Prime.dvd_mul pp).mp this with (hp | hp)
      · exact Nat.dvd_trans hp ha
      · exact hp
    have : p = 1 := by
      simpa[Nat.add_sub_cancel_left] using Nat.dvd_sub (le_add_right _ _) hn (Dvd.dvd.mul_left this n)
    simp[this] at pp)

lemma coprimes_coprimeList (l : List ℕ) : Coprimes ((coprimeList l).map Prod.snd) := by
  have : (coprimeList l).map Prod.snd = List.ofFn (fun i : Fin l.length => (i + 1) * (listSup l)! + 1) := by
    simp[coprimeList, Function.comp]
  rw[this]
  exact coprimes_of_nodup
    (List.nodup_ofFn_ofInjective $ by
       intro i j; simp[listSup, ←Fin.ext_iff, Nat.factorial_ne_zero])
    (by
      simp[←Fin.ext_iff, not_or]
      suffices : ∀ i j : Fin l.length, i < j → coprime ((i + 1) * (listSup l)! + 1) ((j + 1) * (listSup l)! + 1)
      · intro i j hij _
        have : i < j ∨ j < i := Ne.lt_or_lt hij; rcases this with (hij | hij)
        · exact this i j hij
        · exact coprime_comm.mp (this j i hij)
      intro i j hij
      have hjl : j < listSup l := lt_of_lt_of_le j.prop (le_step (le_max_left l.length l.sup))
      apply coprime_mul_succ
        (Nat.succ_le_succ $ le_of_lt hij)
        (Nat.dvd_factorial (by simp[Nat.succ_sub_succ, hij]) (by
          simpa only [Nat.succ_sub_succ] using le_of_lt (lt_of_le_of_lt (sub_le j i) hjl))))

def beta (n i : ℕ) := n.unpair.1 % ((i + 1) * n.unpair.2 + 1)

lemma beta_function_lemma (l : List ℕ) (i : Fin l.length) :
    beta ((chineseRemainderList (coprimeList l) (coprimes_coprimeList l) : ℕ).pair (listSup l)!) i = l.get i := by
  simpa[beta, coprimeList] using mod_eq_of_modEq
    ((chineseRemainderList (coprimeList l) (coprimes_coprimeList l)).2 (i.cast $ by simp))
    (coprimeList_lt l _)

end Nat

namespace Nat

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

lemma bind (f : Vector ℕ n → ℕ →. ℕ) (hf : @ArithPart₁ (n + 1) fun v => f v.tail v.head) {g} (hg : @ArithPart₁ n g) :
    @ArithPart₁ n fun v => (g v).bind (f v) :=
  (hf.comp (g :> fun i v => v.get i) (fun i => by cases i using Fin.cases <;> simp[*]; exact proj _)).of_eq (by
    intro v; simp
    rcases Part.eq_none_or_eq_some (g v) with (hgv | ⟨x, hgv⟩)
    · simp[hgv, mOfFn]
    · simp[hgv, Matrix.comp_vecCons']
      have : mOfFn (fun i => (g :> fun j v => Part.some $ v.get j) i v) = pure (Vector.ofFn (x :> fun j => v.get j)) := by
        rw[←Vector.mOfFn_pure]; apply congr_arg
        funext i; cases i using Fin.cases <;> simp[hgv]
      simp[this])

lemma map (f : Vector ℕ n → ℕ → ℕ) (hf : @Arith₁ (n + 1) fun v => f v.tail v.head) {g} (hg : @ArithPart₁ n g) :
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
    intro v; simp[isDvdNat, Part.eq_some_iff]
    by_cases hv : v.get i ∣ v.get j <;> simp[hv]
    · rcases least_number _ hv with ⟨k, hk, hkm⟩
      have hkvj : k ≤ v.get j := by
        by_cases hkz : k = 0
        · simp[hkz]
        · rw[hk]; exact Nat.le_mul_of_pos_left (Nat.zero_lt_of_ne_zero $ fun hvi => by
            simp[hvi] at hk
            have : v.get j ≠ 0 := hkm 0 (Nat.pos_of_ne_zero hkz)
            contradiction)
      refine ⟨k,
        ⟨by symm; simp; left; simp[hk, mul_comm],
         by intro m hm; symm; simp[mul_comm m, Ne.symm (hkm m hm), le_of_lt (lt_of_lt_of_le hm hkvj)]⟩,
        by simp[isLeNat]; exact not_lt.mpr hkvj⟩
    · exact ⟨v.get j + 1, ⟨by symm; simp, by
        intro m hm; symm; simp[lt_succ.mp hm]; intro A
        have : v.get i ∣ v.get j := by rw[←A]; exact Nat.dvd_mul_left (Vector.get v i) m
        contradiction⟩, by simp[isLeNat]⟩

lemma rem (i j : Fin n) : Arith₁ (fun v => v.get i % v.get j) := by
  let F : Vector ℕ (n + 1) → ℕ := fun v => isDvdNat (v.get j.succ) (v.get i.succ - v.head)
  have : Arith₁ F :=
    (dvd 0 1).comp₂ _ (proj j.succ) ((sub 0 1).comp₂ _ (proj i.succ) head)
  exact (ArithPart₁.rfindPos this).of_eq <| by
    intro v; simp[Part.eq_some_iff, Nat.dvd_sub_mod]
    intro m hm A
    have hmvi : m < v.get i := lt_of_lt_of_le hm <| Nat.mod_le (v.get i) (v.get j)
    have hsub : v.get j ∣ v.get i % v.get j - m := by
      have : v.get i - m - (v.get i - v.get i % v.get j) = v.get i % v.get j - m := by
        rw[Nat.sub_eq_iff_eq_add (Nat.sub_le_sub_left _ (le_of_lt hm)), Nat.sub_eq_iff_eq_add (le_of_lt hmvi),
          ←Nat.sub_add_comm (le_of_lt hm), Nat.add_sub_of_le (Nat.mod_le (v.get i) (v.get j)),
          Nat.sub_add_cancel (le_of_lt hmvi)]
      rw[←this]
      exact Nat.dvd_sub (Nat.sub_le_sub_left _ (le_of_lt hm)) A (@Nat.dvd_sub_mod (v.get j) (v.get i))
    have hpos : 0 < v.get i % v.get j - m := Nat.lt_sub_of_add_lt (by simpa using hm)
    have : v.get i % v.get j - m < v.get j := by
      have : v.get i % v.get j < v.get j :=
        Nat.mod_lt _ (Nat.pos_of_ne_zero $ fun h => (Nat.not_lt.mpr (by simpa[h] using hsub)) hmvi)
      exact lt_of_le_of_lt (sub_le _ _) this
    have : ¬v.get j ∣ v.get i % v.get j - m := Nat.not_dvd_of_pos_of_lt hpos this
    contradiction

end Nat.Arith₁