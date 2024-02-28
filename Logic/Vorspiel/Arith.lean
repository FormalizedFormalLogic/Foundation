--import Logic.Vorspiel.Vorspiel
import Logic.Vorspiel.GodelBetaFunction
import Logic.Vorspiel.PartArith
import Mathlib.Computability.Halting
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime

open Vector Part

namespace Nat.Arith

lemma least_number (P : ℕ → Prop) (hP : ∃ x, P x) : ∃ x, P x ∧ ∀ z < x, ¬P z := by
  rcases hP with ⟨n, hn⟩
  induction' n using Nat.strongRec with n ih
  by_cases H : ∃ m < n, P m
  · rcases H with ⟨m, hm, hPm⟩
    exact ih m hm hPm
  · exact ⟨n, hn, by simpa using H⟩

protected lemma sqrt {n} (i : Fin n) : Arith (fun v => sqrt (v.get i)) := by
  have := PartArith.implicit_fun i (fun _ x => x * x) ((mul 0 1).comp₂ _ head head)
  exact this.of_eq <| by
    intro v; simp[Part.eq_some_iff]
    constructor
    · symm; simp; constructor
      · exact sqrt_le (Vector.get v i)
      · exact lt_succ_sqrt (Vector.get v i)
    · intro m hm; symm; simp
      right; exact Iff.mp le_sqrt hm

lemma sub {n} (i j : Fin n) : Arith (fun v => v.get i - v.get j) := by
  let F : Vector ℕ (n + 1) → ℕ := fun v =>
    (isEqNat (v.head + v.get j.succ) (v.get i.succ)).or
    ((isLtNat (v.get i.succ) (v.get j.succ)).and (isEqNat v.head 0))
  have : Arith F :=
    (or 0 1).comp₂ _
      ((equal 0 1).comp₂ _ ((add 0 1).comp₂ _ head (proj j.succ)) (proj i.succ))
      ((and 0 1).comp₂ _ ((lt 0 1).comp₂ _ (proj i.succ) (proj j.succ)) ((equal 0 1).comp₂ _ head zero))
  exact (PartArith.rfindPos this).of_eq <| by
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

protected lemma pair {n} (i j : Fin n) : Arith (fun v => (v.get i).pair (v.get j)) := by
  have := if_pos (lt i j)
    ((add 0 1).comp₂ _ (mul j j) (proj i))
    ((add 0 1).comp₂ _ ((add 0 1).comp₂ _ (mul i i) (proj i)) (proj j))
  exact this.of_eq <| by
    intro v; simp[pair]

lemma unpair₁ {n} (i : Fin n) : Arith (fun v => (v.get i).unpair.1) := by
  have hf : Arith (fun v => isLtNat (v.get i - (v.get i).sqrt * (v.get i).sqrt) (v.get i).sqrt) :=
    (lt 0 1).comp₂ _
      ((Arith.sub 0 1).comp₂ _ (proj i) ((mul 0 1).comp₂ _ (Arith.sqrt i) (Arith.sqrt i)))
      (Arith.sqrt i)
  have hg : Arith (fun v => v.get i - (v.get i).sqrt * (v.get i).sqrt) :=
    (sub 0 1).comp₂ _ (proj i) ((mul 0 1).comp₂ _ (Arith.sqrt i) (Arith.sqrt i))
  have hh : Arith (fun v => sqrt (v.get i)) := Arith.sqrt i
  have := if_pos hf hg hh
  exact this.of_eq <| by
    intro v; simp[unpair]
    by_cases v.get i - (v.get i).sqrt * (v.get i).sqrt < sqrt (v.get i) <;> simp[*]

lemma unpair₂ {n} (i : Fin n) : Arith (fun v => (v.get i).unpair.2) := by
  have hf : Arith (fun v => isLtNat (v.get i - (v.get i).sqrt * (v.get i).sqrt) (v.get i).sqrt) :=
    (lt 0 1).comp₂ _
      ((Arith.sub 0 1).comp₂ _ (proj i) ((mul 0 1).comp₂ _ (Arith.sqrt i) (Arith.sqrt i)))
      (Arith.sqrt i)
  have hg : Arith (fun v => sqrt (v.get i)) := Arith.sqrt i
  have hh : Arith (fun v => v.get i - (v.get i).sqrt * (v.get i).sqrt - (v.get i).sqrt) :=
    (sub 0 1).comp₂ _ ((sub 0 1).comp₂ _ (proj i) ((mul 0 1).comp₂ _ (Arith.sqrt i) (Arith.sqrt i))) (Arith.sqrt i)
  have := if_pos hf hg hh
  exact this.of_eq <| by
    intro v; simp[unpair]
    by_cases v.get i - (v.get i).sqrt * (v.get i).sqrt < sqrt (v.get i) <;> simp[*]

lemma dvd (i j : Fin n) : Arith (fun v => isDvdNat (v.get i) (v.get j)) := by
  have hr : @Arith (n + 1) (fun v =>
    (isEqNat (v.head * (v.get i.succ)) (v.get j.succ)).or (isLtNat (v.get j.succ) v.head)) :=
    (or 0 1).comp₂ _
      ((equal 0 1).comp₂ _ ((mul 0 1).comp₂ _ head (proj i.succ)) (proj j.succ))
      ((lt 0 1).comp₂ _ (proj j.succ) head)
  have : @Arith (n + 1) (fun v => isLeNat v.head (v.tail.get j)) :=
    (le 0 1).comp₂ _ head ((proj j.succ).of_eq <| by simp)
  have := PartArith.map (fun v x => isLeNat x (v.get j)) this (PartArith.rfindPos hr)
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
        by simp[isLeNat, hkvj]⟩
    · exact ⟨v.get j + 1, ⟨by symm; simp, by
        intro m hm; symm; simp[lt_succ.mp hm]; intro A
        have : v.get i ∣ v.get j := by rw[←A]; exact Nat.dvd_mul_left (Vector.get v i) m
        contradiction⟩, by simp[isLeNat]⟩

lemma rem (i j : Fin n) : Arith (fun v => v.get i % v.get j) := by
  let F : Vector ℕ (n + 1) → ℕ := fun v => isDvdNat (v.get j.succ) (v.get i.succ - v.head)
  have : Arith F :=
    (dvd 0 1).comp₂ _ (proj j.succ) ((sub 0 1).comp₂ _ (proj i.succ) head)
  exact (PartArith.rfindPos this).of_eq <| by
    intro v; simp[Part.eq_some_iff, Nat.dvd_sub_mod]
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
        Nat.mod_lt _ (Nat.pos_of_ne_zero $ fun h => (Nat.not_lt.mpr (by simpa[h] using hsub)) hmvi)
      exact lt_of_le_of_lt (sub_le _ _) this
    have : ¬v.get j ∣ v.get i % v.get j - m := Nat.not_dvd_of_pos_of_lt hpos this
    contradiction

lemma beta (i j : Fin n) : Arith (fun v => Nat.beta (v.get i) (v.get j)) :=
  (rem 0 1).comp₂ _ ((unpair₁ 0).comp₁ (·.unpair.1) (proj i))
    ((succ 0).comp₁ _ $ (mul 0 1).comp₂ _ (succ j) ((unpair₂ 0).comp₁ (·.unpair.2) (proj i)))

lemma ball {p : Vector ℕ n → ℕ → ℕ} (hp : @Arith (n + 1) (fun v => p v.tail v.head)) (i) :
    Arith (fun v => ball (v.get i) (p v)) := by
  let F : Vector ℕ (n + 1) → ℕ := fun v => (p v.tail v.head).inv.or (isLeNat (v.get i.succ) v.head)
  have hF : Arith F := (or 0 1).comp₂ _ ((inv 0).comp₁ _ hp) ((le 0 1).comp₂ _ (proj i.succ) head)
  have : @Arith (n + 1) (fun v => isEqNat v.head (v.get i.succ)) :=
    (equal 0 1).comp₂ _ head (proj i.succ)
  have := PartArith.map (fun v x => isEqNat x (v.get i)) (this.of_eq $ by simp) (PartArith.rfindPos hF)
  exact this.of_eq <| by
    intro v; simp[Part.eq_some_iff]
    by_cases H : ∀ m < v.get i, 0 < p v m
    · exact ⟨v.get i,
        ⟨by symm; simp, by intro m hm; symm; simp[hm]; exact Nat.not_eq_zero_of_lt (H m hm)⟩,
        by { simp[isEqNat]; symm; exact ball_pos_iff_eq_one.mpr (by simpa) }⟩
    · have : ∃ x < Vector.get v i, p v x = 0 ∧ ∀ y < x, p v y ≠ 0 := by
        simp at H; rcases least_number _ H with ⟨x, hx, hxl⟩
        exact ⟨x, hx.1, hx.2, by
          intro y hy; have : y < v.get i → p v y ≠ 0 := by simpa using hxl y hy
          exact this (lt_trans hy hx.1)⟩
      rcases this with ⟨x, hx, hpx, hlx⟩
      exact ⟨x, ⟨by symm; simp[hpx], by intro m hm; symm; simp[hlx m hm, lt_trans hm hx]⟩, by
        have : isEqNat x (v.get i) = 0 := by simp[isEqNat, imp_false]; exact ne_of_lt hx
        simp[this]; symm; simp; exact ⟨x, hx, hpx⟩⟩

def recSequence (f : Vector ℕ n → ℕ) (g : Vector ℕ (n + 2) → ℕ) (z : ℕ) (v : Vector ℕ n) : List ℕ :=
  List.ofFn fun i : Fin (z + 1) => Nat.recOn i (f v) (fun y IH => g (y ::ᵥ IH ::ᵥ v))

lemma beta_unbeta_recSequence_eq (f : Vector ℕ n → ℕ) (g : Vector ℕ (n + 2) → ℕ) (z : ℕ) (v : Vector ℕ n)
  (m : ℕ) (hm : m < z + 1) :
    Nat.beta (unbeta (recSequence f g z v)) m = m.rec (f v) (fun y IH => g (y ::ᵥ IH ::ᵥ v)) := by
  have := beta_function_lemma (recSequence f g z v) ⟨m, by simp[recSequence, hm]⟩
  simp at this; rw[this]; simp[recSequence]

lemma beta_unbeta_recSequence_zero (f : Vector ℕ n → ℕ) (g : Vector ℕ (n + 2) → ℕ) (z : ℕ) (v : Vector ℕ n) :
    Nat.beta (unbeta (recSequence f g z v)) 0 = f v := by
  simpa using beta_unbeta_recSequence_eq f g z v 0 (inv_iff_ne_zero.mp rfl)

lemma beta_unbeta_recSequence_succ (f : Vector ℕ n → ℕ) (g : Vector ℕ (n + 2) → ℕ) (z : ℕ) (v : Vector ℕ n)
  {m : ℕ} (hm : m < z) :
    Nat.beta (unbeta (recSequence f g z v)) (m + 1) = g (m ::ᵥ Nat.beta (unbeta (recSequence f g z v)) m ::ᵥ v) := by
  rw[beta_unbeta_recSequence_eq f g z v m (Nat.lt_add_right 1 hm),
    beta_unbeta_recSequence_eq f g z v (m + 1) (Nat.add_lt_add_right hm 1)]
  simp

lemma beta_eq_rec (f : Vector ℕ n → ℕ) (g : Vector ℕ (n + 2) → ℕ) {z : ℕ} {v}
  (h0 : z.beta 0 = f v) (hs : ∀ i < m, z.beta (i + 1) = g (i ::ᵥ z.beta i ::ᵥ v)) :
    z.beta m = m.rec (f v) (fun y IH => g (y ::ᵥ IH ::ᵥ v)) := by
  induction' m with m ih <;> simp[h0]
  · rw[hs m (lt.base m), ←ih (fun i hi => hs i (lt.step hi))]

variable {α : Type _}

lemma get_one {α : Type*} {n} (v : Vector α (n + 2)) : v.get 1 = v.tail.head := by
  rw[←Vector.get_zero, Vector.get_tail_succ]; rfl

lemma prec {n f g} (hf : @Arith n f) (hg : @Arith (n + 2) g) :
    @Arith (n + 1) (fun v => v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) := by
  let F : Vector ℕ (n + 2) → ℕ := fun v =>
    (isEqNat (Nat.beta v.head 0) (f v.tail.tail)).and
    (Nat.ball v.tail.head $ fun i => isEqNat (Nat.beta v.head (i + 1)) (g (i ::ᵥ Nat.beta v.head i ::ᵥ v.tail.tail)))
  have hp : @Arith (n + 3) (fun v =>
    isEqNat (Nat.beta v.tail.head (v.head + 1))
    (g (v.head ::ᵥ Nat.beta v.tail.head v.head ::ᵥ v.tail.tail.tail))) :=
    (equal 0 1).comp₂ _
      ((beta 0 1).comp₂ _ head.tail ((succ 0).comp₁ _ head))
      (hg.comp' $ head.cons $ ((beta 0 1).comp₂ _ head.tail head).cons $ by intro i; simp; exact proj _)
  have hF : Arith F := (and 0 1).comp₂ _
    ((equal 0 1).comp₂ _ ((beta 0 1).comp₂ _ head zero) hf.tail.tail)
    ((@ball (n + 2) (fun v i =>
      isEqNat (Nat.beta v.head (i + 1)) (g (i ::ᵥ Nat.beta v.head i ::ᵥ v.tail.tail))) hp 1).of_eq $ by
        simp[get_one])
  have : @Arith (n + 2) (fun v => Nat.beta v.head v.tail.head) :=
    (beta 0 1).of_eq (by simp [get_one])
  have := PartArith.map (fun v x => Nat.beta x v.head) this (PartArith.rfindPos hF)
  exact this.of_eq <| by
    intro v; simp[Part.eq_some_iff]
    suffices : ∃ z : ℕ, z.beta 0 = f v.tail ∧ ∀ i < v.head, z.beta (i + 1) = g (i ::ᵥ z.beta i ::ᵥ v.tail)
    · rcases least_number _ this with ⟨z, ⟨hz0, hzs⟩, hzm⟩
      exact ⟨z, ⟨by symm; simp[hz0]; exact hzs,
        by intro m hm; symm; simpa[imp_iff_not_or, not_or] using hzm m hm⟩,
        beta_eq_rec f g hz0 hzs⟩
    let l : List ℕ := recSequence f g v.head v.tail
    exact ⟨unbeta l,
      beta_unbeta_recSequence_zero f g v.head v.tail,
      fun i hi => beta_unbeta_recSequence_succ f g v.head v.tail hi⟩

lemma of_primrec {f : Vector ℕ n → ℕ} (hf : Primrec' f) : Arith f := by
  induction hf
  case zero               => exact zero
  case succ               => exact (@succ 1 0).of_eq (by simp)
  case get i              => exact proj i
  case comp f g _ _ hf hg => exact hf.comp _ hg
  case prec f g _ _ hf hg => exact hf.prec hg

lemma _root_.Nat.PartArith.of_partrec {f : Vector ℕ n →. ℕ} (hf : Partrec' f) : PartArith f := by
  induction hf
  case prim f hf          => exact of_primrec hf
  case comp f g _ _ hf hg => exact hf.comp _ hg
  case rfind f _ hf       => exact PartArith.rfind hf

end Nat.Arith

namespace Nat.PartArith

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

inductive Code.eval : {n : ℕ} → Code n → (Vector ℕ n →. ℕ) → Prop
  | zero {n} : Code.eval (Code.zero n) (fun _ => 0)
  | one  {n} : Code.eval (Code.one n)  (fun _ => 1)
  | add  {n} (i j : Fin n) : Code.eval (Code.add i j) (fun v => ↑(v.get i + v.get j))
  | mul  {n} (i j : Fin n) : Code.eval (Code.mul i j) (fun v => ↑(v.get i * v.get j))
  | proj {n} (i : Fin n)   : Code.eval (Code.proj i) (fun v => v.get i)
  | equal {n} (i j : Fin n)   : Code.eval (Code.equal i j) (fun v => isEqNat (v.get i) (v.get j))
  | lt {n} (i j : Fin n) : Code.eval (Code.lt i j) (fun v => isLtNat (v.get i) (v.get j))
  | comp {m n} (c : Code n) (d : Fin n → Code m) (f : Vector ℕ n →. ℕ) (g : Fin n → (Vector ℕ m →. ℕ)) :
      Code.eval c f → (∀ i, Code.eval (d i) (g i)) →
      Code.eval (c.comp d) (fun v => (mOfFn fun i => g i v) >>= f)
  | rfind {n} (c : Code (n + 1)) (f : Vector ℕ (n + 1) → ℕ) :
      Code.eval c f → Code.eval c.rfind (fun v => Nat.rfind fun n => Part.some (f (n ::ᵥ v) = 0))

lemma exists_code : ∀ {n : ℕ} {f : Vector ℕ n →. ℕ}, PartArith f → ∃ c : Code n, c.eval f
  | n, _, PartArith.zero                => ⟨Code.zero n, Code.eval.zero⟩
  | n, _, PartArith.one                 => ⟨Code.one n, Code.eval.one⟩
  | _, _, PartArith.add i j             => ⟨Code.add i j, Code.eval.add i j⟩
  | _, _, PartArith.mul i j             => ⟨Code.mul i j, Code.eval.mul i j⟩
  | _, _, PartArith.proj i              => ⟨Code.proj i, Code.eval.proj i⟩
  | _, _, PartArith.equal i j           => ⟨Code.equal i j, Code.eval.equal i j⟩
  | _, _, PartArith.lt i j              => ⟨Code.lt i j, Code.eval.lt i j⟩
  | _, _, @PartArith.comp _ _ f g hf hg => by
    rcases exists_code hf with ⟨cf, hcf⟩
    choose cg hcg using fun i            => exists_code (hg i)
    exact ⟨cf.comp cg, Code.eval.comp cf cg f g hcf hcg⟩
  | _, _, @PartArith.rfind _ f hf       => by
    rcases exists_code hf with ⟨cf, hcf⟩
    exact ⟨cf.rfind, Code.eval.rfind cf f hcf⟩

end Nat.PartArith
