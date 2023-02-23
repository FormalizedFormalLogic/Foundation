import Logic.Vorspiel.Notation
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.W.Basic

namespace Nat
variable {α : ℕ → Sort u}

def cases (hzero : α 0) (hsucc : ∀ n, α (n + 1)) : ∀ n, α n
  | 0     => hzero
  | n + 1 => hsucc n  

infixr:70 " :>ₙ " => cases

@[simp] lemma cases_zero (hzero : α 0) (hsucc : ∀ n, α (n + 1)) :
    (hzero :>ₙ hsucc) 0 = hzero := rfl

@[simp] lemma cases_succ (hzero : α 0) (hsucc : ∀ n, α (n + 1)) (n : ℕ) :
    (hzero :>ₙ hsucc) (n + 1) = hsucc n := rfl

end Nat

namespace Matrix
open Fin
section
variable {n : ℕ} {α : Type u} (a b : α) (s : Fin n → α)

infixr:70 " :> " => vecCons

@[simp] lemma vecCons_zero :
    (a :> s) 0 = a := by simp

@[simp] lemma vecCons_succ (i : Fin n) :
    (a :> s) (Fin.succ i) = s i := by simp

@[simp] lemma vecCons_last (a : C) (s : Fin (n + 1) → C) :
    (a :> s) (Fin.last (n + 1)) = s (Fin.last n) := vecCons_succ a s (Fin.last n)

def vecConsLast {n : ℕ} (t : Fin n → α) (h : α) : Fin n.succ → α :=
  Fin.lastCases h t

infixl:70 " <: " => vecConsLast

@[simp] lemma rightConcat_last :
    (s <: a) (last n) = a := by simp[vecConsLast]

@[simp] lemma rightConcat_castSucc (i : Fin n) :
    (s <: a) (Fin.castSucc i) = s i := by simp[vecConsLast]

@[simp] lemma rightConcat_zero (a : α) (s : Fin n.succ → α) :
    (s <: a) 0 = s 0 := rightConcat_castSucc a s 0

@[simp] lemma zero_succ_eq_id {n} : (0 : Fin (n + 1)) :> succ = id :=
  funext $ Fin.cases (by simp) (by simp)

lemma to_vecCons (s : Fin (n + 1) → C) : s = s 0 :> s ∘ Fin.succ :=
   funext $ Fin.cases (by simp) (by simp)

@[simp] lemma vecCons_ext (a₁ a₂ : α) (s₁ s₂ : Fin n → α) :
    a₁ :> s₁ = a₂ :> s₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  ⟨by intros h
      constructor
      · exact congrFun h 0
      · exact funext (fun i => by simpa using congrFun h (Fin.castSucc i + 1)),
   by intros h; simp[h]⟩

def decVec {α : Type _} : {n : ℕ} → (v w : Fin n → α) → (∀ i, Decidable (v i = w i)) → Decidable (v = w)
  | 0,     _, _, _ => by simp; exact isTrue trivial
  | n + 1, v, w, d => by
      rw[to_vecCons v, to_vecCons w, vecCons_ext]
      haveI : Decidable (v ∘ Fin.succ = w ∘ Fin.succ) := decVec _ _ (by intros i; simp; exact d _)
      refine instDecidableAnd

lemma comp_vecCons (f : α → β) (a : α) (s : Fin n → α) : (fun x => f $ (a :> s) x) = f a :> f ∘ s :=
funext (fun i => cases (by simp) (by simp) i)

lemma comp_vecConsLast (f : α → β) (a : α) (s : Fin n → α) : (fun x => f $ (s <: a) x) = f ∘ s <: f a :=
funext (fun i => lastCases (by simp) (by simp) i)

end

variable {α : Type _}

def toList : {n : ℕ} → (Fin n → α) → List α
  | 0,     _ => []
  | _ + 1, v => v 0 :: toList (v ∘ Fin.succ)

@[simp] lemma toList_zero (v : Fin 0 → α) : toList v = [] := rfl

@[simp] lemma toList_succ (v : Fin (n + 1) → α) : toList v = v 0 :: toList (v ∘ Fin.succ) := rfl

@[simp] lemma toList_length (v : Fin n → α) : (toList v).length = n :=
  by induction n <;> simp[*]

@[simp] lemma toList_nth (v : Fin n → α) (i) (hi) : (toList v).nthLe i hi = v ⟨i, by simpa using hi⟩ := by
  induction n generalizing i <;> simp[*, List.nthLe_cons]
  case zero => contradiction
  case succ => rcases i <;> simp

def toOptionVec : {n : ℕ} → (Fin n → Option α) → Option (Fin n → α)
  | 0,     _ => some vecEmpty
  | _ + 1, v => (toOptionVec (v ∘ Fin.succ)).bind (fun vs => (v 0).map (fun z => z :> vs))

@[simp] lemma toOptionVec_some (v : Fin n → α) :
    toOptionVec (fun i => some (v i)) = some v :=
  by induction n <;> simp[*, toOptionVec, Function.comp]; exact funext (Fin.cases (by simp) (by simp))

def vecToNat : {n : ℕ} → (Fin n → ℕ) → ℕ
  | 0,     _ => 0
  | _ + 1, v => Nat.mkpair (v 0) (vecToNat $ v ∘ Fin.succ)

end Matrix

def Nat.unvector : {n : ℕ} → ℕ → Fin n → ℕ
  | 0,     _ => Matrix.vecEmpty
  | _ + 1, e => e.unpair.1 :> Nat.unvector e.unpair.2

namespace Nat
open Matrix
variable {n}

@[simp] lemma unvector_le (e : ℕ) (i : Fin n) : unvector e i ≤ e := by
  induction' n with n ih generalizing e <;> simp[*, unvector]
  · have := i.isLt; contradiction
  · exact Fin.cases (by simpa using Nat.unpair_left_le _) (fun i => le_trans (ih e.unpair.2 i) (Nat.unpair_right_le _)) i

@[simp] lemma unvector_vecToNat (v : Fin n → ℕ) : unvector (vecToNat v) = v := by
  induction n <;> simp[*, Nat.unvector, vecToNat]; exact funext (fun i => i.cases (by simp) (by simp))

-- @[simp] lemma toNat_unvector (ln : 0 < n) (e : ℕ) : Fin.vecToNat (unvector e : Fin n → ℕ) = e := by
--   induction n generalizing e <;> simp[unvector, Fin.vecToNat, Function.comp]
--   · simp at ln
--   · {simp[Function.comp]; sorry}

lemma one_le_of_bodd {n : ℕ} (h : n.bodd = true) : 1 ≤ n :=
by induction n <;> simp[←Nat.add_one] at h ⊢

end Nat

namespace Fintype
variable {ι : Type _} [Fintype ι] {α : Type _} [SemilatticeSup α] [OrderBot α]

def sup (f : ι → α) : α := (Finset.univ : Finset ι).sup f

@[simp] lemma elem_le_sup (f : ι → α) (i : ι) : f i ≤ sup f := Finset.le_sup (by simp)

lemma le_sup {a : α} {f : ι → α} (i : ι) (le : a ≤ f i) : a ≤ sup f := le_trans le (elem_le_sup _ _)

@[simp] lemma sup_le_iff {f : ι → α} {a : α} :
    sup f ≤ a ↔ (∀ i, f i ≤ a) := by simp[sup]

@[simp] lemma finsup_eq_0_of_empty [IsEmpty ι] (f : ι → α) : sup f = ⊥ := by simp[sup]

end Fintype

namespace String

def vecToStr : ∀ {n}, (Fin n → String) → String
  | 0,     _ => ""
  | n + 1, s => if n = 0 then s 0 else s 0 ++ ", " ++ @vecToStr n (fun i => s (Fin.succ i))

#eval vecToStr !["a", "b", "c", "d"]

end String