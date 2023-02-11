import Logic.Vorspiel.Notation
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice

namespace Fin
variable {n : ℕ} {C : Sort u} {a b : C} {s : Fin n → C}

def leftConcat {C : Sort u} (hzero : C) (hsucc : Fin n → C) : Fin (n + 1) → C :=
  @cases n (fun _ => C) hzero hsucc

infixr:70 " :> " => leftConcat

@[simp] lemma leftConcat_zero (a : C) (s : Fin n → C) :
    (a :> s) 0 = a := by simp[leftConcat]

@[simp] lemma leftConcat_succ (a : C) (s : Fin n → C) (i : Fin n) :
    (a :> s) (Fin.succ i) = s i := by simp[leftConcat]

@[simp] lemma leftConcat_last (a : C) (s : Fin (n + 1) → C) :
    (a :> s) (Fin.last (n + 1)) = s (Fin.last n) := leftConcat_succ a s (Fin.last n)

def rightConcat {n} {C : Sort u} (hcast : Fin n → C) (hlast : C) : Fin (n + 1) → C :=
  @lastCases n (fun _ => C) hlast hcast

infixl:70 " <: " => rightConcat

@[simp] lemma rightConcat_last (s : Fin n → C) (a : C) :
    (s <: a) (last n) = a := by simp[rightConcat]

@[simp] lemma rightConcat_castSucc (s : Fin n → C) (a : C) (i : Fin n) :
    (s <: a) (Fin.castSucc i) = s i := by simp[rightConcat]

@[simp] lemma rightConcat_zero {s : Fin (n + 1) → C} {a : C} :
    (s <: a) 0 = s 0 := rightConcat_castSucc s a 0 

def nil : Fin 0 → C := finZeroElim

def singleton (a : C) : Fin 1 → C := a :> nil

def mk2 (a b : C) : Fin 2 → C := a :> b :> nil

end Fin

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



def funFin_toStr : ∀ {n}, (Fin n → String) → String
  | 0,     _ => ""
  | n + 1, s => if n = 0 then s 0 else s 0 ++ ", " ++ @funFin_toStr n (fun i => s (Fin.succ i))

def test : Fin 4 → String := "a" :> "b" :> "c" :> "d" :> Fin.nil

#eval funFin_toStr test

end String
