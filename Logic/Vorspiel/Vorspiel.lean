import Logic.Vorspiel.Notation
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Finset.Preimage
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

namespace Fin
section
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

@[simp] lemma zero_succ_eq_id {n} : (0 : Fin (n + 1)) :> succ = id :=
  funext $ Fin.cases (by simp) (by simp)

def nil : Fin 0 → C := finZeroElim

def singleton (a : C) : Fin 1 → C := a :> nil

def mk2 (a b : C) : Fin 2 → C := a :> b :> nil

lemma to_leftConcat (s : Fin (n + 1) → C) : s = s 0 :> s ∘ Fin.succ :=
   funext $ Fin.cases (by simp) (by simp)

@[simp] lemma leftConcat_ext (a₁ a₂ : C) (s₁ s₂ : Fin n → C) :
    a₁ :> s₁ = a₂ :> s₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  ⟨by intros h
      constructor
      · exact congrFun h 0
      · exact funext (fun i => by simpa using congrFun h (Fin.castSucc i + 1)),
   by intros h; simp[h]⟩

def decFinfun {α : Type _} : {n : ℕ} → (v w : Fin n → α) → (∀ i, Decidable (v i = w i)) → Decidable (v = w)
  | 0,     _, _, _ => by simp; exact isTrue trivial
  | n + 1, v, w, d => by
      rw[Fin.to_leftConcat v, Fin.to_leftConcat w, Fin.leftConcat_ext]
      haveI : Decidable (v ∘ Fin.succ = w ∘ Fin.succ) := decFinfun _ _ (by intros i; simp; exact d _)
      refine instDecidableAnd

lemma comp_left_concat (f : C → α) (a : C) (s : Fin n → C) : (fun x => f $ (a :> s) x) = f a :> f ∘ s :=
funext (fun i => cases (by simp) (by simp) i)

lemma comp_right_concat (f : C → α) (a : C) (s : Fin n → C) : (fun x => f $ (s <: a) x) = f ∘ s <: f a :=
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
  case zero => simp at hi
  case succ => rcases i <;> simp

def toOptionFinTo : {n : ℕ} → (Fin n → Option α) → Option (Fin n → α)
  | 0,     _ => some nil
  | _ + 1, v => (toOptionFinTo (v ∘ Fin.succ)).bind (fun vs => (v 0).map (fun z => z :> vs))

@[simp] lemma toOptionFinTo_some (v : Fin n → α) :
    toOptionFinTo (fun i => some (v i)) = some v :=
  by induction n <;> simp[*, toOptionFinTo, Function.comp]; exact funext (Fin.cases (by simp) (by simp))

def finitaryToNat : {n : ℕ} → (Fin n → ℕ) → ℕ
  | 0,     _ => 0
  | _ + 1, v => Nat.mkpair (v 0) (finitaryToNat $ v ∘ Fin.succ)

end Fin

def Nat.unvector : {n : ℕ} → ℕ → Fin n → ℕ
  | 0,     _ => Fin.nil
  | _ + 1, e => e.unpair.1 :> Nat.unvector e.unpair.2

namespace Nat
variable {n}

@[simp] lemma unvector_le (e : ℕ) (i : Fin n) : unvector e i ≤ e := by
  induction' n with n ih generalizing e <;> simp[*, unvector]
  · have := i.isLt; simp at this
  · exact Fin.cases (by simpa using Nat.unpair_left_le _) (fun i => le_trans (ih e.unpair.2 i) (Nat.unpair_right_le _)) i

@[simp] lemma unvector_finitaryToNat (v : Fin n → ℕ) : unvector (Fin.finitaryToNat v) = v := by
  induction n <;> simp[*, Nat.unvector, Fin.finitaryToNat]; exact funext (fun i => i.cases (by simp) (by simp))

-- @[simp] lemma toNat_unvector (ln : 0 < n) (e : ℕ) : Fin.finitaryToNat (unvector e : Fin n → ℕ) = e := by
--   induction n generalizing e <;> simp[unvector, Fin.finitaryToNat, Function.comp]
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

def funFin_toStr : ∀ {n}, (Fin n → String) → String
  | 0,     _ => ""
  | n + 1, s => if n = 0 then s 0 else s 0 ++ ", " ++ @funFin_toStr n (fun i => s (Fin.succ i))

def test : Fin 4 → String := "a" :> "b" :> "c" :> "d" :> Fin.nil

end String

namespace Finset
variable {I : Type u} {A : I → Type v}

--noncomputable def FinsetSigma (s : Finset (Σ i : I, A i)) (i : I) : Finset (A i) :=
--  Finset.preimage s (Sigma.mk i) (Set.injOn_of_injective sigma_mk_injective _)

end Finset