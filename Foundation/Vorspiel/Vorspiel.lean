import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.W.Basic
import Mathlib.Order.Filter.Ultrafilter
import Mathlib.Logic.Encodable.Basic
import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD

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

@[simp] lemma ne_step_max (n m : ℕ) : n ≠ max n m + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

@[simp] lemma ne_step_max' (n m : ℕ) : n ≠ max m n + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

lemma rec_eq {α : Sort*} (a : α) (f₁ f₂ : ℕ → α → α) (n : ℕ) (H : ∀ m < n, ∀ a, f₁ m a = f₂ m a) :
    (n.rec a f₁ : α) = n.rec a f₂ := by
  induction' n with n ih <;> simp
  · have : (n.rec a f₁ : α) = n.rec a f₂ := ih (fun m hm a =>  H m (Nat.lt.step hm) a)
    simpa[this] using H n (Nat.lt.base n) (n.rec a f₂)

lemma least_number (P : ℕ → Prop) (hP : ∃ x, P x) : ∃ x, P x ∧ ∀ z < x, ¬P z := by
  rcases hP with ⟨n, hn⟩
  induction' n using Nat.strongRec with n ih
  by_cases H : ∃ m < n, P m
  · rcases H with ⟨m, hm, hPm⟩
    exact ih m hm hPm
  · exact ⟨n, hn, by simpa using H⟩

def toFin (n : ℕ) : ℕ → Option (Fin n) := fun x => if hx : x < n then some ⟨x, hx⟩ else none

end Nat

lemma eq_finZeroElim {α : Sort u} (x : Fin 0 → α) : x = finZeroElim := funext (by rintro ⟨_, _⟩; contradiction)

namespace Matrix
open Fin
section
variable {n : ℕ} {α : Type u}

infixr:70 " :> " => vecCons

@[simp] lemma vecCons_zero :
    (a :> s) 0 = a := by simp

@[simp] lemma vecCons_succ (i : Fin n) :
    (a :> s) (Fin.succ i) = s i := by simp

@[simp] lemma vecCons_last (a : C) (s : Fin (n + 1) → C) :
    (a :> s) (Fin.last (n + 1)) = s (Fin.last n) := vecCons_succ (Fin.last n)

def vecConsLast {n : ℕ} (t : Fin n → α) (h : α) : Fin n.succ → α :=
  Fin.lastCases h t

@[simp] lemma cons_app_one {n : ℕ} (a : α) (s : Fin n.succ → α) : (a :> s) 1 = s 0 := rfl

@[simp] lemma cons_app_two {n : ℕ} (a : α) (s : Fin n.succ.succ → α) : (a :> s) 2 = s 1 := rfl

@[simp] lemma cons_app_three {n : ℕ} (a : α) (s : Fin n.succ.succ.succ → α) : (a :> s) 3 = s 2 := rfl

section delab
open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander Matrix.vecEmpty]
def unexpandVecEmpty : Unexpander
  | `($(_)) => `(![])

@[app_unexpander Matrix.vecCons]
def unexpandVecCons : Unexpander
  | `($(_) $a ![])      => `(![$a])
  | `($(_) $a ![$as,*]) => `(![$a, $as,*])
  | _                   => throw ()

#check ![1, 2]

end delab

infixl:70 " <: " => vecConsLast

@[simp] lemma rightConcat_last :
    (s <: a) (last n) = a := by simp[vecConsLast]

@[simp] lemma rightConcat_castSucc (i : Fin n) :
    (s <: a) (Fin.castSucc i) = s i := by simp[vecConsLast]

@[simp] lemma rightConcat_zero (a : α) (s : Fin n.succ → α) :
    (s <: a) 0 = s 0 := rightConcat_castSucc 0

@[simp] lemma zero_succ_eq_id {n} : (0 : Fin (n + 1)) :> succ = id :=
  funext $ Fin.cases (by simp) (by simp)

@[simp] lemma zero_cons_succ_eq_self (f : Fin (n + 1) → α) : (f 0 :> (f ·.succ) : Fin (n + 1) → α) = f := by
    funext x; cases x using Fin.cases <;> simp

lemma eq_vecCons (s : Fin (n + 1) → C) : s = s 0 :> s ∘ Fin.succ :=
   funext $ Fin.cases (by simp) (by simp)

@[simp] lemma vecCons_ext (a₁ a₂ : α) (s₁ s₂ : Fin n → α) :
    a₁ :> s₁ = a₂ :> s₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  ⟨by intros h
      constructor
      · exact congrFun h 0
      · exact funext (fun i => by simpa using congrFun h (Fin.castSucc i + 1)),
   by intros h; simp[h]⟩

lemma vecCons_assoc (a b : α) (s : Fin n → α) :
    a :> (s <: b) = (a :> s) <: b := by
  funext x; cases' x using Fin.cases with x <;> simp; cases x using Fin.lastCases <;> simp[Fin.succ_castSucc]

def decVec {α : Type _} : {n : ℕ} → (v w : Fin n → α) → (∀ i, Decidable (v i = w i)) → Decidable (v = w)
  | 0,     _, _, _ => by simp[Matrix.empty_eq]; exact isTrue trivial
  | n + 1, v, w, d => by
      rw[eq_vecCons v, eq_vecCons w, vecCons_ext]
      haveI : Decidable (v ∘ Fin.succ = w ∘ Fin.succ) := decVec _ _ (by intros i; simp; exact d _)
      refine instDecidableAnd

lemma comp_vecCons (f : α → β) (a : α) (s : Fin n → α) : (fun x => f $ (a :> s) x) = f a :> f ∘ s :=
funext (fun i => cases (by simp) (by simp) i)

lemma comp_vecCons' (f : α → β) (a : α) (s : Fin n → α) : (fun x => f $ (a :> s) x) = f a :> fun i => f (s i) :=
  comp_vecCons f a s

lemma comp_vecCons'' (f : α → β) (a : α) (s : Fin n → α) : f ∘ (a :> s) = f a :> f ∘ s :=
  comp_vecCons f a s

@[simp] lemma comp₀ : f ∘ (![] : Fin 0 → α) = ![] := by simp[Matrix.empty_eq]

@[simp] lemma comp₁ (a : α) : f ∘ ![a] = ![f a] := by simp[comp_vecCons'']

@[simp] lemma comp₂ (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] := by simp[comp_vecCons'']

@[simp] lemma comp₃ (a₁ a₂ a₃ : α) : f ∘ ![a₁, a₂, a₃] = ![f a₁, f a₂, f a₃] := by simp[comp_vecCons'']

lemma comp_vecConsLast (f : α → β) (a : α) (s : Fin n → α) : (fun x => f $ (s <: a) x) = f ∘ s <: f a :=
funext (fun i => lastCases (by simp) (by simp) i)

@[simp] lemma vecHead_comp (f : α → β) (v : Fin (n + 1) → α) : vecHead (f ∘ v) = f (vecHead v) :=
  by simp[vecHead]

@[simp] lemma vecTail_comp (f : α → β) (v : Fin (n + 1) → α) : vecTail (f ∘ v) = f ∘ (vecTail v) := by
  simp [vecTail, Function.comp_assoc]

lemma vecConsLast_vecEmpty {s : Fin 0 → α} (a : α) : s <: a = ![a] :=
  funext (fun x => by
    have : 0 = Fin.last 0 := by rfl
    cases' x using Fin.cases with i
    · rw [this, rightConcat_last, cons_val_fin_one]
    have := i.isLt; contradiction )

lemma constant_eq_singleton {a : α} : (fun _ => a) = ![a] := by funext x; simp

lemma constant_eq_singleton' {v : Fin 1 → α} : v = ![v 0] := by funext x; simp[Fin.eq_zero]

lemma constant_eq_vec₂ {a : α} : (fun _ => a) = ![a, a] := by
  funext x; cases x using Fin.cases <;> simp[Fin.eq_zero]

lemma fun_eq_vec₂ {v : Fin 2 → α} : v = ![v 0, v 1] := by
  funext x; cases x using Fin.cases <;> simp[Fin.eq_zero]

lemma injective_vecCons {f : Fin n → α} (h : Function.Injective f) {a} (ha : ∀ i, a ≠ f i) : Function.Injective (a :> f) := by
  have : ∀ i, f i ≠ a := fun i => (ha i).symm
  intro i j; cases i using Fin.cases <;> cases j using Fin.cases <;> simp[*]
  intro hf; exact h hf

end

variable {α : Type _}

def toList : {n : ℕ} → (Fin n → α) → List α
  | 0,     _ => []
  | _ + 1, v => v 0 :: toList (v ∘ Fin.succ)

@[simp] lemma toList_zero (v : Fin 0 → α) : toList v = [] := rfl

@[simp] lemma toList_succ (v : Fin (n + 1) → α) : toList v = v 0 :: toList (v ∘ Fin.succ) := rfl

@[simp] lemma toList_length (v : Fin n → α) : (toList v).length = n :=
  by induction n <;> simp[*]

@[simp] lemma mem_toList_iff {v : Fin n → α} {a} : a ∈ toList v ↔ ∃ i, v i = a :=
  by induction n <;> simp[*]; constructor; { rintro (rfl | ⟨i, rfl⟩) <;> simp }; { rintro ⟨i, rfl⟩; cases i using Fin.cases <;> simp }

def toOptionVec : {n : ℕ} → (Fin n → Option α) → Option (Fin n → α)
  | 0,     _ => some vecEmpty
  | _ + 1, v => (toOptionVec (v ∘ Fin.succ)).bind (fun vs => (v 0).map (fun z => z :> vs))

@[simp] lemma toOptionVec_some (v : Fin n → α) :
    toOptionVec (fun i ↦ some (v i)) = some v := by
  induction n <;> simp[*, Matrix.empty_eq, toOptionVec, Function.comp_def]

@[simp] lemma toOptionVec_zero (v : Fin 0 → Option α) : toOptionVec v = some ![] := rfl

@[simp] lemma toOptionVec_eq_none_iff {v : Fin n → Option α} :
    toOptionVec v = none ↔ ∃ i, v i = none := by
  induction' n with n ih
  · simp
  · simp[toOptionVec]
    rcases hz : v 0 with (_ | a) <;> simp
    { exact ⟨0, hz⟩ }
    { rcases hs : toOptionVec (v ∘ Fin.succ) with (_ | w) <;> simp
      { rcases ih.mp hs with ⟨i, hi⟩
        exact ⟨i.succ, hi⟩ }
      { intro x; cases x using Fin.cases
        · simp[hz]
        · have : toOptionVec (v ∘ Fin.succ) ≠ none ↔ ∀ i : Fin n, v i.succ ≠ none :=
            by simpa using not_iff_not.mpr (@ih (v ∘ Fin.succ))
          exact this.mp (by simp[hs]) _ } }

@[simp] lemma toOptionVec_eq_some_iff {v : Fin n → Option α} :
    toOptionVec v = some w ↔ ∀ i, v i = some (w i) := by
  induction' n with n ih
  · simp[Matrix.empty_eq]
  · simp[toOptionVec]
    rcases hz : v 0 with (_ | a) <;> simp
    { exact ⟨0, by simp[hz]⟩ }
    { rcases hs : toOptionVec (v ∘ Fin.succ) with (_ | z) <;> simp
      { have : ∃ i : Fin n, v i.succ = none := by simpa using hs
        rcases this with ⟨i, hi⟩
        exact ⟨i.succ, by simp[hi]⟩ }
      { have : ∀ i, v i.succ = some (z i) := ih.mp hs
        have : v = some a :> (fun i => some (z i)) :=
          by funext i; cases i using Fin.cases <;> simp[hz, this]
        simp[this, ←comp_vecCons', Iff.symm Function.funext_iff ] } }


variable {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}

def getM : {n : ℕ} → {β : Fin n → Type u} → ((i : Fin n) → m (β i)) → m ((i : Fin n) → β i)
  | 0,     _, _ => pure finZeroElim
  | _ + 1, _, f => Fin.cases <$> f 0 <*> getM (f ·.succ)

lemma getM_pure [LawfulMonad m] {n} {β : Fin n → Type u} (v : (i : Fin n) → β i) :
    getM (fun i => (pure (v i) : m (β i))) = pure v := by
  induction' n with n ih <;> simp[empty_eq, getM]
  · congr; funext x; exact x.elim0
  · simp[vecHead, vecTail, Function.comp, seq_eq_bind, ih]
    exact congr_arg _ (funext $ Fin.cases rfl (fun i => rfl))

@[simp] lemma getM_some {n} {β : Fin n → Type u} (v : (i : Fin n) → β i) :
    getM (fun i => (some (v i) : Option (β i))) = some v := getM_pure v

def appendr {n m} (v : Fin n → α) (w : Fin m → α) : Fin (m + n) → α := Matrix.vecAppend (add_comm m n) v w

@[simp] lemma appendr_nil {m} (w : Fin m → α) : appendr ![] w = w := by funext i; simp [appendr]

@[simp] lemma appendr_cons {m n} (x : α) (v : Fin n → α) (w : Fin m → α) : appendr (x :> v) w = x :> appendr v w := by funext i; simp [appendr]

section vecToNat

def vecToNat : {n : ℕ} → (Fin n → ℕ) → ℕ
  | 0,     _ => 0
  | _ + 1, v => Nat.pair (v 0) (vecToNat $ v ∘ Fin.succ) + 1

open Encodable

@[simp] lemma vecToNat_empty (v : Fin 0 → ℕ) : vecToNat v = 0 := by rfl

@[simp] lemma encode_succ {n} (x : ℕ) (v : Fin n → ℕ) : vecToNat (x :> v) = Nat.pair x (vecToNat v) + 1 := by
  simp [vecToNat, Function.comp_def]

end vecToNat

end Matrix

namespace DMatrix

def vecEmpty : Fin 0 → α :=
  Fin.elim0

variable {n} {α : Fin (n + 1) → Type*}

def vecCons (h : α 0) (t : (i : Fin n) → α i.succ) : (i : Fin n.succ) → α i :=
  Fin.cons h t

infixr:70 " ::> " => vecCons

@[simp] lemma vecCons_zero (h : α 0) (t : (i : Fin n) → α i.succ) : (h ::> t) 0 = h := rfl

@[simp] lemma vecCons_succ (h : α 0) (t : (i : Fin n) → α i.succ) (i : Fin n) : (h ::> t) i.succ = t i := rfl

lemma eq_vecCons (s : (i : Fin (n + 1)) → α i) : s = s 0 ::> fun i => s i.succ :=
   funext $ Fin.cases (by simp) (by simp)

@[simp] lemma vecCons_ext (a₁ a₂ : α 0) (s₁ s₂ : (i : Fin n) → α i.succ) :
    a₁ ::> s₁ = a₂ ::> s₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  ⟨by intros h
      constructor
      · exact congrFun h 0
      · exact funext (fun i => by simpa using congrFun h i.succ),
   by intros h; simp[h]⟩

def decVec {n : ℕ} {α : Fin n → Type _}
  (v w : (i : Fin n) → α i) (h : ∀ i, Decidable (v i = w i)) : Decidable (v = w) := by
    induction' n with n ih
    · exact isTrue (by funext x; exact finZeroElim (α := fun x => v x = w x) x)
    · rw[eq_vecCons v, eq_vecCons w, vecCons_ext]
      haveI := ih (fun i => v i.succ) (fun i => w i.succ) (fun i => h i.succ)
      refine instDecidableAnd

end DMatrix

namespace Option

lemma pure_eq_some (a : α) : pure a = some a := rfl

@[simp] lemma toList_eq_iff {o : Option α} {a} :
    o.toList = [a] ↔ o = some a := by rcases o <;> simp

end Option

def Nat.natToVec : ℕ → (n : ℕ) → Option (Fin n → ℕ)
  | 0,     0     => some Matrix.vecEmpty
  | e + 1, n + 1 => Nat.natToVec e.unpair.2 n |>.map (e.unpair.1 :> ·)
  | _,     _     => none

namespace Nat
open Matrix
variable {n : ℕ}

@[simp] lemma natToVec_vecToNat (v : Fin n → ℕ) : (vecToNat v).natToVec n = some v := by
  induction n <;> simp[*, Nat.natToVec, vecToNat, Matrix.empty_eq]
  exact funext (fun i ↦ i.cases (by simp[Matrix.empty_eq]) (by simp[Matrix.empty_eq]))

lemma lt_of_eq_natToVec {e : ℕ} {v : Fin n → ℕ} (h : e.natToVec n = some v) (i : Fin n) : v i < e := by
  induction' n with n ih generalizing e
  · exact i.elim0
  · cases' e with e
    · simp [natToVec] at h
    · simp only [natToVec, Option.map_eq_some'] at h
      rcases h with ⟨v, hnv, rfl⟩
      cases' i using Fin.cases with i
      · simp [lt_succ, unpair_left_le]
      · simp only [cons_val_succ]
        exact lt_trans (ih hnv i) (lt_succ.mpr <| unpair_right_le e)

lemma one_le_of_bodd {n : ℕ} (h : n.bodd = true) : 1 ≤ n :=
by induction n <;> simp[←Nat.add_one] at h ⊢

lemma pair_le_pair_of_le {a₁ a₂ b₁ b₂ : ℕ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) : a₁.pair b₁ ≤ a₂.pair b₂ := by
  rcases lt_or_eq_of_le ha with (ha | rfl) <;> rcases lt_or_eq_of_le hb with (hb | rfl)
  { exact le_of_lt (lt_trans (Nat.pair_lt_pair_left b₁ ha) (Nat.pair_lt_pair_right a₂ hb)) }
  { exact le_of_lt (Nat.pair_lt_pair_left b₁ ha) }
  { exact le_of_lt (Nat.pair_lt_pair_right a₁ hb) }
  { rfl }

end Nat

namespace Fin

lemma pos_of_coe_ne_zero {i : Fin (n + 1)} (h : (i : ℕ) ≠ 0) :
    0 < i := Nat.pos_of_ne_zero h

@[simp] lemma one_pos'' : (0 : Fin (n + 2)) < 1 := pos_of_coe_ne_zero (Nat.succ_ne_zero 0)

@[simp] lemma two_pos : (0 : Fin (n + 3)) < 2 := pos_of_coe_ne_zero (Nat.succ_ne_zero 1)

@[simp] lemma three_pos : (0 : Fin (n + 4)) < 3 := pos_of_coe_ne_zero (Nat.succ_ne_zero 2)

@[simp] lemma four_pos : (0 : Fin (n + 5)) < 4 := pos_of_coe_ne_zero (Nat.succ_ne_zero 3)

@[simp] lemma five_pos : (0 : Fin (n + 6)) < 5 := pos_of_coe_ne_zero (Nat.succ_ne_zero 4)

end Fin

namespace Fintype
variable {ι : Type _} [Fintype ι]

section

variable {α : Type _} [SemilatticeSup α] [OrderBot α]

def sup (f : ι → α) : α := (Finset.univ : Finset ι).sup f

@[simp] lemma elem_le_sup (f : ι → α) (i : ι) : f i ≤ sup f := Finset.le_sup (by simp)

lemma le_sup {a : α} {f : ι → α} (i : ι) (le : a ≤ f i) : a ≤ sup f := le_trans le (elem_le_sup _ _)

@[simp] lemma sup_le_iff {f : ι → α} {a : α} :
    sup f ≤ a ↔ (∀ i, f i ≤ a) := by simp[sup]

@[simp] lemma finsup_eq_0_of_empty [IsEmpty ι] (f : ι → α) : sup f = ⊥ := by simp[sup]

end

def decideEqPi {β : ι → Type*} (a b : (i : ι) → β i) (_ : (i : ι) → Decidable (a i = b i)) : Decidable (a = b) :=
  decidable_of_iff (∀ i, a i = b i) Function.funext_iff.symm

end Fintype

namespace String

def vecToStr : ∀ {n}, (Fin n → String) → String
  | 0,     _ => ""
  | n + 1, s => if n = 0 then s 0 else s 0 ++ ", " ++ @vecToStr n (fun i => s (Fin.succ i))

#eval vecToStr !["a", "b", "c", "d"]

end String

namespace Empty

lemma eq_elim {α : Sort u} (f : Empty → α) : f = elim := funext (by rintro ⟨⟩)

end Empty

namespace IsEmpty
variable {o : Sort u} (h : IsEmpty o)

lemma eq_elim {α : Sort*} (f : o → α) : f = h.elim' := funext h.elim

end IsEmpty

namespace Function

variable  {α : Type u} {β : Type v}

def funEqOn (φ : α → Prop) (f g : α → β) : Prop := ∀ a, φ a → f a = g a

lemma funEqOn.of_subset {φ ψ : α → Prop} {f g : α → β} (e : funEqOn φ f g) (h : ∀ a, ψ a → φ a) : funEqOn ψ f g :=
  by intro a ha; exact e a (h a ha)

end Function

namespace Quotient
open Matrix
variable {α : Type u} [s : Setoid α] {β : Sort v}

@[elab_as_elim]
lemma inductionOnVec {φ : (Fin n → Quotient s) → Prop} (v : Fin n → Quotient s)
  (h : ∀ v : Fin n → α, φ (fun i => Quotient.mk s (v i))) : φ v :=
  Quotient.induction_on_pi v h

def liftVec : ∀ {n} (f : (Fin n → α) → β),
  (∀ v₁ v₂ : Fin n → α, (∀ n, v₁ n ≈ v₂ n) → f v₁ = f v₂) → (Fin n → Quotient s) → β
| 0,     f, _, _ => f ![]
| n + 1, f, h, v =>
  let ih : α → (Fin n → Quotient s) → β :=
    fun a v => liftVec (n := n) (fun v => f (a :> v))
      (fun v₁ v₂ hv => h (a :> v₁) (a :> v₂) (Fin.cases (by simp; exact refl a) hv)) v
  Quot.liftOn (vecHead v) (ih · (vecTail v))
    (fun a b hab => by
      have : ∀ v, f (a :> v) = f (b :> v) := fun v => h _ _ (Fin.cases hab (by simp; intro; exact refl _))
      simp [this, ih])

@[simp] lemma liftVec_zero (f : (Fin 0 → α) → β) (h) (v : Fin 0 → Quotient s) : liftVec f h v = f ![] := rfl

lemma liftVec_mk {n} (f : (Fin n → α) → β) (h) (v : Fin n → α) :
    liftVec f h (Quotient.mk s ∘ v) = f v := by
  induction' n with n ih <;> simp[liftVec, empty_eq, Quotient.liftOn_mk]
  simpa using ih (fun v' => f (vecHead v :> v'))
    (fun v₁ v₂ hv => h (vecHead v :> v₁) (vecHead v :> v₂) (Fin.cases (refl _) hv)) (vecTail v)

@[simp] lemma liftVec_mk₁ (f : (Fin 1 → α) → β) (h) (a : α) :
    liftVec f h ![Quotient.mk s a] = f ![a] := liftVec_mk f h ![a]

@[simp] lemma liftVec_mk₂ (f : (Fin 2 → α) → β) (h) (a₁ a₂ : α) :
    liftVec f h ![Quotient.mk s a₁, Quotient.mk s a₂] = f ![a₁, a₂] := liftVec_mk f h ![a₁, a₂]

end Quotient

namespace List

variable {α : Type u} {β: Type v}

lemma getI_map_range [Inhabited α] (f : ℕ → α) (h : i < n) : ((List.range n).map f).getI i = f i := by
  simpa [h] using List.getI_eq_getElem ((List.range n).map f) (n := i) (by simpa using h)

def subsetSet (l : List α) (s : Set α) [DecidablePred s] : Bool :=
  l.foldr (fun a ih => s a && ih) true

def upper : List ℕ → ℕ
  | []      => 0
  | n :: ns => max (n + 1) ns.upper

@[simp] lemma upper_nil : upper [] = 0 := rfl

@[simp] lemma upper_cons (n : ℕ) (ns : List ℕ) : upper (n :: ns) = max (n + 1) ns.upper := rfl

lemma lt_upper (l : List ℕ) {n} (h : n ∈ l) : n < l.upper := by
  induction' l with n ns ih <;> simp at h ⊢
  case cons =>
    rcases h with (rfl | h); { exact Or.inl (Nat.lt_succ_self _) }
    exact Or.inr (ih h)

section finset

variable [DecidableEq α] [DecidableEq β]

lemma toFinset_map {f : α → β} (l : List α) : (l.map f).toFinset = Finset.image f l.toFinset := by
  induction l <;> simp[*]

lemma toFinset_mono {l l' : List α} (h : l ⊆ l') : l.toFinset ⊆ l'.toFinset := by
  intro a; simp; intro ha; exact h ha

end finset

section sup

variable [SemilatticeSup α] [OrderBot α]

def sup : List α → α
  | [] => ⊥
  | a :: as => a ⊔ as.sup

@[simp] lemma sup_nil : ([] : List α).sup = ⊥ := rfl

@[simp] lemma sup_cons (a : α) (as : List α) : (a :: as).sup = a ⊔ as.sup := rfl

lemma le_sup {a} {l : List α} : a ∈ l → a ≤ l.sup :=
  by induction' l with a l ih <;> simp[*]; rintro (rfl | h); { simp }; { exact le_sup_of_le_right $ ih h }

lemma sup_ofFn (f : Fin n → α) : (ofFn f).sup = Finset.sup Finset.univ f := by
  induction' n with n ih <;> simp
  · simp[ih]
    have : (Finset.univ : Finset (Fin (n + 1))) = insert 0 ((Finset.univ : Finset (Fin n)).image Fin.succ) := by
      ext i; simp
    rw[this, Finset.sup_insert]; simp
    have : Finset.sup Finset.univ (fun i => f (Fin.succ i)) = Finset.sup {0}ᶜ f := by
      simpa[Function.comp] using Eq.symm <| Finset.sup_image (Finset.univ : Finset (Fin n)) Fin.succ f
    rw[this]

end sup

lemma ofFn_get_eq_map_cast {n} (g : α → β) (as : List α) {h} :
    ofFn (fun i => g (as.get (i.cast h)) : Fin n → β) = as.map g := by
  ext i b; simp
  by_cases hi : i < n
  · simp [hi, List.ofFnNthVal, List.getElem?_eq_getElem (h ▸ hi)]
  · simp [hi, List.ofFnNthVal, List.getElem?_len_le (le_of_not_lt $ h ▸ hi)]

lemma take_map_range (f : ℕ → α) : ((range n).map f).take m = (range (min n m)).map f := by
  induction' m with m ih
  · simp
  · simp[take_succ, ih]
    rcases hm : (range n)[m]? with (_ | i) <;> simp
    · have : n ≤ m := by simpa using getElem?_eq_none_iff.mp hm
      simp [Nat.min_eq_left this, Nat.min_eq_left (Nat.le_step this)]
    · have : m < n ∧ m = i := by simpa using getElem?_eq_some.mp hm
      rcases this with ⟨lt, rfl⟩
      simp [Nat.min_eq_right lt, Nat.min_eq_right (le_of_lt lt), range_succ]

lemma bind_toList_some {f : β → Option α} {g : β → α} {bs : List β} (h : ∀ x ∈ bs, f x = some (g x)) :
  bs.bind (fun i => (f i).toList) = bs.map g := by
  have : bs.bind (fun i => (f i).toList) = bs.bind (pure ∘ g) :=
    List.bind_congr (by simp; intro m hm; simp[h _ hm])
  rw[this]
  apply flatMap_pure_eq_map;

variable {m : Type _ → Type _} {α : Type _} {β : Type _} [Monad m]

lemma mapM'_eq_none_iff {f : α → Option β} {l : List α} : l.mapM' f = none ↔ ∃ a ∈ l, f a = none := by
  induction' l with a l ih <;> simp[Option.bind_eq_bind]
  { constructor
    { intros H
      rcases hb : f a with (_ | b); { simp }
      rcases hbs : mapM' f l with (_ | bs)
      { exact Or.inr (ih.mp hbs) }
      { have : False := by simpa[Option.pure_eq_some] using (H b hb) bs hbs
        contradiction } }
    { rintro (h | h)
      { simp[h] }
      { have := ih.mpr h; simp[this] } } }

lemma length_mapM' {f : α → Option β} {as : List α} : as.mapM' f = some bs → bs.length = as.length := by
  induction' as with a as ih generalizing bs
  · simp only [mapM', Option.pure_eq_some, Option.some.injEq, length_nil]; rintro rfl; simp
  · simp only [mapM', Option.pure_eq_some, Option.bind_eq_bind, Option.bind_eq_some,
    Option.some.injEq, length_cons, forall_exists_index, and_imp]; rintro b _ bs hbs rfl; simpa using ih hbs

lemma mapM'_mem_inversion {f : α → Option β} {as : List α} (h : as.mapM' f = some bs) (hb : b ∈ bs) :
    ∃ a, f a = some b := by
  induction' as with a as ih generalizing bs
  · simp only [mapM', Option.pure_eq_some, Option.some.injEq] at h
    rcases h with rfl; simp at hb
  · simp only [mapM', Option.pure_eq_some, Option.bind_eq_bind, Option.bind_eq_some,
    Option.some.injEq] at h
    rcases h with ⟨b', hb', bs', hbs', rfl⟩
    have : b = b' ∨ b ∈ bs' := by simpa using hb
    rcases this with (rfl | hb)
    · exact ⟨a, hb'⟩
    · exact ih hbs' hb

lemma mapM'_eq_mapM'_of_eq {f g : α → m β} (l : List α) (hf : ∀ a ∈ l, f a = g a) : l.mapM' f = l.mapM' g := by
  induction' l with a as ih <;> simp
  { have : as.mapM' f = as.mapM' g := ih (fun a ha => hf a (by simp[ha]))
    have : f a = g a := hf a (by simp)
    simp[*] }

lemma mapM'_option_map {f : α → Option β} {g : β → γ} (as : List α) :
    as.mapM' (fun a => (f a).map g) = (as.mapM' f).map (fun bs => bs.map g) := by
  induction' as with a as ih generalizing f g <;> simp[Option.pure_eq_some, Option.bind_eq_bind, Function.comp]
  { simp[ih]
    rcases f a with (_ | b) <;> simp
    rcases mapM' f as with (_ | bs) <;> simp }

def allSome' : List (Option α) → Option (List α) := mapM' id

@[simp] lemma mapM_eq_map (l : List α) (f : α → β) :
    l.mapM' (fun x => some (f x)) = some (l.map f) := by
  induction l <;> simp[Option.pure_eq_some, Option.bind_eq_bind, Function.comp, *]

lemma mapM_map (as : List α) (f : α → Option β) (g : Option β → Option γ) :
    mapM' g (as.map f) = as.mapM' (g ∘ f) := by
  induction' as with a as ih <;> simp[Option.bind_eq_bind, Function.comp, *]

@[simp] lemma allSome_map_some (l : List α) (f : α → β) :
    allSome' (l.map (fun x => some (f x))) = some (l.map f) := by
  simp[allSome', mapM_map]

lemma append_subset_append {l₁ l₂ l : List α} (h : l₁ ⊆ l₂) : l₁ ++ l ⊆ l₂ ++ l :=
  List.append_subset.mpr ⟨List.subset_append_of_subset_left _ h, subset_append_right l₂ l⟩

lemma subset_of_eq {l₁ l₂ : List α} (e : l₁ = l₂) : l₁ ⊆ l₂ := by simp[e]

lemma nil_iff {l : List α} : l = [] ↔ ∀ a, a ∉ l := by
  induction l with
  | nil => simp only [not_mem_nil, not_false_eq_true, implies_true];
  | cons a _ _ =>
    simp_all [mem_cons, not_or]
    use a;
    tauto;

section remove

def remove [DecidableEq α] (a : α) : List α → List α := List.filter (· ≠ a)

variable [DecidableEq α]

@[simp]
lemma remove_nil (a : α) : [].remove a = [] := by simp [List.remove]

@[simp]
lemma eq_remove_cons {l : List α} : (ψ :: l).remove ψ = l.remove ψ := by induction l <;> simp_all [List.remove];

@[simp]
lemma remove_singleton_of_ne {φ ψ : α} (h : φ ≠ ψ) : [φ].remove ψ = [φ] := by simp_all [List.remove, Ne.symm];

lemma mem_remove_iff {l : List α} : b ∈ l.remove a ↔ b ∈ l ∧ b ≠ a := by
  simp [List.remove, List.of_mem_filter]

lemma mem_of_mem_remove {a b : α} {l : List α} (h : b ∈ l.remove a) : b ∈ l := by
  rw [mem_remove_iff] at h; exact h.1

@[simp] lemma remove_cons_self (l : List α) (a) :
  (a :: l).remove a = l.remove a := by simp[remove]

lemma remove_cons_of_ne (l : List α) {a b} (ne : a ≠ b) :
  (a :: l).remove b = a :: l.remove b := by simp_all [remove];

lemma remove_subset (a) (l : List α) :
    l.remove a ⊆ l := by
  simp[subset_def, mem_remove_iff]
  intros; simp[*]

lemma remove_subset_remove (a) {l₁ l₂ : List α} (h : l₁ ⊆ l₂) :
    l₁.remove a ⊆ l₂.remove a := by
  simp[subset_def, mem_remove_iff]; intros; simp[*]; exact h (by assumption)

lemma remove_cons_subset_cons_remove (a b) (l : List α) :
    (a :: l).remove b ⊆ a :: l.remove b := by
  intro x; simp[List.mem_remove_iff]
  rintro (rfl | hx) nex <;> simp[*]

lemma remove_map_substet_map_remove [DecidableEq β] (f : α → β) (l : List α) (a) :
    (l.map f).remove (f a) ⊆ (l.remove a).map f := by
  simp[List.subset_def, List.mem_remove_iff]
  intro b hb neb;
  exact ⟨b, ⟨hb, by rintro rfl; exact neb rfl⟩, rfl⟩

end remove

@[elab_as_elim]
lemma induction_with_singleton
  {motive : List F → Prop}
  (hnil : motive [])
  (hsingle : ∀ a, motive [a])
  (hcons : ∀ a as, as ≠ [] → motive as → motive (a :: as)) : ∀ as, motive as := by
  intro as;
  induction as with
  | nil => exact hnil;
  | cons a as ih => cases as with
    | nil => exact hsingle a;
    | cons b bs => exact hcons a (b :: bs) (by simp) ih;



end List

namespace List.Vector

variable {α : Type*}

lemma get_mk_eq_get {n} (l : List α) (h : l.length = n) (i : Fin n) : List.Vector.get (⟨l, h⟩ : List.Vector α n) i = l.get (i.cast h.symm) := rfl

lemma get_one {α : Type*} {n} (v : Vector α (n + 2)) : v.get 1 = v.tail.head := by
  rw[←Vector.get_zero, Vector.get_tail_succ]; rfl

lemma ofFn_vecCons (a : α) (v : Fin n → α) :
    ofFn (a :> v) = a ::ᵥ ofFn v := by
  ext i; cases i using Fin.cases <;> simp

end List.Vector

namespace Finset

variable {α : Type u} {β : Type v} {γ : Type w}

noncomputable def rangeOfFinite {ι : Sort v} [Finite ι] (f : ι → α) : Finset α :=
  Set.Finite.toFinset (s := Set.range f) (Set.toFinite (Set.range f))

lemma mem_rangeOfFinite_iff  {ι : Sort v} [Finite ι] {f : ι → α} {a : α} :
    a ∈ rangeOfFinite f ↔ ∃ i : ι, f i = a := by simp[rangeOfFinite]

noncomputable def imageOfFinset [DecidableEq β] (s : Finset α) (f : (a : α) → a ∈ s → β) : Finset β :=
  Finset.biUnion s (rangeOfFinite $ f ·)

lemma mem_imageOfFinset_iff [DecidableEq β] {s : Finset α} {f : (a : α) → a ∈ s → β} {b : β} :
    b ∈ imageOfFinset s f ↔ ∃ (a : α) (ha : a ∈ s), f a ha = b := by
  simp[imageOfFinset, mem_rangeOfFinite_iff]
  constructor
  · rintro ⟨a, _, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, ha, rfl⟩

@[simp] lemma mem_imageOfFinset  [DecidableEq β] {s : Finset α} (f : (a : α) → a ∈ s → β) (a : α) (ha : a ∈ s) :
    f a ha ∈ imageOfFinset s f := by simp[mem_imageOfFinset_iff]; exact ⟨a, ha, rfl⟩

lemma erase_union [DecidableEq α] {a : α} {s t : Finset α} :
  (s ∪ t).erase a = (s.erase a) ∪ (t.erase a) := by ext; simp[and_or_left]

@[simp] lemma equiv_univ {α α'} [Fintype α] [Fintype α'] [DecidableEq α'] (e : α ≃ α') :
    (Finset.univ : Finset α).image e = Finset.univ := by ext x; simp

@[simp] lemma sup_univ_equiv {α α'} [DecidableEq α] [Fintype α] [Fintype α'] [SemilatticeSup β] [OrderBot β] (f : α → β) (e : α' ≃ α) :
    Finset.sup Finset.univ (fun i => f (e i)) = Finset.sup Finset.univ f := by
  simpa [Function.comp] using Eq.symm <| Finset.sup_image Finset.univ e f

lemma sup_univ_cast {α : Type _} [SemilatticeSup α] [OrderBot α] {n} (f : Fin n → α) (n') {h : n' = n} :
    Finset.sup Finset.univ (fun (i : Fin n') => f (i.cast h)) = Finset.sup Finset.univ f := by rcases h with rfl; simp

end Finset

namespace Denumerable

lemma lt_of_mem_list : ∀ n i, i ∈ Denumerable.ofNat (List ℕ) n → i < n
  | 0     => by simp
  | n + 1 =>
    have : n.unpair.2 < n + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le n)
    by simp
       exact ⟨Nat.lt_succ_of_le (Nat.unpair_left_le n),
         by { intro i hi
              have : i < n.unpair.2 := lt_of_mem_list n.unpair.2 i hi
              exact lt_trans this (Nat.lt_succ_of_le $ Nat.unpair_right_le n) }⟩

end Denumerable

namespace Part

@[simp] lemma mem_vector_mOfFn : ∀ {n : ℕ} {w : List.Vector α n} {v : Fin n →. α},
    w ∈ List.Vector.mOfFn v ↔ ∀ i, w.get i ∈ v i
  | 0,     _, _ => by simp[List.Vector.mOfFn, List.Vector.eq_nil]
  | n + 1, w, v => by
    simp[List.Vector.mOfFn, @mem_vector_mOfFn _ n]
    exact ⟨by rintro ⟨a, ha, v, hv, rfl⟩ i; cases i using Fin.cases <;> simp[ha, hv],
      by intro h; exact ⟨w.head, by simpa using h 0, w.tail, fun i => by simpa using h i.succ, by simp⟩⟩

end Part

namespace Set

variable {α : Type*}

lemma subset_mem_chain_of_finite (c : Set (Set α)) (hc : Set.Nonempty c) (hchain : IsChain (· ⊆ ·) c)
    {s} (hfin : Set.Finite s) : s ⊆ ⋃₀ c → ∃ t ∈ c, s ⊆ t :=
  Set.Finite.induction_on hfin
    (by rcases hc with ⟨t, ht⟩; intro; exact ⟨t, ht, by simp⟩)
    (by intro a s _ _ ih h
        have : ∃ t ∈ c, s ⊆ t := ih (subset_trans (Set.subset_insert a s) h)
        rcases this with ⟨t, htc, ht⟩
        have : ∃ u ∈ c, a ∈ u := by simp [Set.insert_subset_iff] at h; exact h.1
        rcases this with ⟨u, huc, hu⟩
        have : ∃ z ∈ c, t ⊆ z ∧ u ⊆ z := IsChain.directedOn hchain t htc u huc
        rcases this with ⟨z, hzc, htz, huz⟩
        exact ⟨z, hzc, Set.insert_subset (huz hu) (Set.Subset.trans ht htz)⟩)

end Set

class Exp (α : Type*) where
  exp : α → α
export Exp (exp)

namespace Set

variable (s₁ s₂ s₃ s₄ : Set F)

@[simp] lemma subset_triunion₁ : s₁ ⊆ (s₁ ∪ s₂ ∪ s₃) := Set.Subset.trans Set.subset_union_left Set.subset_union_left

@[simp] lemma subset_triunion₂ : s₂ ⊆ (s₁ ∪ s₂ ∪ s₃) := Set.Subset.trans Set.subset_union_right Set.subset_union_left

@[simp] lemma subset_triunion₃ : s₃ ⊆ (s₁ ∪ s₂ ∪ s₃) := by simp [Set.subset_union_right]


@[simp] lemma subset_tetraunion₁ : s₁ ⊆ (s₁ ∪ s₂ ∪ s₃ ∪ s₄) :=
  Set.Subset.trans
    Set.subset_union_left
    $ Set.Subset.trans Set.subset_union_left Set.subset_union_left

@[simp]
lemma subset_tetraunion₂ : s₂ ⊆ (s₁ ∪ s₂ ∪ s₃ ∪ s₄) :=
  Set.Subset.trans
    Set.subset_union_right
    $ Set.Subset.trans Set.subset_union_left Set.subset_union_left

@[simp] lemma subset_tetraunion₃ : s₃ ⊆ (s₁ ∪ s₂ ∪ s₃ ∪ s₄) := by simp only [subset_triunion₂]
@[simp] lemma subset_tetraunion₄ : s₄ ⊆ (s₁ ∪ s₂ ∪ s₃ ∪ s₄) := by simp only [Set.subset_union_right]

end Set

/-- Class for `α` has at least `n` elements -/
class Atleast (n : ℕ+) (α) where
  mapping : ∃ f : Fin n → α, Function.HasLeftInverse f
