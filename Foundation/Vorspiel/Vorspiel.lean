import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.Logic.Encodable.Basic
import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Set.Finite.Range
import Mathlib.Tactic.TautoSet
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Vector
import Mathlib.Computability.Halting
import Mathlib.Tactic.Cases

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
    simpa [this] using H n (Nat.lt.base n) (n.rec a f₂)

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

@[simp] lemma cons_app_four {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ → α) : (a :> s) 4 = s 3 := rfl

@[simp] lemma cons_app_five {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ → α) : (a :> s) 5 = s 4 := rfl

@[simp] lemma cons_app_six {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ → α) : (a :> s) 6 = s 5 := rfl

@[simp] lemma cons_app_seven {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ.succ → α) : (a :> s) 7 = s 6 := rfl

@[simp] lemma cons_app_eight {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ.succ.succ → α) : (a :> s) 8 = s 7 := rfl

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

end delab

infixl:70 " <: " => vecConsLast

@[simp] lemma rightConcat_last :
    (s <: a) (last n) = a := by simp [vecConsLast]

@[simp] lemma rightConcat_castSucc (i : Fin n) :
    (s <: a) (Fin.castSucc i) = s i := by simp [vecConsLast]

@[simp] lemma rightConcat_zero (a : α) (s : Fin n.succ → α) :
    (s <: a) 0 = s 0 := rightConcat_castSucc 0

@[simp] lemma zero_succ_eq_id {n} : (0 : Fin (n + 1)) :> succ = id :=
  funext $ Fin.cases (by simp) (by simp)

@[simp] lemma zero_cons_succ_eq_self (f : Fin (n + 1) → α) : (f 0 :> (f ·.succ) : Fin (n + 1) → α) = f := by
    funext x; cases x using Fin.cases <;> simp

lemma eq_vecCons (s : Fin (n + 1) → C) : s 0 :> s ∘ Fin.succ = s :=
   funext $ Fin.cases (by simp) (by simp)

lemma eq_vecCons' (s : Fin (n + 1) → C) : s 0 :> (s ·.succ) = s :=
   funext $ Fin.cases (by simp) (by simp)

@[simp] lemma vecCons_ext (a₁ a₂ : α) (s₁ s₂ : Fin n → α) :
    a₁ :> s₁ = a₂ :> s₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  ⟨by intros h
      constructor
      · exact congrFun h 0
      · exact funext (fun i => by simpa using congrFun h (Fin.castSucc i + 1)),
   by intros h; simp [h]⟩

lemma vecCons_assoc (a b : α) (s : Fin n → α) :
    a :> (s <: b) = (a :> s) <: b := by
  funext x; cases' x using Fin.cases with x
  · simp
  · cases x using Fin.lastCases
    · simp
    case cast i =>
      simp; simp only [rightConcat_castSucc, Fin.succ_castSucc i, cons_val_succ]

def decVec {α : Type _} : {n : ℕ} → (v w : Fin n → α) → (∀ i, Decidable (v i = w i)) → Decidable (v = w)
  | 0,     _, _, _ => by simpa [Matrix.empty_eq] using isTrue trivial
  | n + 1, v, w, d => by
      rw [←eq_vecCons v, ←eq_vecCons w, vecCons_ext]
      haveI : Decidable (v ∘ Fin.succ = w ∘ Fin.succ) := decVec _ _ (by intros i; simpa using d _)
      refine instDecidableAnd

lemma comp_vecCons (f : α → β) (a : α) (s : Fin n → α) :
    (fun x ↦ f <| (a :> s) x) = f a :> f ∘ s :=
  funext (fun i => cases (by simp) (by simp) i)

lemma comp_vecCons' (f : α → β) (a : α) (s : Fin n → α) :
    (fun x ↦ f <| (a :> s) x) = f a :> fun i ↦ f (s i) :=
  comp_vecCons f a s

lemma comp_vecCons'' (f : α → β) (a : α) (s : Fin n → α) : f ∘ (a :> s) = f a :> f ∘ s :=
  comp_vecCons f a s

lemma comp_vecCons₂' (g : β → γ) (f : α → β) (a : α) (s : Fin n → α) :
    (fun x ↦ g <| f <| (a :> s) x) = (g (f a) :> fun i ↦ g <| f <| s i) := by
  funext x
  cases x using Fin.cases <;> simp

@[simp] lemma comp₀ : f ∘ (![] : Fin 0 → α) = ![] := by simp [Matrix.empty_eq]

@[simp] lemma comp₁ (a : α) : f ∘ ![a] = ![f a] := by simp [comp_vecCons'']

@[simp] lemma comp₂ (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] := by simp [comp_vecCons'']

@[simp] lemma comp₃ (a₁ a₂ a₃ : α) : f ∘ ![a₁, a₂, a₃] = ![f a₁, f a₂, f a₃] := by simp [comp_vecCons'']

lemma comp_vecConsLast (f : α → β) (a : α) (s : Fin n → α) : (fun x => f $ (s <: a) x) = f ∘ s <: f a :=
funext (fun i => lastCases (by simp) (by simp) i)

@[simp] lemma vecHead_comp (f : α → β) (v : Fin (n + 1) → α) : vecHead (f ∘ v) = f (vecHead v) :=
  by simp [vecHead]

@[simp] lemma vecTail_comp (f : α → β) (v : Fin (n + 1) → α) : vecTail (f ∘ v) = f ∘ (vecTail v) := by
  simp [vecTail, Function.comp_assoc]

lemma vecConsLast_vecEmpty {s : Fin 0 → α} (a : α) : s <: a = ![a] :=
  funext (fun x => by
    have : 0 = Fin.last 0 := by rfl
    cases' x using Fin.cases with i
    · rw [this, rightConcat_last, cons_val_fin_one]
    have := i.isLt; contradiction )

lemma constant_eq_singleton {a : α} : (fun _ => a) = ![a] := by funext x; simp

lemma fun_eq_vec_one {v : Fin 1 → α} : v = ![v 0] := by funext x; simp [Fin.eq_zero]

lemma constant_eq_vec₂ {a : α} : (fun _ => a) = ![a, a] := by
  funext x; cases x using Fin.cases <;> simp [Fin.eq_zero]

lemma fun_eq_vec_two {v : Fin 2 → α} : v = ![v 0, v 1] := by
  funext x; cases x using Fin.cases <;> simp [Fin.eq_zero]

lemma fun_eq_vec_three {v : Fin 3 → α} : v = ![v 0, v 1, v 2] := by
  funext x
  cases' x using Fin.cases with x <;> simp
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]

lemma fun_eq_vec_four {v : Fin 4 → α} : v = ![v 0, v 1, v 2, v 3] := by
  funext x
  cases' x using Fin.cases with x <;> simp
  cases' x using Fin.cases with x <;> simp
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]

lemma injective_vecCons {f : Fin n → α} (h : Function.Injective f) {a} (ha : ∀ i, a ≠ f i) : Function.Injective (a :> f) := by
  have : ∀ i, f i ≠ a := fun i => (ha i).symm
  intro i j; cases i using Fin.cases <;> cases j using Fin.cases
  · simp
  · simp [*]
  · simp [*]
  · simpa using @h _ _

@[simp] lemma vecCons_empty_eq_singleton (v : Fin 0 → α) (x : α) : x :> v = ![x] := by
  ext i
  rcases fin_one_eq_zero i
  simp

@[simp] lemma vecConsLast_empty_eq_singleton (v : Fin 0 → α) (x : α) : v <: x = ![x] := by
  ext i
  rcases fin_one_eq_zero i
  simp [vecConsLast]
  rfl

end

variable {α : Type _}

def toList : {n : ℕ} → (Fin n → α) → List α
  | 0,     _ => []
  | _ + 1, v => v 0 :: toList (v ∘ Fin.succ)

@[simp] lemma toList_zero (v : Fin 0 → α) : toList v = [] := rfl

@[simp] lemma toList_succ (v : Fin (n + 1) → α) : toList v = v 0 :: toList (v ∘ Fin.succ) := rfl

@[simp] lemma toList_length (v : Fin n → α) : (toList v).length = n :=
  by induction n <;> simp [*]

@[simp] lemma mem_toList_iff {v : Fin n → α} {a} : a ∈ toList v ↔ ∃ i, v i = a := by
  induction n
  · simp [*]
  · suffices (a = v 0 ∨ ∃ i : Fin _, v i.succ = a) ↔ ∃ i, v i = a by simp [*]
    constructor
    · rintro (rfl | ⟨i, rfl⟩) <;> simp
    · rintro ⟨i, rfl⟩; cases i using Fin.cases <;> simp

variable {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}

def getM : {n : ℕ} → {β : Fin n → Type u} → ((i : Fin n) → m (β i)) → m ((i : Fin n) → β i)
  | 0,     _, _ => pure finZeroElim
  | _ + 1, _, f => Fin.cases <$> f 0 <*> getM (f ·.succ)

lemma getM_pure [LawfulMonad m] {n} {β : Fin n → Type u} (v : (i : Fin n) → β i) :
    getM (fun i => (pure (v i) : m (β i))) = pure v := by
  induction' n with n ih
  · unfold getM; congr; funext x; exact x.elim0
  · simp only [getM, map_pure, ih, seq_pure]
    exact congr_arg _ (funext <| Fin.cases rfl fun i ↦ rfl)

@[simp] lemma getM_some {n} {β : Fin n → Type u} (v : (i : Fin n) → β i) :
    getM (fun i => (some (v i) : Option (β i))) = some v := getM_pure v

def appendr {n m} (v : Fin n → α) (w : Fin m → α) : Fin (m + n) → α := Matrix.vecAppend (add_comm m n) v w

@[simp] lemma appendr_nil {m} (w : Fin m → α) : appendr ![] w = w := by funext i; simp [appendr]

@[simp] lemma appendr_cons {m n} (x : α) (v : Fin n → α) (w : Fin m → α) : appendr (x :> v) w = x :> appendr v w := by funext i; simp [appendr]

lemma forall_iff {n : ℕ} (φ : (Fin (n + 1) → α) → Prop) :
    (∀ v, φ v) ↔ (∀ a, ∀ v, φ (a :> v)) :=
  ⟨fun h a v ↦ h (a :> v), fun h v ↦ by simpa [eq_vecCons v] using h (v 0) (v ∘ Fin.succ)⟩

lemma exists_iff {n : ℕ} (φ : (Fin (n + 1) → α) → Prop) :
    (∃ v, φ v) ↔ (∃ a, ∃ v, φ (a :> v)) :=
  ⟨by rintro ⟨v, hv⟩; exact ⟨v 0, v ∘ Fin.succ, by simpa [eq_vecCons] using hv⟩,
   by rintro ⟨a, v, hv⟩; exact ⟨_, hv⟩⟩

def foldr (f : α → β → β) (init : β) : {k : ℕ} → (Fin k → α) → β
  |     0, _ => init
  | _ + 1, v => f (vecHead v) (Matrix.foldr f init (vecTail v))

def map (f : α → β) : (Fin k → α) → (Fin k → β) := fun v ↦ f ∘ v

section map

postfix:max "⨟" => map

variable (f : α → β)

@[simp] lemma map_nil (v : Fin 0 → α) : f⨟ v = ![] := empty_eq (f⨟ v)

@[simp] lemma map_cons (a : α) (v : Fin k → α) : f⨟ (a :> v) = f a :> f⨟ v := by
  ext i
  cases i using Fin.cases <;> simp [map]

@[simp] lemma map_cons' (v : Fin (k + 1) → α) : f⨟ v = f (vecHead v) :> f⨟ (vecTail v) := by
  ext i
  cases i using Fin.cases <;> { simp [map]; rfl }

@[simp] lemma map_app (v : Fin k → α) (i : Fin k) : (f⨟ v) i = f (v i) := rfl

lemma map_map_comp (g : β → γ) (f : α → β) (v : Fin k → α) :
    g⨟ (f⨟ v) = (g ∘ f)⨟ v := by ext x; simp

lemma map_map_comp' (g : β → γ) (f : α → β) (v : Fin k → α) :
    g⨟ (f⨟ v) = (fun x ↦ g (f x))⨟ v := by ext x; simp

end map
section foldr

variable (f : α → β → β) (init : β)

@[simp] lemma foldr_zero (v : Fin 0 → α) : foldr f init v = init := rfl

@[simp] lemma foldr_succ (v : Fin (k + 1) → α) : foldr f init v = f (vecHead v) (foldr f init (vecTail v)) := rfl

end foldr

def foldl (f : α → β → α) : (init : α) → {k : ℕ} → (Fin k → β) → α
  | a,     0, _ => a
  | a, _ + 1, v => Matrix.foldl f (f a (vecHead v)) (vecTail v)

section foldl

variable (f : α → β → α) (init : α)

@[simp] lemma foldl_zero (v : Fin 0 → β) : foldl f init v = init := rfl

@[simp] lemma foldl_succ (v : Fin (k + 1) → β) : foldl f init v = foldl f (f init (vecHead v)) (vecTail v) := rfl

end foldl

lemma eq_iff_eq_vecHead_of_eq_vecTail {v₁ v₂ : Fin (n + 1) → α} :
    Matrix.vecHead v₁ = Matrix.vecHead v₂ ∧ Matrix.vecTail v₁ = Matrix.vecTail v₂ ↔ v₁ = v₂ := by
  constructor
  · rintro ⟨h, t⟩
    ext i; cases i using Fin.cases
    · exact h
    · exact congr_fun t _
  · rintro rfl; simp

section vecToNat

def vecToNat (v : Fin n → ℕ) : ℕ := foldr (fun x ih ↦ Nat.pair x ih + 1) 0 v

open Encodable

@[simp] lemma vecToNat_empty (v : Fin 0 → ℕ) : vecToNat v = 0 := by rfl

@[simp] lemma encode_succ {n} (x : ℕ) (v : Fin n → ℕ) : vecToNat (x :> v) = Nat.pair x (vecToNat v) + 1 := by
  simp [vecToNat]

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
   by intros h; simp [h]⟩

def decVec {n : ℕ} {α : Fin n → Type _}
  (v w : (i : Fin n) → α i) (h : ∀ i, Decidable (v i = w i)) : Decidable (v = w) := by
    induction' n with n ih
    · exact isTrue (by funext x; exact finZeroElim (α := fun x => v x = w x) x)
    · rw [eq_vecCons v, eq_vecCons w, vecCons_ext]
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
  induction n
  · simp [*, Nat.natToVec, vecToNat, Matrix.empty_eq]
  case succ _ ih =>
    suffices v 0 :> v ∘ Fin.succ = v by
      simp only [vecToNat, foldr_succ, natToVec, unpair_pair, Option.map_eq_some_iff]
      use vecTail v
      simpa using ih (vecTail v)
    exact funext (fun i ↦ i.cases (by simp) (by simp))

lemma lt_of_eq_natToVec {e : ℕ} {v : Fin n → ℕ} (h : e.natToVec n = some v) (i : Fin n) : v i < e := by
  induction' n with n ih generalizing e
  · exact i.elim0
  · cases' e with e
    · simp [natToVec] at h
    · simp only [natToVec, Option.map_eq_some_iff] at h
      rcases h with ⟨v, hnv, rfl⟩
      cases' i using Fin.cases with i
      · simp [lt_succ, unpair_left_le]
      · simp only [cons_val_succ]
        exact lt_trans (ih hnv i) (lt_succ.mpr <| unpair_right_le e)

lemma one_le_of_bodd {n : ℕ} (h : n.bodd = true) : 1 ≤ n :=
by induction n <;> simp at h ⊢

lemma pair_le_pair_of_le {a₁ a₂ b₁ b₂ : ℕ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) : a₁.pair b₁ ≤ a₂.pair b₂ := by
  rcases lt_or_eq_of_le ha with (ha | rfl) <;> rcases lt_or_eq_of_le hb with (hb | rfl)
  · exact le_of_lt (lt_trans (Nat.pair_lt_pair_left b₁ ha) (Nat.pair_lt_pair_right a₂ hb))
  · exact le_of_lt (Nat.pair_lt_pair_left b₁ ha)
  · exact le_of_lt (Nat.pair_lt_pair_right a₁ hb)
  · rfl

end Nat

namespace Fin

lemma pos_of_coe_ne_zero {i : Fin (n + 1)} (h : (i : ℕ) ≠ 0) :
    0 < i := Nat.pos_of_ne_zero h

@[simp] lemma one_pos'' : (0 : Fin (n + 2)) < 1 := pos_of_coe_ne_zero (Nat.succ_ne_zero 0)

@[simp] lemma two_pos : (0 : Fin (n + 3)) < 2 := pos_of_coe_ne_zero (Nat.succ_ne_zero 1)

@[simp] lemma three_pos : (0 : Fin (n + 4)) < 3 := pos_of_coe_ne_zero (Nat.succ_ne_zero 2)

@[simp] lemma four_pos : (0 : Fin (n + 5)) < 4 := pos_of_coe_ne_zero (Nat.succ_ne_zero 3)

@[simp] lemma five_pos : (0 : Fin (n + 6)) < 5 := pos_of_coe_ne_zero (Nat.succ_ne_zero 4)

lemma forall_fin_iff_zero_and_forall_succ {P : Fin (k + 1) → Prop} : (∀ i, P i) ↔ P 0 ∧ ∀ i : Fin k, P i.succ :=
  ⟨fun h ↦ ⟨h 0, fun i ↦ h i.succ⟩, by
    rintro ⟨hz, hs⟩ i
    cases' i using Fin.cases with i
    · exact hz
    · exact hs i⟩

lemma exists_fin_iff_zero_or_exists_succ {P : Fin (k + 1) → Prop} : (∃ i, P i) ↔ P 0 ∨ ∃ i : Fin k, P i.succ :=
  ⟨by rintro ⟨i, hi⟩
      cases i using Fin.cases
      · left; exact hi
      · right; exact ⟨_, hi⟩,
   by rintro (hz | ⟨i, h⟩)
      · exact ⟨0, hz⟩
      · exact ⟨_, h⟩⟩

lemma forall_vec_iff_forall_forall_vec {P : (Fin (k + 1) → α) → Prop} :
    (∀ v : Fin (k + 1) → α, P v) ↔ ∀ x, ∀ v : Fin k → α, P (x :> v) := by
  constructor
  · intro h x v; exact h _
  · intro h v; simpa using h (v 0) (v ·.succ)

lemma exists_vec_iff_exists_exists_vec {P : (Fin (k + 1) → α) → Prop} :
    (∃ v : Fin (k + 1) → α, P v) ↔ ∃ x, ∃ v : Fin k → α, P (x :> v) := by
  constructor
  · rintro ⟨v, h⟩; exact ⟨v 0, (v ·.succ), by simpa using h⟩
  · rintro ⟨x, v, h⟩; exact ⟨_, h⟩

lemma exists_le_vec_iff_exists_le_exists_vec [LE α] {P : (Fin (k + 1) → α) → Prop} {f : Fin (k + 1) → α} :
    (∃ v ≤ f, P v) ↔ ∃ x ≤ f 0, ∃ v ≤ (f ·.succ), P (x :> v) := by
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨w 0, hw 0, (w ·.succ), fun i ↦ hw i.succ, by simpa using h⟩
  · rintro ⟨x, hx, v, hv, h⟩
    refine ⟨x :> v, ?_, h⟩
    intro i; cases' i using Fin.cases with i
    · exact hx
    · exact hv i

lemma forall_le_vec_iff_forall_le_forall_vec [LE α] {P : (Fin (k + 1) → α) → Prop} {f : Fin (k + 1) → α} :
    (∀ v ≤ f, P v) ↔ ∀ x ≤ f 0, ∀ v ≤ (f ·.succ), P (x :> v) := by
  constructor
  · intro h x hx v hv
    refine h (x :> v) ?_
    intro i; cases' i using Fin.cases with i
    · exact hx
    · exact hv i
  · intro h v hv
    simpa using h (v 0) (hv 0) (v ·.succ) (hv ·.succ)

@[inline] def addCast (m) : Fin n → Fin (m + n) :=
  castLE <| Nat.le_add_left n m

@[simp] lemma addCast_val (i : Fin n) : (i.addCast m : ℕ) = i := rfl

end Fin

namespace Matrix

variable {α : Type*}

@[simp] lemma appeendr_addCast (u : Fin m → α) (v : Fin n → α) (i : Fin m) :
    appendr u v (i.addCast n) = u i := by simp [appendr, vecAppend_eq_ite]

@[simp] lemma appeendr_addNat (u : Fin m → α) (v : Fin n → α) (i : Fin n) :
    appendr u v (i.addNat m) = v i := by simp [appendr, vecAppend_eq_ite]

end Matrix

namespace Fintype
variable {ι : Type _} [Fintype ι]

section

variable {α : Type _} [SemilatticeSup α] [OrderBot α]

def sup (f : ι → α) : α := (Finset.univ : Finset ι).sup f

@[simp] lemma elem_le_sup (f : ι → α) (i : ι) : f i ≤ sup f := Finset.le_sup (by simp)

lemma le_sup {a : α} {f : ι → α} (i : ι) (le : a ≤ f i) : a ≤ sup f := le_trans le (elem_le_sup _ _)

@[simp] lemma sup_le_iff {f : ι → α} {a : α} :
    sup f ≤ a ↔ (∀ i, f i ≤ a) := by simp [sup]

@[simp] lemma finsup_eq_0_of_empty [IsEmpty ι] (f : ι → α) : sup f = ⊥ := by simp [sup]

end

def decideEqPi {β : ι → Type*} (a b : (i : ι) → β i) (_ : (i : ι) → Decidable (a i = b i)) : Decidable (a = b) :=
  decidable_of_iff (∀ i, a i = b i) funext_iff.symm

end Fintype

namespace String

def vecToStr : ∀ {n}, (Fin n → String) → String
  | 0,     _ => ""
  | n + 1, s => if n = 0 then s 0 else s 0 ++ ", " ++ @vecToStr n (fun i => s (Fin.succ i))

end String

namespace Empty

lemma eq_elim {α : Sort u} (f : Empty → α) : f = elim := funext (by rintro ⟨⟩)

end Empty

namespace IsEmpty
variable {o : Sort u} (h : IsEmpty o)

lemma eq_elim' {α : Sort*} (f : o → α) : f = h.elim' := funext h.elim

lemma eq_elim {α : Sort*} (f : o → α) : f = h.elim := funext h.elim

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
      (fun v₁ v₂ hv => h (a :> v₁) (a :> v₂) (Fin.cases (by simp) hv)) v
  Quot.liftOn (vecHead v) (ih · (vecTail v))
    (fun a b hab => by
      have : ∀ v, f (a :> v) = f (b :> v) := fun v ↦ h _ _ (Fin.cases hab (by simp))
      simp [this, ih])

@[simp] lemma liftVec_zero (f : (Fin 0 → α) → β) (h) (v : Fin 0 → Quotient s) : liftVec f h v = f ![] := rfl

lemma liftVec_mk {n} (f : (Fin n → α) → β) (h) (v : Fin n → α) :
    liftVec f h (Quotient.mk s ∘ v) = f v := by
  induction' n with n ih <;> simp [liftVec, empty_eq]
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
  induction' l with n ns ih
  case nil => simp at h
  case cons m =>
    suffices m < n + 1 ∨ m < ns.upper by simpa
    rcases show m = n ∨ m ∈ ns by simpa using h with (rfl | h)
    · exact Or.inl (Nat.lt_succ_self _)
    · exact Or.inr (ih h)

section finset

variable [DecidableEq α] [DecidableEq β]

lemma toFinset_map {f : α → β} (l : List α) : (l.map f).toFinset = Finset.image f l.toFinset := by
  induction l <;> simp [*]

lemma toFinset_mono {l l' : List α} (h : l ⊆ l') : l.toFinset ⊆ l'.toFinset := by
  intro a; simp only [mem_toFinset]; intro ha; exact h ha

end finset

section sup

variable [SemilatticeSup α] [OrderBot α]

def sup : List α → α
  |      [] => ⊥
  | a :: as => a ⊔ as.sup

@[simp] lemma sup_nil : ([] : List α).sup = ⊥ := rfl

@[simp] lemma sup_cons (a : α) (as : List α) : (a :: as).sup = a ⊔ as.sup := rfl

lemma le_sup {a} {l : List α} : a ∈ l → a ≤ l.sup := by
  induction' l with a l ih
  · simp
  case cons _ b =>
    intro h
    rcases show b = a ∨ b ∈ l by simpa using h with (rfl | h)
    · simp
    · exact le_sup_of_le_right (ih h)

lemma sup_ofFn (f : Fin n → α) : (ofFn f).sup = Finset.sup Finset.univ f := by
  induction' n with n ih
  · simp
  · have h₁ : (Finset.univ : Finset (Fin (n + 1))) = insert 0 ((Finset.univ : Finset (Fin n)).image Fin.succ) := by
      ext i; simp
    have h₂ : Finset.sup Finset.univ (fun i ↦ f (Fin.succ i)) = Finset.sup {0}ᶜ f := by
      simpa [Function.comp] using Eq.symm <| Finset.sup_image (Finset.univ : Finset (Fin n)) Fin.succ f
    calc
      (ofFn f).sup = (f 0 ⊔ Finset.univ.sup fun i : Fin _ ↦ f i.succ) := by simp [ih]
      _            = f 0 ⊔ Finset.sup {0}ᶜ f                          := by rw [h₂]
      _            = Finset.univ.sup f                                := by rw [h₁, Finset.sup_insert]; simp

end sup

lemma ofFn_get_eq_map_cast {n} (g : α → β) (as : List α) {h} :
    ofFn (fun i => g (as.get (i.cast h)) : Fin n → β) = as.map g := by
  ext i b; simp
  by_cases hi : i < n
  · simp [hi, List.getElem?_eq_getElem (h ▸ hi)]
  · simp [hi, List.getElem?_eq_none (le_of_not_gt $ h ▸ hi)]

variable {m : Type _ → Type _} {α : Type _} {β : Type _} [Monad m]

lemma append_subset_append {l₁ l₂ l : List α} (h : l₁ ⊆ l₂) : l₁ ++ l ⊆ l₂ ++ l :=
  List.append_subset.mpr ⟨List.subset_append_of_subset_left _ h, subset_append_right l₂ l⟩

lemma subset_of_eq {l₁ l₂ : List α} (e : l₁ = l₂) : l₁ ⊆ l₂ := by simp [e]

section remove

def remove [DecidableEq α] (a : α) : List α → List α := List.filter (· ≠ a)

variable [DecidableEq α]

@[simp]
lemma remove_nil (a : α) : [].remove a = [] := by simp [List.remove]

@[simp]
lemma eq_remove_cons {l : List α} : (ψ :: l).remove ψ = l.remove ψ := by induction l <;> simp_all [List.remove];

@[simp]
lemma remove_singleton_of_ne {φ ψ : α} (h : φ ≠ ψ) : [φ].remove ψ = [φ] := by simp_all [List.remove];

lemma mem_remove_iff {l : List α} : b ∈ l.remove a ↔ b ∈ l ∧ b ≠ a := by
  simp [List.remove]

lemma mem_of_mem_remove {a b : α} {l : List α} (h : b ∈ l.remove a) : b ∈ l := by
  rw [mem_remove_iff] at h; exact h.1

@[simp] lemma remove_cons_self (l : List α) (a) :
  (a :: l).remove a = l.remove a := by simp [remove]

lemma remove_cons_of_ne (l : List α) {a b} (ne : a ≠ b) :
  (a :: l).remove b = a :: l.remove b := by simp_all [remove];

@[simp] lemma remove_subset (a) (l : List α) :
    l.remove a ⊆ l := by
  simp only [subset_def, mem_remove_iff, ne_eq, and_imp]
  intros; simp [*]

@[simp] lemma subset_cons_remove (a) (l : List α) :
    l ⊆ a :: l.remove a := by
  simp only [subset_def, mem_cons, mem_remove_iff, ne_eq]
  intro b; tauto

lemma remove_subset_remove (a) {l₁ l₂ : List α} (h : l₁ ⊆ l₂) :
    l₁.remove a ⊆ l₂.remove a := by
  simp only [subset_def, mem_remove_iff, ne_eq, and_imp]
  intros
  simpa [*] using h (by assumption)

lemma remove_cons_subset_cons_remove (a b) (l : List α) :
    (a :: l).remove b ⊆ a :: l.remove b := by
  intro x
  simp only [mem_remove_iff, mem_cons, ne_eq, and_imp]
  rintro (rfl | hx) nex <;> simp [*]

lemma remove_map_substet_map_remove [DecidableEq β] (f : α → β) (l : List α) (a) :
    (l.map f).remove (f a) ⊆ (l.remove a).map f := by
  simp only [subset_def, mem_remove_iff, mem_map, ne_eq, and_imp, forall_exists_index,
    forall_apply_eq_imp_iff₂]
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

@[elab_as_elim]
def induction_with_singleton'
  {motive : List α → Sort*}
  (hnil : motive [])
  (hsingle : ∀ a, motive [a])
  (hcons : ∀ a b as, motive (b :: as) → motive (a :: b :: as)) : ∀ as, motive as
  |           [] => hnil
  |          [a] => hsingle a
  | a :: b :: as => hcons a b as (induction_with_singleton' hnil hsingle hcons (b :: as))

instance Nodup.finite [Finite α] : Finite {l : List α // l.Nodup} := by
  haveI : Fintype α := Fintype.ofFinite α
  let N := Fintype.card α + 1
  have : Fintype ((i : Fin N) × Vector α i) := Sigma.instFintype
  let f : {l : List α // l.Nodup} → ((i : Fin N) × Vector α i) := fun l ↦
    ⟨⟨l.val.length, Nat.lt_add_one_of_le <| l.prop.length_le_card⟩, l, by simp⟩
  have : Function.Injective f := by
    intro ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ H
    simpa [f] using congrArg (fun p ↦ p.2.val) H
  exact Finite.of_injective f this

section suffix

lemma suffix_of_cons_suffix {l₁ l₂ : List α} {a} : a :: l₁ <:+ l₂ → l₁ <:+ l₂ := by rintro ⟨l₂, rfl⟩; exact ⟨l₂ ++ [a], by simp⟩

lemma suffix_cons_of {l₁ l₂ : List α} {a} : l₁ <:+ l₂ → l₁ <:+ a :: l₂ := fun h ↦ suffix_cons_iff.mpr <| Or.inr h

lemma exists_of_not_suffix (l₁ l₂ : List α) : ¬l₁ <:+ l₂ → ∃ l a, a :: l <:+ l₁ ∧ l <:+ l₂ ∧ ¬a :: l <:+ l₂ :=
  match l₁ with
  |      [] => by simp
  | a :: l₁ => by
    intro h
    by_cases h₁₂ : l₁ <:+ l₂
    · exact ⟨l₁, a, by simp_all⟩
    · rcases exists_of_not_suffix l₁ l₂ h₁₂ with ⟨l, b, hb, hll₂, nh⟩
      exact ⟨l, b, suffix_cons_of hb, hll₂, nh⟩

lemma IsSuffix.eq_or_cons_suffix : l₁ <:+ l₂ → l₁ = l₂ ∨ ∃ a, a :: l₁ <:+ l₂ := by
  rintro ⟨l, rfl⟩
  rcases eq_nil_or_concat' l with (rfl | ⟨l, a, rfl⟩)
  · simp
  · right; exact ⟨a, l, by simp⟩

lemma suffix_trichotomy {l₁ l₂ : List α} (h₁₂ : ¬l₁ <:+ l₂) (h₂₁ : ¬l₂ <:+ l₁) : ∃ l a b, a ≠ b ∧ a :: l <:+ l₁ ∧ b :: l <:+ l₂ := by
  rcases exists_of_not_suffix _ _ h₁₂ with ⟨l, a, ha, hkl, _⟩
  have : ∃ b, b :: l <:+ l₂ := by
    rcases hkl.eq_or_cons_suffix with (rfl | h)
    · have : l <:+ l₁ := suffix_of_cons_suffix ha
      contradiction
    exact h
  rcases this with ⟨b, hb⟩
  exact ⟨l, a, b, by rintro rfl; contradiction, ha, hb⟩

end suffix

end List

namespace List.Vector

variable {α : Type*}

lemma get_mk_eq_get {n} (l : List α) (h : l.length = n) (i : Fin n) : List.Vector.get (⟨l, h⟩ : List.Vector α n) i = l.get (i.cast h.symm) := rfl

lemma get_one {α : Type*} {n} (v : Vector α (n + 2)) : v.get 1 = v.tail.head := by
  rw [←Vector.get_zero, Vector.get_tail_succ]; rfl

lemma ofFn_vecCons (a : α) (v : Fin n → α) :
    ofFn (a :> v) = a ::ᵥ ofFn v := by
  ext i; cases i using Fin.cases <;> simp

lemma cons_get (a : α) (v : List.Vector α k) : (a ::ᵥ v).get = a :> v.get := by
  ext i; cases i using Fin.cases <;> simp

end List.Vector

namespace Finset

variable {α : Type u} {β : Type v} {γ : Type w}

noncomputable def rangeOfFinite {ι : Sort v} [Finite ι] (f : ι → α) : Finset α :=
  Set.Finite.toFinset (s := Set.range f) (Set.finite_range f)

lemma mem_rangeOfFinite_iff  {ι : Sort v} [Finite ι] {f : ι → α} {a : α} :
    a ∈ rangeOfFinite f ↔ ∃ i : ι, f i = a := by simp [rangeOfFinite]

noncomputable def imageOfFinset [DecidableEq β] (s : Finset α) (f : (a : α) → a ∈ s → β) : Finset β :=
  Finset.biUnion s (rangeOfFinite $ f ·)

lemma mem_imageOfFinset_iff [DecidableEq β] {s : Finset α} {f : (a : α) → a ∈ s → β} {b : β} :
    b ∈ imageOfFinset s f ↔ ∃ (a : α) (ha : a ∈ s), f a ha = b := by
  simp [imageOfFinset, mem_rangeOfFinite_iff]

@[simp] lemma mem_imageOfFinset  [DecidableEq β] {s : Finset α} (f : (a : α) → a ∈ s → β) (a : α) (ha : a ∈ s) :
    f a ha ∈ imageOfFinset s f := by simpa [mem_imageOfFinset_iff] using ⟨a, ha, rfl⟩

lemma erase_union [DecidableEq α] {a : α} {s t : Finset α} :
  (s ∪ t).erase a = (s.erase a) ∪ (t.erase a) := by ext; simp [and_or_left]

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
  |     0 => by simp
  | n + 1 => by
    have : n.unpair.2 < n + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le n)
    suffices (Nat.unpair n).1 < n + 1 ∧ ∀ a ∈ ofNat (List ℕ) (Nat.unpair n).2, a < n + 1 by simpa
    constructor
    · exact Nat.lt_succ_of_le (Nat.unpair_left_le n)
    · intro i hi
      have : i < n.unpair.2 := lt_of_mem_list n.unpair.2 i hi
      exact lt_trans this (Nat.lt_succ_of_le $ Nat.unpair_right_le n)

end Denumerable

namespace Part

@[simp] lemma mem_vector_mOfFn : ∀ {n : ℕ} {w : List.Vector α n} {v : Fin n →. α},
    w ∈ List.Vector.mOfFn v ↔ ∀ i, w.get i ∈ v i
  |     0, _, _ => by simp [List.Vector.mOfFn, List.Vector.eq_nil]
  | n + 1, w, v => by
    suffices (∃ a ∈ v 0, ∃ u, (∀ (i : Fin n), u.get i ∈ v i.succ) ∧ w = a ::ᵥ u) ↔ ∀ (i : Fin (n + 1)), w.get i ∈ v i by
      simpa [List.Vector.mOfFn, @mem_vector_mOfFn _ n]
    constructor
    · rintro ⟨a, ha, v, hv, rfl⟩ i; cases i using Fin.cases <;> simp [ha, hv]
    · intro h; exact ⟨w.head, by simpa using h 0, w.tail, fun i => by simpa using h i.succ, by simp⟩

lemma unit_dom_iff (x : Part Unit) : x.Dom ↔ () ∈ x := by simp [dom_iff_mem, show ∀ x : Unit, x = () by intro x; rfl]

end Part

namespace Set

variable {α : Type*}

lemma subset_mem_chain_of_finite (c : Set (Set α)) (hc : Set.Nonempty c) (hchain : IsChain (· ⊆ ·) c)
    {s} (hfin : Set.Finite s) : s ⊆ ⋃₀ c → ∃ t ∈ c, s ⊆ t :=
  Set.Finite.induction_on s hfin
    (by rcases hc with ⟨t, ht⟩; intro; exact ⟨t, ht, by simp⟩)
    (by intro a s _ _ ih h
        have : ∃ t ∈ c, s ⊆ t := ih (subset_trans (Set.subset_insert a s) h)
        rcases this with ⟨t, htc, ht⟩
        have : ∃ u ∈ c, a ∈ u := by
          have : (∃ t ∈ c, a ∈ t) ∧ s ⊆ ⋃₀ c := by simpa [Set.insert_subset_iff] using h
          exact this.1
        rcases this with ⟨u, huc, hu⟩
        have : ∃ z ∈ c, t ⊆ z ∧ u ⊆ z := IsChain.directedOn hchain t htc u huc
        rcases this with ⟨z, hzc, htz, huz⟩
        exact ⟨z, hzc, Set.insert_subset (huz hu) (Set.Subset.trans ht htz)⟩)

@[simp] lemma subset_union_three₁ (s t u : Set α) : s ⊆ s ∪ t ∪ u := Set.subset_union_of_subset_left (by simp) _

@[simp] lemma subset_union_three₂ (s t u : Set α) : t ⊆ s ∪ t ∪ u := Set.subset_union_of_subset_left (by simp) _

@[simp] lemma subset_union_three₃ (s t u : Set α) : u ⊆ s ∪ t ∪ u := Set.subset_union_of_subset_right (by rfl) _

end Set

namespace ToString

instance : ToString Empty := ⟨Empty.elim⟩

end ToString

namespace Nonempty

instance [Zero α] : Nonempty α := ⟨0⟩

end Nonempty

/-- Class for `α` has at least `n` elements -/
class Atleast (n : ℕ+) (α) where
  mapping : ∃ f : Fin n → α, Function.HasLeftInverse f

namespace Nat.Partrec

open Part _root_.Primrec

lemma projection {f : ℕ →. ℕ} (hf : Nat.Partrec f) (unif : ∀ {m n₁ n₂ a₁ a₂ : ℕ}, a₁ ∈ f (m.pair n₁) → a₂ ∈ f (m.pair n₂) → a₁ = a₂) :
    ∃ g : ℕ →. ℕ, Nat.Partrec g ∧ (∀ a m, a ∈ g m ↔ ∃ z, a ∈ f (m.pair z)) := by
  obtain ⟨cf, rfl⟩ := Code.exists_code.1 hf
  let F : ℕ → ℕ → Option ℕ := fun m n ↦ Nat.rec .none (fun x ih ↦ ih.casesOn (cf.evaln n (m.pair x)) .some) n
  have : Primrec₂ F := .to₂ <| Primrec.nat_rec' Primrec.snd (.const Option.none)
      (Primrec.option_casesOn (Primrec.snd.comp .snd)
        (Code.primrec_evaln.comp <| _root_.Primrec.pair (_root_.Primrec.pair (snd.comp .fst) (.const cf)) (Primrec₂.natPair.comp (fst.comp fst) (fst.comp snd)))
        (Primrec.option_some.comp snd).to₂).to₂
  have hF : ∀ {m n a}, a ∈ F m n ↔ ∃ x < n, a ∈ cf.evaln n (m.pair x) := by
    suffices ∀ m n s a : ℕ,
      Nat.rec Option.none (fun x ih ↦ ih.casesOn (cf.evaln s (m.pair x)) Option.some) n = Option.some a ↔
      ∃ x < n, cf.evaln s (m.pair x) = .some a from fun m n a ↦ this m n n a
    intro m n s a
    induction n generalizing a
    case zero => simp
    case succ n ih =>
      cases hC : @Nat.rec (fun _ ↦ Option ℕ) Option.none (fun x ih ↦ ih.rec (cf.evaln s (m.pair x)) Option.some) n
      · suffices
          Code.evaln s cf (Nat.pair m n) = Option.some a
          ↔ ∃ x < n + 1, Code.evaln s cf (Nat.pair m x) = Option.some a by simpa [hC]
        constructor
        · intro h; exact ⟨n, by simp, h⟩
        · rintro ⟨x, hx, Hx⟩
          rcases eq_or_lt_of_le (le_of_lt_succ hx) with (rfl | hx)
          · exact Hx
          · exfalso; simpa using ((ih _).mpr ⟨x, hx, Hx⟩).symm.trans hC
      case some i =>
        suffices i = a ↔ ∃ x < n + 1, Code.evaln s cf (Nat.pair m x) = Option.some a by simpa [hC]
        constructor
        · rintro rfl;
          rcases (ih _).mp hC with ⟨x, hx, Hx⟩
          exact ⟨x, lt_trans hx (by simp), Hx⟩
        · rintro ⟨x, _, Hx⟩
          rcases (ih _).mp hC with ⟨y, _, Hy⟩
          exact unif (Nat.Partrec.Code.evaln_sound Hy) (Nat.Partrec.Code.evaln_sound Hx)
  have mono : ∀ {a m n₁ n₂ : ℕ}, n₁ ≤ n₂ → a ∈ F m n₁ → a ∈ F m n₂ := by
    intro a m n₁ n₂ hn h₁
    rcases hF.mp h₁ with ⟨x, hx, H⟩
    apply hF.mpr ⟨x, lt_of_lt_of_le hx hn, Code.evaln_mono hn H⟩
  have : Partrec (fun m ↦ rfindOpt (F m)) := Partrec.nat_iff.1 <| Partrec.rfindOpt <| this.to_comp
  exact ⟨_, this, by
    intro a m
    rw [Nat.rfindOpt_mono mono]
    constructor
    · rintro ⟨n, H⟩
      obtain ⟨x, _, H⟩ := hF.mp H
      exact ⟨x, Code.evaln_sound H⟩
    · rintro ⟨x, H⟩
      obtain ⟨s, Hs⟩ := Code.evaln_complete.mp H
      exact ⟨max s x + 1, (@hF m (max s x + 1) a).mpr
        ⟨x, by simp [Nat.lt_succ_iff],
          Code.evaln_mono (le_trans (Nat.le_max_left s x) (le_add_right (max s x) 1)) Hs⟩⟩⟩

end Nat.Partrec

namespace Partrec

variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

lemma projection {f : α → β →. γ} (hf : Partrec₂ f) (unif : ∀ {a b₁ b₂ c₁ c₂}, c₁ ∈ f a b₁ → c₂ ∈ f a b₂ → c₁ = c₂) :
    ∃ g : α →. γ, Partrec g ∧ (∀ c a, c ∈ g a ↔ ∃ b, c ∈ f a b) := by
  have := Nat.Partrec.projection (Partrec.bind_decode₂_iff.mp hf)
    (by intro m n₁ n₂ c₁ c₂; simp only [Part.mem_bind_iff, Part.mem_ofOption,
          Option.mem_def, Encodable.decode₂_eq_some, Part.mem_map_iff, Prod.exists, Encodable.encode_prod_val,
          Nat.pair_eq_pair, forall_exists_index, and_imp]
        rintro a b₁ rfl rfl c₁ h₁ rfl a b₂ e rfl c₂ h₂ rfl
        rcases Encodable.encode_inj.mp e
        rw [unif h₁ h₂])
  rcases this with ⟨g, hg, H⟩
  let g' : α →. γ := fun a ↦ (g (Encodable.encode a)).bind fun n ↦ Encodable.decode (α := γ) n
  refine ⟨g', ((nat_iff.2 hg).comp Computable.encode).bind (Computable.decode.ofOption.comp Computable.snd).to₂, ?_⟩
  have H : ∀ {c a : ℕ}, c ∈ g a ↔ ∃ a' b, Encodable.encode a' = a ∧ ∃ c' ∈ f a' b, Encodable.encode c' = c := by
    have H : ∀ (a m : ℕ),
      a ∈ g m ↔ ∃ z a' b, (Encodable.encode a' = m ∧ Encodable.encode b = z) ∧ ∃ a'' ∈ f a' b, Encodable.encode a'' = a := by
      simpa [Encodable.decode₂_eq_some] using H
    intro c a; constructor
    · intro h; rcases (H c a).mp h with ⟨b, a, b, ⟨rfl, rfl⟩, ⟨c, H, rfl⟩⟩
      exact ⟨a, b, rfl, c, H, rfl⟩
    · rintro ⟨a, b, rfl, c, hc, rfl⟩
      exact (H _ _).mpr ⟨Encodable.encode b, a, b, ⟨rfl, rfl⟩, c, hc, rfl⟩
  intro c a
  suffices (∃ c' ∈ g (Encodable.encode a), Encodable.decode c' = some c) ↔ ∃ b, c ∈ f a b by simpa [g']
  constructor
  · rintro ⟨c', h, hc⟩
    rcases H.mp h with ⟨a, b, ae, c, habc, rfl⟩;
    rcases by simpa using hc
    rcases Encodable.encode_inj.mp ae
    exact ⟨b, habc⟩
  · rintro ⟨b, habc⟩
    exact ⟨Encodable.encode c, H.mpr ⟨a, b, rfl, c, habc, rfl⟩, by simp⟩

end Partrec

namespace REPred

variable {α β : Type*} [Primcodable α] [Primcodable β] {p q : α → Prop}

@[simp] protected lemma const (p : Prop) : REPred fun _ : α ↦ p := by
  by_cases h : p
  · simpa [h] using Partrec.some.dom_re
  · simpa [h] using (Partrec.none (α := α) (σ := α)).dom_re

lemma iff : REPred p ↔ ∃ f : α →. Unit, Partrec f ∧ p = fun x ↦ (f x).Dom :=
  ⟨fun h ↦ ⟨_, h, by ext x; simp [Part.assert]⟩, by rintro ⟨f, hf, rfl⟩; exact hf.dom_re⟩

lemma iff' : REPred p ↔ ∃ f : α →. Unit, Partrec f ∧ ∀ x, p x ↔ (f x).Dom :=
  ⟨fun h ↦ ⟨_, h, by intro x; simp [Part.assert]⟩, by rintro ⟨f, hf, H⟩; exact hf.dom_re.of_eq (by simp [H])⟩

lemma and (hp : REPred p) (hq : REPred q) : REPred fun x ↦ p x ∧ q x := by
  rcases REPred.iff.mp hp with ⟨f, hf, rfl⟩
  rcases REPred.iff.mp hq with ⟨g, hg, rfl⟩
  let h : α →. Unit := fun x ↦ (f x).bind fun _ ↦ (g x).map fun _ ↦ ()
  have : Partrec h := Partrec.bind hf <| Partrec.to₂ <| Partrec.map (hg.comp Computable.fst) (Computable.const ()).to₂
  exact REPred.iff.mpr ⟨_, this, by funext x; simp [h]⟩

lemma or (hp : REPred p) (hq : REPred q) : REPred fun x ↦ p x ∨ q x := by
  rcases REPred.iff.mp hp with ⟨f, hf, rfl⟩
  rcases REPred.iff.mp hq with ⟨g, hg, rfl⟩
  rcases hf.merge hg (by intro a x; simp) with ⟨k, hk, h⟩
  exact REPred.iff.mpr ⟨k, hk, by funext x; simp [Part.unit_dom_iff, h]⟩

lemma projection {p : α × β → Prop} (hp : REPred p) : REPred fun x ↦ ∃ y, p (x, y) := by
  rcases REPred.iff.mp hp with ⟨f, hf, rfl⟩
  have : Partrec₂ fun a b ↦ f (a, b) := hf.comp <| Computable.pair .fst .snd
  obtain ⟨g, hg, Hg⟩ := Partrec.projection this (by simp)
  exact REPred.iff.mpr ⟨g, hg, by funext x; simp [Part.unit_dom_iff, Hg]⟩

protected lemma comp {f : α → β} (hf : Computable f) {p : β → Prop} (hp : REPred p) : REPred fun x ↦ p (f x) := by
  rcases REPred.iff.mp hp with ⟨p, pp, rfl⟩
  exact REPred.iff'.mpr ⟨_, pp.comp hf, by intro x; simp⟩

end REPred

namespace ComputablePred

variable {α β : Type*} [Primcodable α] [Primcodable β] {p q : α → Prop}

@[simp] protected lemma const (p : Prop) : ComputablePred fun _ : α ↦ p :=
  computable_iff_re_compl_re'.mpr ⟨REPred.const _, REPred.const _⟩

lemma and : ComputablePred p → ComputablePred q → ComputablePred fun x ↦ p x ∧ q x := by
  simp_rw [computable_iff_re_compl_re']
  rintro ⟨hp, hnp⟩
  rintro ⟨hq, hnq⟩
  refine ⟨hp.and hq, (hnp.or hnq).of_eq <| by grind⟩

lemma or : ComputablePred p → ComputablePred q → ComputablePred fun x ↦ p x ∨ q x := by
  simp_rw [computable_iff_re_compl_re']
  rintro ⟨hp, hnp⟩
  rintro ⟨hq, hnq⟩
  refine ⟨hp.or hq, (hnp.and hnq).of_eq <| by grind⟩

end ComputablePred
