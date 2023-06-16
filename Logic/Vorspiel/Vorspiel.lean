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
import Mathlib.Order.Filter.Ultrafilter

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

#check 0 :> ![1, 2]

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

lemma to_vecCons (s : Fin (n + 1) → C) : s = s 0 :> s ∘ Fin.succ :=
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
  | 0,     _, _, _ => by simp; exact isTrue trivial
  | n + 1, v, w, d => by
      rw[to_vecCons v, to_vecCons w, vecCons_ext]
      haveI : Decidable (v ∘ Fin.succ = w ∘ Fin.succ) := decVec _ _ (by intros i; simp; exact d _)
      refine instDecidableAnd

lemma comp_vecCons (f : α → β) (a : α) (s : Fin n → α) : (fun x => f $ (a :> s) x) = f a :> f ∘ s :=
funext (fun i => cases (by simp) (by simp) i)

lemma comp_vecCons' (f : α → β) (a : α) (s : Fin n → α) : (fun x => f $ (a :> s) x) = f a :> fun i => f (s i) :=
  comp_vecCons f a s

lemma comp_vecCons'' (f : α → β) (a : α) (s : Fin n → α) : f ∘ (a :> s) = f a :> f ∘ s :=
  comp_vecCons f a s

@[simp] lemma comp₀ : f ∘ (![] : Fin 0 → α) = ![] := by simp

@[simp] lemma comp₁ (a : α) : f ∘ ![a] = ![f a] := by simp[comp_vecCons'']

@[simp] lemma comp₂ (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] := by simp[comp_vecCons'']

@[simp] lemma comp₃ (a₁ a₂ a₃ : α) : f ∘ ![a₁, a₂, a₃] = ![f a₁, f a₂, f a₃] := by simp[comp_vecCons'']

lemma comp_vecConsLast (f : α → β) (a : α) (s : Fin n → α) : (fun x => f $ (s <: a) x) = f ∘ s <: f a :=
funext (fun i => lastCases (by simp) (by simp) i)

@[simp] lemma vecHead_comp (f : α → β) (v : Fin (n + 1) → α) : vecHead (f ∘ v) = f (vecHead v) :=
  by simp[vecHead]

@[simp] lemma vecTail_comp (f : α → β) (v : Fin (n + 1) → α) : vecTail (f ∘ v) = f ∘ (vecTail v) :=
  by simp[vecTail, Function.comp.assoc]

lemma vecConsLast_vecEmpty {s : Fin 0 → α} (a : α) : s <: a = ![a] :=
  funext (fun x => by
    have : 0 = Fin.last 0 := by rfl
    cases' x using Fin.cases with i <;> simp[this]
    have := i.isLt; contradiction )

lemma constant_eq_singleton {a : α} : (fun _ => a) = ![a] := by funext x; simp

lemma injective_vecCons {f : Fin n → α} (h : Function.Injective f) {a} (ha : ∀ i, a ≠ f i) : Function.Injective (a :> f) := by
  have : ∀ i, f i ≠ a := fun i => (ha i).symm
  intro i j; cases i using Fin.cases <;> cases j using Fin.cases <;> simp[*]
  intro hf; exact h hf

section And

variable [HasLogicSymbols α] [HasLogicSymbols β]

def conj : {n : ℕ} → (Fin n → α) → α
  | 0,     _ => ⊤
  | _ + 1, v => v 0 ⋏ conj (vecTail v)

@[simp] lemma conj_nil (v : Fin 0 → α) : conj v = ⊤ := rfl

@[simp] lemma conj_cons {a : α} {v : Fin n → α} : conj (a :> v) = a ⋏ conj v := rfl

@[simp] lemma conj_hom_prop (f : α →L Prop) (v : Fin n → α) : f (conj v) = ∀ i, f (v i) := by
  induction' n with n ih <;> simp[conj]
  · intro ⟨_, _⟩; contradiction
  · simp[ih]; constructor
    · intro ⟨hz, hs⟩ i; cases i using Fin.cases; { exact hz }; { exact hs _ }
    · intro h; exact ⟨h 0, fun i => h _⟩

lemma hom_conj (f : α →L β) (v : Fin n → α) : f (conj v) = conj (f ∘ v) := by
  induction' n with n ih <;> simp[*, conj]

lemma hom_conj' (f : α →L β) (v : Fin n → α) : f (conj v) = conj fun i => f (v i) := hom_conj f v

end And

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

@[simp] lemma mem_toList_iff {v : Fin n → α} {a} : a ∈ toList v ↔ ∃ i, v i = a :=
  by induction n <;> simp[*]; constructor; { rintro (rfl | ⟨i, rfl⟩) <;> simp }; { rintro ⟨i, rfl⟩; cases i using Fin.cases <;> simp }

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

namespace Empty

lemma eq_elim {α : Sort u} (f : Empty → α) : f = elim := funext (by rintro ⟨⟩)

end Empty

namespace IsEmpty
variable {o : Sort u} (h : IsEmpty o)

lemma eq_elim {α : Sort u} (f : o → α) : f = h.elim' := funext h.elim

end IsEmpty

namespace Set
variable  {α : Type u} {β : Type v}

lemma subset_image_iff (f : α → β) {s : Set α} {t : Set β} :
    t ⊆ f '' s ↔ ∃ u, u ⊆ s ∧ f '' u = t :=
  ⟨by intro h
      use {a : α | a ∈ s ∧ f a ∈ t}
      constructor
      { intros a ha; exact ha.1 }
      { ext b; constructor <;> simp; { rintro a _ hfa rfl; exact hfa };
        { intros hb; rcases h hb with ⟨a, ha, rfl⟩; exact ⟨a, ⟨ha, hb⟩, rfl⟩ } },
   by { rintro ⟨u, hu, rfl⟩; intros b; simp; rintro a ha rfl; exact ⟨a, hu ha, rfl⟩ }⟩

end Set

namespace Function

variable  {α : Type u} {β : Type v}

def funEqOn (p : α → Prop) (f g : α → β) : Prop := ∀ a, p a → f a = g a

lemma funEqOn.of_subset {p q : α → Prop} {f g : α → β} (e : funEqOn p f g) (h : ∀ a, q a → p a) : funEqOn q f g :=
  by intro a ha; exact e a (h a ha)

end Function

namespace Quotient
open Matrix
variable {α : Type u} [s : Setoid α] {β : Sort v}

@[elab_as_elim]
lemma inductionOnVec {p : (Fin n → Quotient s) → Prop} (v : Fin n → Quotient s)
  (h : ∀ v : Fin n → α, p (fun i => Quotient.mk s (v i))) : p v :=
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
    simp[this])

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

def upper : List ℕ → ℕ
  | []      => 0
  | n :: ns => max (n + 1) ns.upper

@[simp] lemma upper_nil : upper [] = 0 := rfl

@[simp] lemma upper_cons (n : ℕ) (ns : List ℕ) : upper (n :: ns) = max (n + 1) ns.upper := rfl

lemma lt_upper (l : List ℕ) {n} (h : n ∈ l) : n < l.upper := by
  induction' l with n ns ih <;> simp at h ⊢
  case cons =>
    rcases h with (rfl | h) <;> simp
    exact Or.inr (ih h)

variable {α : Type u} [DecidableEq α] {β: Type v} [DecidableEq β]

lemma toFinset_map {f : α → β} (l : List α) : (l.map f).toFinset = Finset.image f l.toFinset := by
  induction l <;> simp[*]

section

variable {α : Type u} [HasLogicSymbols α]

def conj : List α → α
  | []      => ⊤
  | a :: as => a ⋏ as.conj

@[simp] lemma conj_nil : conj (α := α) [] = ⊤ := rfl

@[simp] lemma conj_cons {a : α} {as : List α} : conj (a :: as) = a ⋏ as.conj := rfl

lemma map_conj (f : α →L Prop) (l : List α) : f l.conj ↔ ∀ a ∈ l, f a := by
  induction l <;> simp[*]

def disj : List α → α
  | []      => ⊥
  | a :: as => a ⋎ as.disj

@[simp] lemma disj_nil : disj (α := α) [] = ⊥ := rfl

@[simp] lemma disj_cons {a : α} {as : List α} : disj (a :: as) = a ⋎ as.disj := rfl

lemma map_disj (f : α →L Prop) (l : List α) : f l.disj ↔ ∃ a ∈ l, f a := by
  induction l <;> simp[*]

end

variable {α : Type u} [inst : SemilatticeSup α] [inst : OrderBot α]

def sup : List α → α
  | [] => ⊥
  | a :: as => a ⊔ as.sup

@[simp] lemma sup_nil : ([] : List α).sup = ⊥ := rfl

@[simp] lemma sup_cons (a : α) (as : List α) : (a :: as).sup = a ⊔ as.sup := rfl

lemma le_sup {a} {l : List α} : a ∈ l → a ≤ l.sup :=
  by induction' l with a l ih <;> simp[*]; rintro (rfl | h) <;> simp[*]; exact le_sup_of_le_right $ ih h

end List

namespace Finset

variable {α : Type u} {β : Type v} {γ : Type w}

noncomputable def rangeOfFinite {ι : Sort v} [Finite ι] (f : ι → α) : Finset α :=
  Set.Finite.toFinset (s := Set.range f) (Set.toFinite (Set.range f))

lemma mem_rangeOfFinite_iff  {ι : Sort v} [Finite ι] {f : ι → α} {a : α} :
    a ∈ rangeOfFinite f ↔ ∃ i : ι, f i = a := by simp[rangeOfFinite]

noncomputable def imageOfFinset [DecidableEq β] (s : Finset α) (f : (a : α) → a ∈ s → β) : Finset β :=
  Finset.bunionᵢ s (rangeOfFinite $ f ·)

lemma mem_imageOfFinset_iff [DecidableEq β] {s : Finset α} {f : (a : α) → a ∈ s → β} {b : β} :
    b ∈ imageOfFinset s f ↔ ∃ (a : α) (ha : a ∈ s), f a ha = b := by
  simp[imageOfFinset, mem_rangeOfFinite_iff]
  constructor
  · rintro ⟨a, _, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, ha, rfl⟩

@[simp] lemma mem_imageOfFinset  [DecidableEq β] {s : Finset α} (f : (a : α) → a ∈ s → β) (a : α) (ha : a ∈ s) :
    f a ha ∈ imageOfFinset s f := by simp[mem_imageOfFinset_iff]; exact ⟨a, ha, rfl⟩

-- lemma ext_image {f : β → α} {g : γ → α} {s : Finset β} {t : Finset γ} : f s = g t ↔ ∀ 

section

variable [HasLogicSymbols α]

noncomputable def conj (s : Finset α) : α := s.toList.conj

lemma map_conj (f : α →L Prop) (s : Finset α) : f s.conj ↔ ∀ a ∈ s, f a := by
  simpa using List.map_conj f s.toList
  
noncomputable def disj (s : Finset α) : α := s.toList.disj

lemma map_disj (f : α →L Prop) (s : Finset α) : f s.disj ↔ ∃ a ∈ s, f a := by
  simpa using List.map_disj f s.toList

end

lemma erase_union [DecidableEq α] {a : α} {s t : Finset α} :
  (s ∪ t).erase a = (s.erase a) ∪ (t.erase a) := by ext; simp[and_or_left]

end Finset