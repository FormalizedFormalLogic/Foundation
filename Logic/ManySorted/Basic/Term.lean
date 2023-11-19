import Logic.FirstOrder.Basic
import Logic.ManySorted.Basic.Language

attribute [-instance] WType.instEncodableWType Encodable.finPi Encodable.fintypeArrowOfEncodable

section
variable {S : Type w} [DecidableEq S]

def idxMap (s : S) {α : S → Type*} (f : α s → α s) : (s : S) → α s → α s := fun s' =>
  if h : s = s' then h ▸ f else id

namespace Nat

def indexedMod (s : S) (m : ℕ) (n : S → ℕ) : S → ℕ := fun s' => if s = s' then m else n s'

def indexedSucc (s : S) (n : S → ℕ) : S → ℕ := fun s' => if s = s' then n s' + 1 else n s'

@[simp] lemma indexedSucc_app_eq {s : S} {n : S → ℕ} : indexedSucc s n s = n s + 1 := by simp[indexedSucc]

@[simp] lemma indexedSucc_app_ne {s s' : S} (h : s ≠ s') {n : S → ℕ} : indexedSucc s n s' = n s' := by simp[indexedSucc, h]

def condSucc (s s' : S) : ℕ → ℕ := fun i => if s = s' then i + 1 else i

def indexedVecCons {β : S → Type*} (s : S) (b : β s) (f : (s' : S) → ℕ → β s') (s' : S) :
    ℕ → β s' := if h : s = s' then h ▸ b :>ₙ f s' else f s'

end Nat

namespace Fin

def condSucc (s : S) {n : S → ℕ} (s') : Fin (n s') → Fin (Nat.indexedSucc s n s') :=
  fun i => if h : s = s' then i.succ.cast (by simp[h]) else i.cast (by simp[h])

end Fin

namespace Matrix

def indexedVecCons {β : S → Type*} {n : S → ℕ} (s : S) (b : β s) (f : (s' : S) → Fin (n s') → β s') (s' : S) :
    Fin (Nat.indexedSucc s n s') → β s' :=
  if h : s = s' then fun i => (h ▸ b :> f s') (i.cast $ by simp[h]) else fun i => f s' (i.cast $ by simp[h])

def indexedVecConsLast {β : S → Type*} {n : S → ℕ} (s : S) (b : β s) (f : (s' : S) → Fin (n s') → β s') (s' : S) :
    Fin (Nat.indexedSucc s n s') → β s' :=
  if h : s = s' then fun i => (f s' <: h ▸ b) (i.cast $ by simp[h]) else fun i => f s' (i.cast $ by simp[h])

end Matrix

end

namespace LO

namespace ManySorted

inductive Subterm {S : Type w} : (s : S) → (L : Language.{w, u} S) → (μ : S → Type v) → (S → ℕ) → Type _
  | bvar {n} (sort : S) : Fin (n sort) → Subterm sort L μ n
  | fvar {n} (sort : S) : μ sort → Subterm sort L μ n
  | func {n} {sort : S} {arity : S → ℕ} :
    L.Func sort arity → ((s : S) → Fin (arity s) → Subterm s L μ n) → Subterm sort L μ n

scoped notation:max "#" x "∷" s:max => Subterm.bvar s x
scoped notation:max "&" x "∷" s:max => Subterm.fvar s x
scoped prefix:max "#"  => Subterm.bvar _
scoped prefix:max "&"  => Subterm.fvar _

abbrev Term {S : Type w} (s : S) (L : Language.{w, u} S) (μ : S → Type v) := Subterm s L μ 0

abbrev SyntacticSubterm {S : Type w} (s : S) (L : Language.{w, u} S) (n : ℕ) := Subterm s L (fun _ => ℕ) n

abbrev SyntacticTerm {S : Type w} (s : S) (L : Language.{w, u} S) := Subterm s L (fun _ => ℕ) 0

namespace Subterm

variable {S : Type w} {L : Language.{w, u} S} {μ : S → Type v}

def cast {n n' : S → ℕ} (t : Subterm s L μ n) (h : n = n')  : Subterm s L μ n' := h ▸ t

section Decidable

variable
  [(sort : S) → (arity : S → ℕ) → DecidableEq (L.Func sort arity)]
  [Fintype S] [DecidableEq S] [(s : S) → DecidableEq (μ s)]

def hasDecEq : (s : S) → (t u : Subterm s L μ n) → Decidable (t = u)
  | _, #x∷_,                     #y∷_                     => by simp; exact decEq x y
  | _, #x∷_,                     &y∷_                     => isFalse Subterm.noConfusion
  | _, #x∷_,                     func f v                 => isFalse Subterm.noConfusion
  | _, &x∷_,                     #y∷_                     => isFalse Subterm.noConfusion
  | _, &x∷_,                     &y∷_                     => by simp; exact decEq x y
  | _, &x∷_,                     func f v                 => isFalse Subterm.noConfusion
  | _, func f v,                 #y∷_                     => isFalse Subterm.noConfusion
  | _, func f v,                 &y∷_                     => isFalse Subterm.noConfusion
  | s, @func _ _ _ _ _ a₁ f₁ v₁, @func _ _ _ _ _ a₂ f₂ v₂ => by
      by_cases ea : a₁ = a₂
      · rcases ea with rfl
        by_cases ef : f₁ = f₂
        · rcases ef with rfl
          simp
          exact Fintype.decideEqPi v₁ v₂
            (fun s => DMatrix.decVec _ _ (fun i => hasDecEq s (v₁ s i) (v₂ s i)))
        · exact isFalse (by simp[ef])
      · exact isFalse (by simp[ea])

instance (s : S) : DecidableEq (Subterm s L μ n) := hasDecEq s

end Decidable

end Subterm

structure Rew {S : Type w} (L : Language.{w,u} S) (μ₁ : S → Type ν₁) (n₁ : S → ℕ) (μ₂ : S → Type ν₂) (n₂ : S → ℕ) where
  toFun : (s : S) → Subterm s L μ₁ n₁ → Subterm s L μ₂ n₂
  func' : ∀ {s : S} {arity : S → ℕ} (f : L.Func s arity) (v : (s : S) → Fin (arity s) → Subterm s L μ₁ n₁),
    toFun s (Subterm.func f v) = Subterm.func f (fun s i => toFun s (v s i))

abbrev SyntacticRew (L : Language.{w, u} S) (n₁ n₂ : S → ℕ) := Rew L (fun _ => ℕ) n₁ (fun _ => ℕ) n₂

namespace Rew

open Subterm
variable {S : Type w} [DecidableEq S] {L : Language.{w, u} S}
{μ : S → Type v} {μ₁ : S → Type v₁} {μ₂ : S → Type v₂}
{n n₁ n₂ : S → ℕ}

def trm (ω : Rew L μ₁ n₁ μ₂ n₂) {s : S} : Subterm s L μ₁ n₁ → Subterm s L μ₂ n₂ := ω.toFun s

section
variable {ω : Rew L μ₁ n₁ μ₂ n₂}

protected lemma func {s} {k : S → ℕ} (f : L.Func s k) (v : (s : S) → (i : Fin (k s)) → Subterm s L μ₁ n₁) :
    ω.trm (func f v) = func f (fun s i => ω.trm (v s i)) := ω.func' f v

lemma ext' {ω₁ ω₂ : Rew L μ₁ n₁ μ₂ n₂} (h : ∀ s, ∀ t : Subterm s L μ₁ n₁, ω₁.trm t = ω₂.trm t) : ω₁ = ω₂ := by
  rcases ω₁; rcases ω₂; simp
  funext s t; simpa using h s t

end

@[ext] lemma ext (ω₁ ω₂ : Rew L μ₁ n₁ μ₂ n₂)
  (hb : ∀ s x, ω₁.trm #x∷s = ω₂.trm #x∷s)
  (hf : ∀ s x, ω₁.trm &x∷s = ω₂.trm &x∷s) : ω₁ = ω₂ := by
  apply ext'; intro s t
  induction t <;> simp[*, Rew.func]
  case func v ih => funext s i; exact ih s i ω₁ ω₂ hb hf

protected def id : Rew L μ n μ n where
  toFun := fun _ => id
  func' := fun _ _ => rfl

@[simp] lemma id_app (t : Subterm s L μ n) : Rew.id.trm t = t := rfl

protected def comp (ω₂ : Rew L μ₂ n₂ μ₃ n₃) (ω₁ : Rew L μ₁ n₁ μ₂ n₂) : Rew L μ₁ n₁ μ₃ n₃ where
  toFun := fun _ t => ω₂.trm (ω₁.trm t)
  func' := fun f v => by simp[Rew.func]

infixr:70 " ⊚ " => Rew.comp

lemma comp_app (ω₂ : Rew L μ₂ n₂ μ₃ n₃) (ω₁ : Rew L μ₁ n₁ μ₂ n₂) {s} (t : Subterm s L μ₁ n₁) :
    (ω₂ ⊚ ω₁).trm t = ω₂.trm (ω₁.trm t) := rfl

lemma comp_assoc (ω₃ : Rew L μ₃ n₃ μ₄ n₄) (ω₂ : Rew L μ₂ n₂ μ₃ n₃) (ω₁ : Rew L μ₁ n₁ μ₂ n₂) :
    ω₃ ⊚ (ω₂ ⊚ ω₁) = (ω₃ ⊚ ω₂) ⊚ ω₁ := ext' (by intro s t; simp[comp_app])

@[simp] lemma id_comp (ω : Rew L μ₁ n₁ μ₂ n₂) : Rew.id ⊚ ω = ω := by ext <;> simp[comp_app]

@[simp] lemma comp_id (ω : Rew L μ₁ n₁ μ₂ n₂) : ω ⊚ Rew.id = ω := by ext <;> simp[comp_app]

def bindAux (b : (s : S) → Fin (n₁ s) → Subterm s L μ₂ n₂) (e : (s : S) → μ₁ s → Subterm s L μ₂ n₂) :
    (s : S) → Subterm s L μ₁ n₁ → Subterm s L μ₂ n₂
  | _, #x∷s     => b s x
  | _, &x∷s     => e s x
  | _, func f v => func f (fun s i => bindAux b e s (v s i))

def bind
    (b : (s : S) → Fin (n₁ s) → Subterm s L μ₂ n₂)
    (e : (s : S) → μ₁ s → Subterm s L μ₂ n₂) : Rew L μ₁ n₁ μ₂ n₂ where
  toFun := bindAux b e
  func' := fun _ _ => rfl

def map (b : (s : S) → Fin (n₁ s) → Fin (n₂ s)) (e : (s : S) → μ₁ s → μ₂ s) : Rew L μ₁ n₁ μ₂ n₂ :=
  bind (fun s x => #(b s x)) (fun s x => &(e s x))

def bShift (s : S) : Rew L μ n μ (Nat.indexedSucc s n) :=
  map (Fin.condSucc s) (fun _ => id)

lemma eq_id_of_eq {ω : Rew L μ n μ n} (hb : ∀ s x, ω.trm #x∷s = #x∷s) (he : ∀ s x, ω.trm &x∷s = &x∷s)
    {s} (t : Subterm s L μ n) : ω.trm t = t := by
  have : ω = Rew.id := by ext <;> simp[*]
  simp[this]

protected def q (s : S) (ω : Rew L μ₁ n₁ μ₂ n₂) : Rew L μ₁ (Nat.indexedSucc s n₁) μ₂ (Nat.indexedSucc s n₂) :=
  bind
    (Matrix.indexedVecCons s #((0 : Fin (n₂ s + 1)).cast $ by simp)∷s (fun s' => (bShift s).trm ∘ ω.trm ∘ bvar s'))
    (fun s' => (bShift s).trm ∘ ω.trm ∘ fvar s')

def shift (s : S) : SyntacticRew L n n := map (fun _ => id) (idxMap s Nat.succ)

def free (s : S) : SyntacticRew L (Nat.indexedSucc s n) n :=
  bind
    (Matrix.indexedVecConsLast s &0∷s bvar)
    (fun s' x => &(Nat.condSucc s s' x)∷s')

def fix (s : S) : SyntacticRew L n (Nat.indexedSucc s n) :=
  bind
    (fun s' x => #(Fin.condSucc s s' x))
    (Nat.indexedVecCons s #((0 : Fin (n s + 1)).cast $ by simp)∷s fvar)

end Rew

end ManySorted

end LO
