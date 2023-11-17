import Logic.Predicate.FirstOrder.Basic
import Logic.Predicate.ManySorted.Basic.Language

attribute [-instance] WType.instEncodableWType Encodable.finPi Encodable.fintypeArrowOfEncodable

namespace LO

namespace ManySorted

inductive Subterm {S : Type w} : (s : S) → (L : Language.{w, u} S) → (μ : S → Type v) → ℕ → Type _
  | bvar {n} (sort : S) : Fin n → Subterm sort L μ n
  | fvar {n} (sort : S) : μ sort → Subterm sort L μ n
  | func {n} {sort : S} {arity} {aug : Fin arity → S} :
    L.Func sort aug → ((i : Fin arity) → Subterm (aug i) L μ n) → Subterm sort L μ n

scoped notation:max "#" x "∷" s:max => Subterm.bvar s x
scoped notation:max "&" x "∷" s:max => Subterm.fvar s x
scoped prefix:max "#"  => Subterm.bvar _
scoped prefix:max "&"  => Subterm.fvar _

abbrev Term {S : Type w} (s : S) (L : Language.{w, u} S) (μ : S → Type v) := Subterm s L μ 0

abbrev SyntacticSubterm {S : Type w} (s : S) (L : Language.{w, u} S) (n : ℕ) := Subterm s L (fun _ => ℕ) n

abbrev SyntacticTerm {S : Type w} (s : S) (L : Language.{w, u} S) := Subterm s L (fun _ => ℕ) 0

namespace Subterm

variable {S : Type w} {L : Language.{w, u} S} {μ : S → Type v}

section Decidable

variable
  [(sort : S) → (k : ℕ) → (aug : Fin k → S) → DecidableEq (L.Func sort aug)]
  [DecidableEq S] [(s : S) → DecidableEq (μ s)]

def hasDecEq : (s : S) → (t u : Subterm s L μ n) → Decidable (t = u)
  | _, #x∷_,                        #y∷_                        => by simp; exact decEq x y
  | _, #x∷_,                        &y∷_                        => isFalse Subterm.noConfusion
  | _, #x∷_,                        func f v                    => isFalse Subterm.noConfusion
  | _, &x∷_,                        #y∷_                        => isFalse Subterm.noConfusion
  | _, &x∷_,                        &y∷_                        => by simp; exact decEq x y
  | _, &x∷_,                        func f v                    => isFalse Subterm.noConfusion
  | _, func f v,                    #y∷_                        => isFalse Subterm.noConfusion
  | _, func f v,                    &y∷_                        => isFalse Subterm.noConfusion
  | s, @func _ _ _ _ _ k₁ a₁ f₁ v₁, @func _ _ _ _ _ k₂ a₂ f₂ v₂ => by
    by_cases e : k₁ = k₂
    · rcases e with rfl
      by_cases ea : a₁ = a₂
      · rcases ea with rfl
        by_cases ef : f₁ = f₂
        · rcases ef with rfl
          simp; exact DMatrix.decVec _ _ (fun i => hasDecEq (a₁ i) (v₁ i) (v₂ i))
        · exact isFalse (by simp[ef])
      · exact isFalse (by simp[ea])
    · exact isFalse (by simp[e])

instance (s : S) : DecidableEq (Subterm s L μ n) := hasDecEq s

end Decidable

end Subterm

structure Rew {S : Type w} (L : Language.{w,u} S) (μ₁ : S → Type ν₁) (n₁ : ℕ) (μ₂ : S → Type ν₂) (n₂ : ℕ) where
  toFun : (s : S) → Subterm s L μ₁ n₁ → Subterm s L μ₂ n₂
  func' : ∀ {s : S} {k : ℕ} {a : Fin k → S} (f : L.Func s a) (v : (i : Fin k) → Subterm (a i) L μ₁ n₁),
    toFun s (Subterm.func f v) = Subterm.func f (fun i => toFun (a i) (v i))

abbrev SyntacticRew (L : Language.{w, u} S) (n₁ n₂ : ℕ) := Rew L (fun _ => ℕ) n₁ (fun _ => ℕ) n₂

namespace Rew

open Subterm
variable {S : Type w} {L : Language.{w, u} S} {μ : S → Type v} {μ₁ : S → Type v₁} {μ₂ : S → Type v₂}

def trm (ω : Rew L μ₁ n₁ μ₂ n₂) {s : S} : Subterm s L μ₁ n₁ → Subterm s L μ₂ n₂ := ω.toFun s

section
variable {ω : Rew L μ₁ n₁ μ₂ n₂}

protected lemma func {s k} {a : Fin k → S} (f : L.Func s a) (v : (i : Fin k) → Subterm (a i) L μ₁ n₁) :
    ω.trm (func f v) = func f (fun i => ω.trm (v i)) := ω.func' f v

lemma ext' {ω₁ ω₂ : Rew L μ₁ n₁ μ₂ n₂} (h : ∀ s, ∀ t : Subterm s L μ₁ n₁, ω₁.trm t = ω₂.trm t) : ω₁ = ω₂ := by
  rcases ω₁; rcases ω₂; simp
  funext s t; simpa using h s t

end

@[ext] lemma ext (ω₁ ω₂ : Rew L μ₁ n₁ μ₂ n₂)
  (hb : ∀ s x, ω₁.trm #x∷s = ω₂.trm #x∷s)
  (hf : ∀ s x, ω₁.trm &x∷s = ω₂.trm &x∷s) : ω₁ = ω₂ := by
  apply ext'; intro s t
  induction t <;> simp[*, Rew.func]
  case func v ih => funext i; exact ih i ω₁ ω₂ hb hf

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

def bindAux (b : (s : S) → Fin n₁ → Subterm s L μ₂ n₂) (e : (s : S) → μ₁ s → Subterm s L μ₂ n₂) :
    (s : S) → Subterm s L μ₁ n₁ → Subterm s L μ₂ n₂
  | _, #x∷s     => b s x
  | _, &x∷s     => e s x
  | _, func f v => func f (fun i => bindAux b e _ (v i))

def bind
    (b : (s : S) → Fin n₁ → Subterm s L μ₂ n₂)
    (e : (s : S) → μ₁ s → Subterm s L μ₂ n₂) : Rew L μ₁ n₁ μ₂ n₂ where
  toFun := bindAux b e
  func' := fun _ _ => rfl

def map (b : S → Fin n₁ → Fin n₂) (e : (s : S) → μ₁ s → μ₂ s) : Rew L μ₁ n₁ μ₂ n₂ :=
  bind (fun s x => #(b s x)) (fun s x => &(e s x))

def bShift : Rew L μ n μ (n + 1) :=
  map (fun _ => Fin.succ) (fun _ => id)

protected def q (ω : Rew L μ₁ n₁ μ₂ n₂) : Rew L μ₁ (n₁ + 1) μ₂ (n₂ + 1) :=
  bind (fun s => #0∷s ::> (bShift.trm ∘ ω.trm ∘ bvar s)) (fun s => bShift.trm ∘ ω.trm ∘ fvar s)

lemma eq_id_of_eq {ω : Rew L μ n μ n} (hb : ∀ s x, ω.trm #x∷s = #x∷s) (he : ∀ s x, ω.trm &x∷s = &x∷s)
    {s} (t : Subterm s L μ n) : ω.trm t = t := by
  have : ω = Rew.id := by ext <;> simp[*]
  simp[this]

end Rew

end ManySorted

end LO
