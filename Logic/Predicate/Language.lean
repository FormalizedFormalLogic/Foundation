import Logic.Vorspiel.Vorspiel
import Mathlib.Data.Finset.Basic

structure Language where
  func : Nat → Type u
  rel  : Nat → Type u

namespace Language

protected def empty : Language.{u} where
  func := fun _ => PEmpty
  rel  := fun _ => PEmpty

instance : Inhabited Language := ⟨Language.empty⟩

inductive GraphFunc : ℕ → Type
  | start : GraphFunc 0
  | terminal : GraphFunc 0

inductive GraphRel : ℕ → Type
  | equal : GraphRel 2
  | le : GraphRel 2

def graph : Language where
  func := GraphFunc
  rel := GraphRel

inductive BinaryRel : ℕ → Type
  | isone : BinaryRel 1
  | equal : BinaryRel 2
  | le : BinaryRel 2

def binary : Language where
  func := fun _ => Empty
  rel := BinaryRel

inductive EqRel : ℕ → Type
  | equal : EqRel 2

@[reducible]
def equal : Language where
  func := fun _ => Empty
  rel := EqRel

instance (k) : ToString (equal.func k) := ⟨fun _ => ""⟩

instance (k) : ToString (equal.rel k) := ⟨fun _ => "\\mathrm{Eq}"⟩

instance (k) : DecidableEq (equal.func k) := fun a b => by rcases a

instance (k) : DecidableEq (equal.rel k) := fun a b => by rcases a; rcases b; exact isTrue (by simp)

instance (k) : Encodable (equal.func k) := Encodable.IsEmpty.toEncodable

instance (k) : Encodable (equal.rel k) where
  encode := fun _ => 0
  decode := fun _ => 
    match k with
    | 2 => some EqRel.equal
    | _ => none
  encodek := fun x => by rcases x; simp

inductive RingFunc : ℕ → Type
  | zero : RingFunc 0
  | one : RingFunc 0
  | add : RingFunc 2
  | mul : RingFunc 2

inductive RingRel : ℕ → Type
  | equal : RingRel 2
  | le : RingRel 2

@[reducible]
def ring : Language where
  func := RingFunc
  rel := RingRel

instance (k) : ToString (ring.func k) :=
⟨ fun s =>
  match s with
  | RingFunc.zero => "0"
  | RingFunc.one  => "1"
  | RingFunc.add  => "(+)"
  | RingFunc.mul  => "(\\cdot)"⟩

instance (k) : ToString (ring.rel k) :=
⟨ fun s =>
  match s with
  | RingRel.equal => "\\mathrm{Eq}"
  | RingRel.le    => "\\mathrm{Le}"⟩

instance (k) : DecidableEq (ring.func k) := fun a b =>
  by rcases a <;> rcases b <;> simp <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : DecidableEq (ring.rel k) := fun a b =>
  by rcases a <;> rcases b <;> simp <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : Encodable (ring.func k) where
  encode := fun x =>
    match x with
    | RingFunc.zero => 0
    | RingFunc.one  => 1
    | RingFunc.add  => 0
    | RingFunc.mul  => 1
  decode := fun e =>
    match k, e with
    | 0, 0 => some RingFunc.zero
    | 0, 1 => some RingFunc.one
    | 2, 0 => some RingFunc.add
    | 2, 1 => some RingFunc.mul
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

instance (k) : Encodable (ring.rel k) where
  encode := fun x =>
    match x with
    | RingRel.equal => 0
    | RingRel.le    => 1
  decode := fun e =>
    match k, e with
    | 2, 0 => some RingRel.equal
    | 2, 1 => some RingRel.le
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

@[reducible]
def relational (α : ℕ → Type u) : Language where
  func := fun _ => PEmpty
  rel := α

section relational
variable {α : ℕ → Type u} [e : ∀ n, Encodable (α n)] [d : ∀ n, DecidableEq (α n)] [s : ∀ n, ToString (α n)]

instance (k) : Encodable ((relational α).func k) := Encodable.IsEmpty.toEncodable

instance (k) : Encodable ((relational α).rel k) := e k

instance (k) : DecidableEq ((relational α).func k) := fun a => by cases a

instance (k) : DecidableEq ((relational α).rel k) := d k

instance : ToString ((relational α).rel k) := ⟨fun a => "P^{" ++ toString k ++ "}_{" ++ toString a ++ "}"⟩

instance : ToString ((relational α).func k) := ⟨fun a => by cases a⟩

end relational

structure Hom (L₁ L₂ : Language) where
  onFunc : {k : ℕ} → L₁.func k → L₂.func k
  onRel : {k : ℕ} → L₁.rel k → L₂.rel k

infix:25 " →ᵥ " => Hom

namespace Hom
variable (L L₁ L₂ L₃ : Language) (Φ : Hom L₁ L₂)

protected def id : L →ᵥ L where
  onFunc := id
  onRel := id

variable {L L₁ L₂ L₃}

def comp (Ψ : L₂ →ᵥ L₃) (Φ : L₁ →ᵥ L₂) : L₁ →ᵥ L₃ where
  onFunc := Ψ.onFunc ∘ Φ.onFunc 
  onRel  := Ψ.onRel ∘ Φ.onRel 

end Hom

def subLanguage (L : Language) (pfunc : ∀ k, Language.func L k → Prop) (prel : ∀ k, L.rel k → Prop) :
    Language where
  func := fun k => Subtype (pfunc k)
  rel  := fun k => Subtype (prel k)

section subLanguage

variable (L) {pf : ∀ k, Language.func L k → Prop} {pr : ∀ k, L.rel k → Prop}

def ofSubLanguage : subLanguage L pf pr →ᵥ L where
  onFunc := Subtype.val
  onRel  := Subtype.val

@[simp] lemma ofSubLanguage_onFunc {k : ℕ} :
    (ofSubLanguage L).onFunc p = p.val := rfl

@[simp] lemma ofSubLanguage_onRel {k : ℕ} :
    (ofSubLanguage L).onRel p = p.val := rfl

end subLanguage

end Language