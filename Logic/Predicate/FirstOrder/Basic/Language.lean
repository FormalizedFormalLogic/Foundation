import Logic.Vorspiel.Vorspiel
import Mathlib.Data.Finset.Basic

namespace LO
    
namespace FirstOrder

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

inductive ORingFunc : ℕ → Type
  | zero : ORingFunc 0
  | one : ORingFunc 0
  | add : ORingFunc 2
  | mul : ORingFunc 2

inductive ORingRel : ℕ → Type
  | eq : ORingRel 2
  | lt : ORingRel 2

@[reducible]
def oRing : Language where
  func := ORingFunc
  rel := ORingRel

instance (k) : ToString (oRing.func k) :=
⟨ fun s =>
  match s with
  | ORingFunc.zero => "0"
  | ORingFunc.one  => "1"
  | ORingFunc.add  => "(+)"
  | ORingFunc.mul  => "(\\cdot)"⟩

instance (k) : ToString (oRing.rel k) :=
⟨ fun s =>
  match s with
  | ORingRel.eq => "\\mathrm{Eq}"
  | ORingRel.lt    => "\\mathrm{Lt}"⟩

instance (k) : DecidableEq (oRing.func k) := fun a b =>
  by rcases a <;> rcases b <;> simp <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : DecidableEq (oRing.rel k) := fun a b =>
  by rcases a <;> rcases b <;> simp <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : Encodable (oRing.func k) where
  encode := fun x =>
    match x with
    | ORingFunc.zero => 0
    | ORingFunc.one  => 1
    | ORingFunc.add  => 0
    | ORingFunc.mul  => 1
  decode := fun e =>
    match k, e with
    | 0, 0 => some ORingFunc.zero
    | 0, 1 => some ORingFunc.one
    | 2, 0 => some ORingFunc.add
    | 2, 1 => some ORingFunc.mul
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

instance (k) : Encodable (oRing.rel k) where
  encode := fun x =>
    match x with
    | ORingRel.eq => 0
    | ORingRel.lt    => 1
  decode := fun e =>
    match k, e with
    | 2, 0 => some ORingRel.eq
    | 2, 1 => some ORingRel.lt
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

inductive ORingWithPowPairingFunc : ℕ → Type
  | zero : ORingWithPowPairingFunc 0
  | one : ORingWithPowPairingFunc 0
  | exp : ORingWithPowPairingFunc 1
  | add : ORingWithPowPairingFunc 2
  | mul : ORingWithPowPairingFunc 2
  | pow : ORingWithPowPairingFunc 2
  | pair : ORingWithPowPairingFunc 2

@[reducible] def oRingWithExpPowPairing : Language where
  func := ORingWithPowPairingFunc
  rel := ORingRel

instance (k) : ToString (oRingWithExpPowPairing.func k) :=
⟨ fun s =>
  match s with
  | .zero => "0"
  | .one  => "1"
  | .exp  => "exp"
  | .add  => "(+)"
  | .mul  => "(\\cdot)"
  | .pow  => "(\\cdot)"
  | .pair  => "(\\mathrm{pair})"⟩

instance (k) : ToString (oRingWithExpPowPairing.rel k) :=
⟨ fun s =>
  match s with
  | ORingRel.eq => "\\mathrm{Eq}"
  | ORingRel.lt    => "\\mathrm{Lt}"⟩

instance (k) : DecidableEq (oRingWithExpPowPairing.func k) := fun a b =>
  by rcases a <;> rcases b <;> simp <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : DecidableEq (oRingWithExpPowPairing.rel k) := fun a b =>
  by rcases a <;> rcases b <;> simp <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : Encodable (oRingWithExpPowPairing.func k) where
  encode := fun x =>
    match x with
    | .zero => 0
    | .one  => 1
    | .exp  => 0
    | .add  => 0
    | .mul  => 1
    | .pow  => 2
    | .pair  => 3
  decode := fun e =>
    match k, e with
    | 0, 0 => some .zero
    | 0, 1 => some .one
    | 1, 0 => some .exp
    | 2, 0 => some .add
    | 2, 1 => some .mul
    | 2, 2 => some .pow
    | 2, 3 => some .pair
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

instance (k) : Encodable (oRingWithExpPowPairing.rel k) where
  encode := fun x =>
    match x with
    | ORingRel.eq => 0
    | ORingRel.lt    => 1
  decode := fun e =>
    match k, e with
    | 2, 0 => some ORingRel.eq
    | 2, 1 => some ORingRel.lt
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

def relational (α : ℕ → Type u) : Language where
  func := fun _ => PEmpty
  rel := α

section relational
variable {α : ℕ → Type u} [e : ∀ n, Encodable (α n)] [d : ∀ n, DecidableEq (α n)] [s : ∀ n, ToString (α n)]

instance (k) : Encodable ((relational α).func k) := Encodable.IsEmpty.toEncodable (α := PEmpty)

instance (k) : Encodable ((relational α).rel k) := e k

instance (k) : DecidableEq ((relational α).func k) := fun a => by cases a

instance (k) : DecidableEq ((relational α).rel k) := d k

instance : ToString ((relational α).rel k) :=
  ⟨fun a => "R^{" ++ toString k ++ "}_{" ++ toString (α := α k) a ++ "}"⟩

def toRelational (a : α k) : (relational α).rel k := a

instance : ToString ((relational α).func k) := ⟨fun a => by cases a⟩

end relational

class Eq (L : Language.{u}) where
  eq : L.rel 2

class Lt (L : Language.{u}) where
  lt : L.rel 2

class Zero (L : Language.{u}) where
  zero : L.func 0

class One (L : Language.{u}) where
  one : L.func 0

class Add (L : Language.{u}) where
  add : L.func 2

class Mul (L : Language.{u}) where
  mul : L.func 2

class Pow (L : Language.{u}) where
  pow : L.func 2

class Exp (L : Language.{u}) where
  exp : L.func 1

class Pairing (L : Language.{u}) where
  pair : L.func 2

attribute [match_pattern] Eq.eq Add.add Mul.mul

class ORing (L : Language) extends L.Eq, L.Lt, L.Zero, L.One, L.Add, L.Mul

instance : ORing oRing where
  eq := .eq
  lt := .lt
  zero := .zero
  one := .one
  add := .add
  mul := .mul

instance : ORing oRingWithExpPowPairing where
  eq := .eq
  lt := .lt
  zero := .zero
  one := .one
  add := .add
  mul := .mul

instance : Exp oRingWithExpPowPairing where
  exp := .exp

instance : Pow oRingWithExpPowPairing where
  pow := .pow

instance : Pairing oRingWithExpPowPairing where
  pair := .pair

structure Hom (L₁ L₂ : Language) where
  func : {k : ℕ} → L₁.func k → L₂.func k
  rel : {k : ℕ} → L₁.rel k → L₂.rel k

scoped[LO.FirstOrder] infix:25 " →ᵥ " => LO.FirstOrder.Language.Hom
 
namespace Hom
variable (L L₁ L₂ L₃ : Language) (Φ : Hom L₁ L₂)

protected def id : L →ᵥ L where
  func := id
  rel := id

variable {L L₁ L₂ L₃}

def comp (Ψ : L₂ →ᵥ L₃) (Φ : L₁ →ᵥ L₂) : L₁ →ᵥ L₃ where
  func := Ψ.func ∘ Φ.func 
  rel  := Ψ.rel ∘ Φ.rel 

end Hom

def subLanguage (L : Language) (pfunc : ∀ k, Language.func L k → Prop) (prel : ∀ k, L.rel k → Prop) :
    Language where
  func := fun k => Subtype (pfunc k)
  rel  := fun k => Subtype (prel k)

section subLanguage

variable (L) {pf : ∀ k, Language.func L k → Prop} {pr : ∀ k, L.rel k → Prop}

def ofSubLanguage : subLanguage L pf pr →ᵥ L where
  func := Subtype.val
  rel  := Subtype.val

@[simp] lemma ofSubLanguage_onFunc {k : ℕ} :
    L.ofSubLanguage.func p = p.val := rfl

@[simp] lemma ofSubLanguage_onRel {k : ℕ} :
    L.ofSubLanguage.rel p = p.val := rfl

end subLanguage

end Language

end FirstOrder

end LO