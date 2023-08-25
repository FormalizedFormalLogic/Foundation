import Logic.Vorspiel.Vorspiel
import Mathlib.Data.Finset.Basic

namespace Language

inductive GraphFunc : ℕ → Type
  | start : GraphFunc 0
  | terminal : GraphFunc 0

inductive GraphRel : ℕ → Type
  | equal : GraphRel 2
  | le : GraphRel 2

inductive BinaryRel : ℕ → Type
  | isone : BinaryRel 1
  | equal : BinaryRel 2
  | le : BinaryRel 2

inductive EqRel : ℕ → Type
  | equal : EqRel 2

instance (k) : ToString (EqRel k) := ⟨fun _ => "\\mathrm{Eq}"⟩

instance (k) : Encodable (EqRel k) where
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

instance (k) : ToString (ORingFunc k) :=
⟨ fun s =>
  match s with
  | ORingFunc.zero => "0"
  | ORingFunc.one  => "1"
  | ORingFunc.add  => "(+)"
  | ORingFunc.mul  => "(\\cdot)"⟩

instance (k) : ToString (ORingRel k) :=
⟨ fun s =>
  match s with
  | ORingRel.eq => "\\mathrm{Eq}"
  | ORingRel.lt    => "\\mathrm{Lt}"⟩

instance (k) : DecidableEq (ORingFunc k) := fun a b =>
  by rcases a <;> rcases b <;> simp <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : DecidableEq (ORingRel k) := fun a b =>
  by rcases a <;> rcases b <;> simp <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : Encodable (ORingFunc k) where
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

instance (k) : Encodable (ORingRel k) where
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

instance (k) : ToString (ORingWithPowPairingFunc k) :=
⟨ fun s =>
  match s with
  | .zero => "0"
  | .one  => "1"
  | .exp  => "exp"
  | .add  => "(+)"
  | .mul  => "(\\cdot)"
  | .pow  => "(\\cdot)"
  | .pair  => "(\\mathrm{pair})"⟩

instance (k) : DecidableEq (ORingWithPowPairingFunc k) := fun a b =>
  by rcases a <;> rcases b <;> simp <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : Encodable (ORingWithPowPairingFunc k) where
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

class Eq (Lr : ℕ → Type u) where
  eq : Lr 2

class Lt (Lr : ℕ → Type u) where
  lt : Lr 2

class Zero (Lf : ℕ → Type u) where
  zero : Lf 0

class One (Lf : ℕ → Type u) where
  one : Lf 0

class Add (Lf : ℕ → Type u) where
  add : Lf 2

class Mul (Lf : ℕ → Type u) where
  mul : Lf 2

class Pow (Lf : ℕ → Type u) where
  pow : Lf 2

class Exp (Lf : ℕ → Type u) where
  exp : Lf 1

class Pairing (Lf : ℕ → Type u) where
  pair : Lf 2

attribute [match_pattern] Eq.eq Add.add Mul.mul

class ORing (Lf Lr : ℕ → Type u) extends Eq Lr, Lt Lr, Zero Lf, One Lf, Add Lf, Mul Lf

instance : ORing ORingFunc ORingRel where
  eq := .eq
  lt := .lt
  zero := .zero
  one := .one
  add := .add
  mul := .mul

instance : ORing ORingWithPowPairingFunc ORingRel where
  eq := .eq
  lt := .lt
  zero := .zero
  one := .one
  add := .add
  mul := .mul

instance : Exp ORingWithPowPairingFunc where
  exp := .exp

instance : Pow ORingWithPowPairingFunc where
  pow := .pow

instance : Pairing ORingWithPowPairingFunc where
  pair := .pair

/-
structure Hom (L₁ L₂ : ℕ → Type u) where
  toFun : {k : ℕ} → L₁ k → L₂ k

infix:25 " →ᵥ " => Hom

namespace Hom
variable (L L₁ L₂ L₃ : ℕ → Type u) (Φ : Hom L₁ L₂)

protected def id : L →ᵥ L where
  toFun := id

variable {L L₁ L₂ L₃}

def comp (Ψ : L₂ →ᵥ L₃) (Φ : L₁ →ᵥ L₂) : L₁ →ᵥ L₃ where
  toFun := Ψ.toFun ∘ Φ.toFun

end Hom
-/

end Language