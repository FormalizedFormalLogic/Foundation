import Foundation.Logic.System

/-!
# Language of first-order logic

This file defines the language of first-order logic.

- `LO.FirstOrder.Language.empty` is the empty language.
- `LO.FirstOrder.Language.constant C` is a language with only constants of the element `C`.
- `LO.FirstOrder.Language.oRing`, `ℒₒᵣ` is the language of ordered ring.
-/

namespace LO

open Primrec
namespace FirstOrder

structure Language where
  Func : Nat → Type u
  Rel  : Nat → Type u

namespace Language

class IsRelational (L : Language) where
  func_empty : ∀ k, IsEmpty (L.Func (k + 1))

class IsConstant (L : Language) extends IsRelational L where
  rel_empty  : ∀ k, IsEmpty (L.Rel k)

class ConstantInhabited (L : Language) extends Inhabited (L.Func 0)

instance {L : Language} [L.ConstantInhabited] : Inhabited (L.Func 0) := inferInstance

protected def empty : Language where
  Func := fun _ => PEmpty
  Rel  := fun _ => PEmpty

instance : Inhabited Language := ⟨Language.empty⟩

inductive GraphFunc : ℕ → Type
  | start : GraphFunc 0
  | terminal : GraphFunc 0

inductive GraphRel : ℕ → Type
  | equal : GraphRel 2
  | le : GraphRel 2

def graph : Language where
  Func := GraphFunc
  Rel := GraphRel

inductive BinaryRel : ℕ → Type
  | isone : BinaryRel 1
  | equal : BinaryRel 2
  | le : BinaryRel 2

def binary : Language where
  Func := fun _ => Empty
  Rel := BinaryRel

inductive EqRel : ℕ → Type
  | equal : EqRel 2

@[reducible]
def equal : Language where
  Func := fun _ => Empty
  Rel := EqRel

instance (k) : ToString (equal.Func k) := ⟨fun _ => ""⟩

instance (k) : ToString (equal.Rel k) := ⟨fun _ => "\\mathrm{Eq}"⟩

instance (k) : DecidableEq (equal.Func k) := fun a b => by rcases a

instance (k) : DecidableEq (equal.Rel k) := fun a b => by rcases a; rcases b; exact isTrue (by simp)

instance (k) : Encodable (equal.Func k) := IsEmpty.toEncodable

instance (k) : Encodable (equal.Rel k) where
  encode := fun _ => 0
  decode := fun _ =>
    match k with
    | 2 => some EqRel.equal
    | _ => none
  encodek := fun x => by rcases x; simp

namespace ORing

inductive Func : ℕ → Type
  | zero : Func 0
  | one : Func 0
  | add : Func 2
  | mul : Func 2

inductive Rel : ℕ → Type
  | eq : Rel 2
  | lt : Rel 2

end ORing

@[reducible]
def oRing : Language where
  Func := ORing.Func
  Rel := ORing.Rel

notation "ℒₒᵣ" => oRing

namespace ORing

instance (k) : ToString (oRing.Func k) :=
⟨ fun s =>
  match s with
  | Func.zero => "0"
  | Func.one  => "1"
  | Func.add  => "(+)"
  | Func.mul  => "(\\cdot)"⟩

instance (k) : ToString (oRing.Rel k) :=
⟨ fun s =>
  match s with
  | Rel.eq => "\\mathrm{Eq}"
  | Rel.lt    => "\\mathrm{LT}"⟩

instance (k) : DecidableEq (oRing.Func k) := fun a b =>
  by rcases a <;> rcases b <;> simp <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : DecidableEq (oRing.Rel k) := fun a b =>
  by rcases a <;> rcases b <;> simp <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : Encodable (oRing.Func k) where
  encode := fun x =>
    match x with
    | Func.zero => 0
    | Func.one  => 1
    | Func.add  => 0
    | Func.mul  => 1
  decode := fun e =>
    match k, e with
    | 0, 0 => some Func.zero
    | 0, 1 => some Func.one
    | 2, 0 => some Func.add
    | 2, 1 => some Func.mul
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

instance Func1IsEmpty : IsEmpty (oRing.Func 1) := ⟨by rintro ⟨⟩⟩

instance FuncGe3IsEmpty : ∀ k ≥ 3, IsEmpty (oRing.Func k)
  | 0       => by simp
  | 1       => by simp [show ¬3 ≤ 1 from of_decide_eq_false rfl]
  | 2       => by simp [show ¬3 ≤ 2 from of_decide_eq_false rfl]
  | (n + 3) => fun _ => ⟨by rintro ⟨⟩⟩

private lemma Func_encodeDecode_primrec : Primrec₂ (fun k e =>
  if k = 0 ∧ e = 0 then some 0
  else if k = 0 ∧ e = 1 then some 1
  else if k = 2 ∧ e = 0 then some 0
  else if k = 2 ∧ e = 1 then some 1
  else none) :=
  to₂ <| Primrec.ite (PrimrecPred.and (Primrec.eq.comp fst (const _)) (Primrec.eq.comp snd (const _))) (const _)
      <| Primrec.ite (PrimrecPred.and (Primrec.eq.comp fst (const _)) (Primrec.eq.comp snd (const _))) (const _)
      <| Primrec.ite (PrimrecPred.and (Primrec.eq.comp fst (const _)) (Primrec.eq.comp snd (const _))) (const _)
      <| Primrec.ite (PrimrecPred.and (Primrec.eq.comp fst (const _)) (Primrec.eq.comp snd (const _))) (const _)
      <| const _

instance (k) : Primcodable (oRing.Func k) where
  prim := nat_iff.mp <| (Primrec.encode.comp (Func_encodeDecode_primrec.comp (Primrec.const k) Primrec.id)).of_eq (fun e => by
    simp[Encodable.decode]
    rcases k with (_ | k)
    · rcases e with (_ | e) <;> simp
      · rfl
      · rcases e with (_ | e) <;> simp
        · rfl
    · rcases k with (_ | k) <;> simp
      · rcases k with (_ | k) <;> simp
        · rcases e with (_ | e) <;> simp
          · rfl
          · rcases e with (_ | e) <;> simp
            · rfl)

instance (k) : Encodable (oRing.Rel k) where
  encode := fun x =>
    match x with
    | Rel.eq => 0
    | Rel.lt => 1
  decode := fun e =>
    match k, e with
    | 2, 0 => some Rel.eq
    | 2, 1 => some Rel.lt
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

private lemma Rel_encodeDecode_primrec : Primrec₂ (fun k e =>
  if k = 2 ∧ e = 0 then some 0
  else if k = 2 ∧ e = 1 then some 1
  else none) :=
  to₂ <| Primrec.ite (PrimrecPred.and (Primrec.eq.comp fst (const _)) (Primrec.eq.comp snd (const _))) (const _)
      <| Primrec.ite (PrimrecPred.and (Primrec.eq.comp fst (const _)) (Primrec.eq.comp snd (const _))) (const _)
      <| const _

instance (k) : Primcodable (oRing.Rel k) where
  prim := nat_iff.mp <| (Primrec.encode.comp (Rel_encodeDecode_primrec.comp (Primrec.const k) Primrec.id)).of_eq (fun e => by
    simp[Encodable.decode]
    rcases k with (_ | k) <;> simp
    rcases k with (_ | k) <;> simp
    rcases k with (_ | k) <;> simp
    rcases e with (_ | e) <;> simp
    · rfl
    · rcases e with (_ | e) <;> simp
      · rfl)

end ORing

namespace ORingExp

inductive Func : ℕ → Type
  | zero : Func 0
  | one : Func 0
  | exp : Func 1
  | add : Func 2
  | mul : Func 2

inductive Rel : ℕ → Type
  | eq : Rel 2
  | lt : Rel 2

end ORingExp

@[reducible]
def oRingExp : Language where
  Func := ORingExp.Func
  Rel := ORingExp.Rel

notation "ℒₒᵣ(exp)" => oRingExp

namespace ORingExp

instance (k) : ToString (oRingExp.Func k) :=
⟨ fun s =>
  match s with
  | Func.zero => "0"
  | Func.one  => "1"
  | Func.exp  => "(^)"
  | Func.add  => "(+)"
  | Func.mul  => "(\\cdot)"⟩

instance (k) : ToString (oRingExp.Rel k) :=
⟨ fun s =>
  match s with
  | Rel.eq => "\\mathrm{Eq}"
  | Rel.lt    => "\\mathrm{LT}"⟩

instance (k) : DecidableEq (oRingExp.Func k) := fun a b =>
  by rcases a <;> rcases b <;> simp <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : DecidableEq (oRingExp.Rel k) := fun a b =>
  by rcases a <;> rcases b <;> simp <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

end ORingExp

namespace Constant

variable (C : Type*)

inductive Func : ℕ → Type _
  | const (c : C) : Func 0

end Constant

section Constant

variable (C : Type*)

def constant : Language := ⟨Constant.Func C, fun _ => PEmpty⟩

--instance : Coe (Type*) Language := ⟨constant⟩

instance : Coe C ((constant C).Func 0) := ⟨Constant.Func.const⟩

instance : IsConstant (constant C) where
  func_empty := fun k => ⟨by rintro ⟨⟩⟩
  rel_empty  := fun k => ⟨by rintro ⟨⟩⟩

abbrev unit : Language := constant PUnit

end Constant

def ofFunc (F : ℕ → Type v) : Language := ⟨F, fun _ => PEmpty⟩

def add (L₁ : Language.{u₁}) (L₂ : Language.{u₂}) : Language :=
  ⟨fun k => L₁.Func k ⊕ L₂.Func k, fun k => L₁.Rel k ⊕ L₂.Rel k⟩

instance : _root_.Add Language := ⟨add⟩

def sigma (L : ι → Language) : Language := ⟨fun k => Σ i, (L i).Func k, fun k => Σ i, (L i).Rel k⟩

protected class Eq (L : Language) where
  eq : L.Rel 2

protected class LT (L : Language) where
  lt : L.Rel 2

protected class Zero (L : Language) where
  zero : L.Func 0

protected class One (L : Language) where
  one : L.Func 0

protected class Add (L : Language) where
  add : L.Func 2

protected class Mul (L : Language) where
  mul : L.Func 2

protected class Pow (L : Language) where
  pow : L.Func 2

protected class Exp (L : Language) where
  exp : L.Func 1

class Pairing (L : Language) where
  pair : L.Func 2

class Star (L : Language) where
  star : L.Func 0

attribute [match_pattern] Zero.zero One.one Add.add Mul.mul Exp.exp Eq.eq LT.lt Star.star

class ORing (L : Language) extends L.Eq, L.LT, L.Zero, L.One, L.Add, L.Mul

instance : ORing oRing where
  eq := .eq
  lt := .lt
  zero := .zero
  one := .one
  add := .add
  mul := .mul

instance : ConstantInhabited ℒₒᵣ where
  default := Language.Zero.zero

instance : ORing oRingExp where
  eq := .eq
  lt := .lt
  zero := .zero
  one := .one
  add := .add
  mul := .mul

instance : Language.Exp oRingExp where
  exp := .exp

instance : Star unit where
  star := ()

instance (L : Language) (S : Language) [Star S] : Star (L.add S) where
  star := Sum.inr Star.star

instance (L : Language) (S : Language) [L.Zero] : (L.add S).Zero where
  zero := Sum.inl Zero.zero

instance (L : Language) (S : Language) [L.One] : (L.add S).One where
  one := Sum.inl One.one

instance (L : Language) (S : Language) [L.Add] : (L.add S).Add where
  add := Sum.inl Add.add

instance (L : Language) (S : Language) [L.Mul] : (L.add S).Mul where
  mul := Sum.inl Mul.mul

instance (L : Language) (S : Language) [L.Eq] : (L.add S).Eq where
  eq := Sum.inl Eq.eq

instance (L : Language) (S : Language) [L.LT] : (L.add S).LT where
  lt := Sum.inl LT.lt

/-
namespace ORing

open Qq Lean Elab Meta Tactic

def denoteFunc : (k : ℕ) → Q(oRing.Func $k) → MetaM (oRing.Func k)
  | 0, e =>
    match e with
    | ∼ψ(Zero.zero) => return Language.Zero.zero
    | ∼ψ(One.one)   => return Language.One.one
  | 2, e =>
    match e with
    | ∼ψ(Language.Add.add) => return Language.Add.add
    | ∼ψ(Language.Mul.mul) => return Language.Mul.mul
  | _, e => throwError m!"error in DenotationORing : {e}"

def denoteRel : (k : ℕ) → Q(oRing.Rel $k) → MetaM (oRing.Rel k)
  | 2, e =>
    match e with
    | ∼ψ(Language.Eq.eq) => return Language.Eq.eq
    | ∼ψ(Language.LT.lt) => return Language.LT.lt
  | _, e => throwError m!"error in DenotationORing : {e}"

instance (k : ℕ) : Denotation ψ(oRing.Func $k) (oRing.Func k) where
   denote := denoteFunc k
   toExpr := fun f =>
     ( match f with
       | Func.zero => ψ(Language.Zero.zero)
       | Func.one  => ψ(Language.One.one)
       | Func.add  => ψ(Language.Add.add)
       | Func.mul  => ψ(Language.Mul.mul) : Q(oRing.Func $k))

instance (k : ℕ) : Denotation ψ(oRing.Rel $k) (oRing.Rel k) where
   denote := denoteRel k
   toExpr := fun f =>
     ( match f with
       | Rel.eq => ψ(Language.Eq.eq)
       | Rel.lt => ψ(Language.LT.lt) : Q(oRing.Rel $k))

end ORing
-/

@[ext] structure Hom (L₁ L₂ : Language) where
  func : {k : ℕ} → L₁.Func k → L₂.Func k
  rel : {k : ℕ} → L₁.Rel k → L₂.Rel k

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

def add₁ (L₁ : Language) (L₂ : Language) : L₁ →ᵥ L₁.add L₂ := ⟨Sum.inl, Sum.inl⟩

def add₂ (L₁ : Language) (L₂ : Language) : L₂ →ᵥ L₁.add L₂ := ⟨Sum.inr, Sum.inr⟩

lemma func_add₁ (L₁ : Language) (L₂ : Language) (f : L₁.Func k) :
    (add₁ L₁ L₂).func f = Sum.inl f := rfl

lemma rel_add₁ (L₁ : Language) (L₂ : Language) (r : L₁.Rel k) :
    (add₁ L₁ L₂).rel r = Sum.inl r := rfl

lemma func_add₂ (L₁ : Language) (L₂ : Language) (f : L₂.Func k) :
    (add₂ L₁ L₂).func f = Sum.inr f := rfl

lemma rel_add₂ (L₁ : Language) (L₂ : Language) (r : L₂.Rel k) :
    (add₂ L₁ L₂).rel r = Sum.inr r := rfl

@[simp] lemma add₂_star (L₁ : Language) (L₂ : Language) [Star L₂] :
    (add₂ L₁ L₂).func Star.star = Star.star := rfl

@[simp] lemma add₁_zero (L₁ : Language) (L₂ : Language) [L₁.Zero] :
    (add₁ L₁ L₂).func Zero.zero = Zero.zero := rfl

@[simp] lemma add₁_one (L₁ : Language) (L₂ : Language) [L₁.One] :
    (add₁ L₁ L₂).func One.one = One.one := rfl

@[simp] lemma add₁_add (L₁ : Language) (L₂ : Language) [L₁.Add] :
    (add₁ L₁ L₂).func Add.add = Add.add := rfl

@[simp] lemma add₁_mul (L₁ : Language) (L₂ : Language) [L₁.Mul] :
    (add₁ L₁ L₂).func Mul.mul = Mul.mul := rfl

@[simp] lemma add₁_eq (L₁ : Language) (L₂ : Language) [L₁.Eq] :
    (add₁ L₁ L₂).rel Eq.eq = Eq.eq := rfl

@[simp] lemma add₁_lt (L₁ : Language) (L₂ : Language) [L₁.LT] :
    (add₁ L₁ L₂).rel LT.lt = LT.lt := rfl

def sigma (L : ι → Language) (i : ι) : L i →ᵥ Language.sigma L := ⟨fun f => ⟨i, f⟩, fun r => ⟨i, r⟩⟩

lemma func_sigma (L : ι → Language) (i : ι) (f : (L i).Func k) : (sigma L i).func f = ⟨i, f⟩ := rfl

lemma rel_sigma (L : ι → Language) (i : ι) (r : (L i).Rel k) : (sigma L i).rel r = ⟨i, r⟩ := rfl

end Hom

def ORing.embedding (L : Language) [ORing L] : ℒₒᵣ →ᵥ L where
  func := fun {n} f ↦
    match n, f with
    | 0, Zero.zero => Zero.zero
    | 0, One.one   => One.one
    | 2, Add.add   => Add.add
    | 2, Mul.mul   => Mul.mul
  rel := fun {n} r ↦
    match n, r with
    | 2, Eq.eq => Eq.eq
    | 2, LT.lt => LT.lt
end Language

end FirstOrder

end LO
