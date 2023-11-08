import Logic.Logic.Logic
import Logic.Vorspiel.Computability
import Logic.Vorspiel.Meta

namespace LO

open Primrec
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

instance (k) : Encodable (equal.func k) := IsEmpty.toEncodable

instance (k) : Encodable (equal.rel k) where
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
  func := ORing.Func
  rel := ORing.Rel

namespace ORing

instance (k) : ToString (oRing.func k) :=
⟨ fun s =>
  match s with
  | Func.zero => "0"
  | Func.one  => "1"
  | Func.add  => "(+)"
  | Func.mul  => "(\\cdot)"⟩

instance (k) : ToString (oRing.rel k) :=
⟨ fun s =>
  match s with
  | Rel.eq => "\\mathrm{Eq}"
  | Rel.lt    => "\\mathrm{LT}"⟩

instance (k) : DecidableEq (oRing.func k) := fun a b =>
  by rcases a <;> rcases b <;> simp <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : DecidableEq (oRing.rel k) := fun a b =>
  by rcases a <;> rcases b <;> simp <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : Encodable (oRing.func k) where
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

instance Func1IsEmpty : IsEmpty (oRing.func 1) := ⟨by rintro ⟨⟩⟩

instance FuncGe3IsEmpty : ∀ k ≥ 3, IsEmpty (oRing.func k)
  | 0       => by simp
  | 1       => by simp
  | 2       => by simp
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

instance (k) : Primcodable (oRing.func k) where
  prim := nat_iff.mp <| (Primrec.encode.comp (Func_encodeDecode_primrec.comp (Primrec.const k) Primrec.id)).of_eq (fun e => by
    simp[Encodable.decode]
    rcases k with (_ | k)
    · rcases e with (_ | e) <;> simp; rcases e with (_ | e) <;> simp
    · rcases k with (_ | k) <;> simp
      · rcases k with (_ | k) <;> simp
        · rcases e with (_ | e) <;> simp; rcases e with (_ | e) <;> simp)

instance : UniformlyPrimcodable oRing.func := UniformlyPrimcodable.ofEncodeDecode
  (Func_encodeDecode_primrec.of_eq $ fun k e => by
    simp[Encodable.encodeDecode, Encodable.decode]
    rcases k with (_ | k)
    · rcases e with (_ | e) <;> simp; rcases e with (_ | e) <;> simp
    · rcases k with (_ | k) <;> simp
      · rcases k with (_ | k) <;> simp
        · rcases e with (_ | e) <;> simp; rcases e with (_ | e) <;> simp)

instance (k) : Encodable (oRing.rel k) where
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

instance (k) : Primcodable (oRing.rel k) where
  prim := nat_iff.mp <| (Primrec.encode.comp (Rel_encodeDecode_primrec.comp (Primrec.const k) Primrec.id)).of_eq (fun e => by
    simp[Encodable.decode]
    rcases k with (_ | k) <;> simp
    rcases k with (_ | k) <;> simp
    rcases k with (_ | k) <;> simp
    rcases e with (_ | e) <;> simp
    rcases e with (_ | e) <;> simp)

instance : UniformlyPrimcodable oRing.rel := UniformlyPrimcodable.ofEncodeDecode
  (Rel_encodeDecode_primrec.of_eq $ fun k e => by
    simp[Encodable.encodeDecode, Encodable.decode]
    rcases k with (_ | k) <;> simp
    rcases k with (_ | k) <;> simp
    rcases k with (_ | k) <;> simp
    rcases e with (_ | e) <;> simp
    rcases e with (_ | e) <;> simp)

end ORing

def relational (α : ℕ → Type u) : Language where
  func := fun _ => PEmpty
  rel := α

section relational
variable {α : ℕ → Type u} [e : ∀ n, Encodable (α n)] [d : ∀ n, DecidableEq (α n)] [s : ∀ n, ToString (α n)]

instance (k) : Encodable ((relational α).func k) := IsEmpty.toEncodable (α := PEmpty)

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

class LT (L : Language.{u}) where
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

class ORing (L : Language) extends L.Eq, L.LT, L.Zero, L.One, L.Add, L.Mul

instance : ORing oRing where
  eq := .eq
  lt := .lt
  zero := .zero
  one := .one
  add := .add
  mul := .mul

/-
namespace ORing

open Qq Lean Elab Meta Tactic

def denoteFunc : (k : ℕ) → Q(oRing.func $k) → MetaM (oRing.func k)
  | 0, e =>
    match e with
    | ~q(Zero.zero) => return Language.Zero.zero
    | ~q(One.one)   => return Language.One.one
  | 2, e =>
    match e with
    | ~q(Language.Add.add) => return Language.Add.add
    | ~q(Language.Mul.mul) => return Language.Mul.mul
  | _, e => throwError m!"error in DenotationORing : {e}"

def denoteRel : (k : ℕ) → Q(oRing.rel $k) → MetaM (oRing.rel k)
  | 2, e =>
    match e with
    | ~q(Language.Eq.eq) => return Language.Eq.eq
    | ~q(Language.LT.lt) => return Language.LT.lt
  | _, e => throwError m!"error in DenotationORing : {e}"

instance (k : ℕ) : Denotation q(oRing.func $k) (oRing.func k) where
   denote := denoteFunc k
   toExpr := fun f =>
     ( match f with
       | Func.zero => q(Language.Zero.zero)
       | Func.one  => q(Language.One.one)
       | Func.add  => q(Language.Add.add)
       | Func.mul  => q(Language.Mul.mul) : Q(oRing.func $k))

instance (k : ℕ) : Denotation q(oRing.rel $k) (oRing.rel k) where
   denote := denoteRel k
   toExpr := fun f =>
     ( match f with
       | Rel.eq => q(Language.Eq.eq)
       | Rel.lt => q(Language.LT.lt) : Q(oRing.rel $k))

end ORing
-/

def ofFunc (F : ℕ → Type v) : Language := ⟨F, fun _ => PEmpty⟩

def add (L₁ : Language.{u₁}) (L₂ : Language.{u₂}) : Language :=
  ⟨fun k => L₁.func k ⊕ L₂.func k, fun k => L₁.rel k ⊕ L₂.rel k⟩

instance : _root_.Add Language := ⟨add⟩

def sigma (L : ι → Language) : Language := ⟨fun k => Σ i, (L i).func k, fun k => Σ i, (L i).rel k⟩

@[ext] structure Hom (L₁ L₂ : Language) where
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

def add₁ (L₁ : Language.{u₁}) (L₂ : Language.{u₂}) : L₁ →ᵥ L₁.add L₂ := ⟨Sum.inl, Sum.inl⟩

def add₂ (L₁ : Language.{u₁}) (L₂ : Language.{u₂}) : L₂ →ᵥ L₁.add L₂ := ⟨Sum.inr, Sum.inr⟩

@[simp] lemma func_add₁ (L₁ : Language.{u₁}) (L₂ : Language.{u₂}) (f : L₁.func k) :
    (add₁ L₁ L₂).func f = Sum.inl f := rfl

@[simp] lemma rel_add₁ (L₁ : Language.{u₁}) (L₂ : Language.{u₂}) (r : L₁.rel k) :
    (add₁ L₁ L₂).rel r = Sum.inl r := rfl

@[simp] lemma func_add₂ (L₁ : Language.{u₁}) (L₂ : Language.{u₂}) (f : L₂.func k) :
    (add₂ L₁ L₂).func f = Sum.inr f := rfl

@[simp] lemma rel_add₂ (L₁ : Language.{u₁}) (L₂ : Language.{u₂}) (r : L₂.rel k) :
    (add₂ L₁ L₂).rel r = Sum.inr r := rfl

def sigma (L : ι → Language) (i : ι) : L i →ᵥ Language.sigma L := ⟨fun f => ⟨i, f⟩, fun r => ⟨i, r⟩⟩

@[simp] lemma func_sigma (L : ι → Language) (i : ι) (f : (L i).func k) : (sigma L i).func f = ⟨i, f⟩ := rfl

@[simp] lemma rel_sigma (L : ι → Language) (i : ι) (r : (L i).rel k) : (sigma L i).rel r = ⟨i, r⟩ := rfl

end Hom

end Language

end FirstOrder

end LO
