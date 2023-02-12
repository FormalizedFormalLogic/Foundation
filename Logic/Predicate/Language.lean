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

def equal : Language where
  func := fun _ => Empty
  rel := EqRel

instance (k) : ToString (equal.func k) := ⟨fun _ => ""⟩

instance (k) : ToString (equal.rel k) := ⟨fun _ => "\\mathrm{Eq}"⟩

instance (k) : DecidableEq (equal.func k) := fun a b => by rcases a

instance (k) : DecidableEq (equal.rel k) := fun a b => by rcases a; rcases b; exact isTrue (by simp)

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

variable (L) {pfunc : ∀ k, Language.func L k → Prop} {prel : ∀ k, L.rel k → Prop}

def ofSub : subLanguage L pfunc prel →ᵥ L where
  onFunc := Subtype.val
  onRel  := Subtype.val

@[simp] lemma ofSub_onFunc {k : ℕ} :
    (ofSub L : subLanguage L pfunc prel →ᵥ L).onFunc p = p.val := rfl

@[simp] lemma ofSub_onRel {k : ℕ} :
    (ofSub L : subLanguage L pfunc prel →ᵥ L).onRel p = p.val := rfl

end subLanguage

end Language