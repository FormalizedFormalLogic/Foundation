import Logic.Logic.HilbertStyle2
import Logic.Modal.Basic.Formula

namespace LO

namespace Modal

namespace Hilbert

section Axioms

variable (F : Type u) [ModalLogicSymbol F] [Hilbert F]

class HasNecessitation where
  necessitation {Γ : Finset F} {p : F} : (Γ ⊢ᴴ! p) → (Γ ⊢ᴴ! □p)

class HasAxiomK where
  K (Γ : Finset F) (p q : F) : Γ ⊢ᴴ! □(p ⟶ q) ⟶ □p ⟶ □q

class HasAxiomT where
  T (Γ : Finset F) (p : F) : Γ ⊢ᴴ! □p ⟶ p

class HasAxiomD where
  D (Γ : Finset F) (p : F) : Γ ⊢ᴴ! □p ⟶ ◇p

class HasAxiomB where
  B (Γ : Finset F) (p q : F) : Γ ⊢ᴴ! p ⟶ □◇p

class HasAxiom4 where
  A4 (Γ : Finset F) (p : F) : Γ ⊢ᴴ! □p ⟶ □□p

class HasAxiom5 where
  A5 (Γ : Finset F) (p q : F) : Γ ⊢ᴴ! ◇p ⟶ □◇p

class HasAxiomL where
  L (Γ : Finset F) (p : F) : Γ ⊢ᴴ! □(□p ⟶ p) ⟶ □p

class HasAxiomDot2 where
  Dot2 (Γ : Finset F) (p : F) : Γ ⊢ᴴ! ◇□p ⟶ □◇p

class HasAxiomDot3 where
  Dot3 (Γ : Finset F) (p : F) : Γ ⊢ᴴ! □(□p ⟶ □q) ⋎ □(□q ⟶ □p)

class HasAxiomGrz where
  Grz (Γ : Finset F) (p : F) : Γ ⊢ᴴ! □(□(p ⟶ □p) ⟶ p) ⟶ p

/-- McKinsey Axiom -/
class HasAxiomM where
  M (Γ : Finset F) (p : F) : Γ ⊢ᴴ! □◇p ⟶ ◇□p

class HasAxiomCD where
  CD (Γ : Finset F) (p : F) : Γ ⊢ᴴ! ◇p ⟶ □p

class HasAxiomC4 where
  C4 (Γ : Finset F) (p : F) : Γ ⊢ᴴ! □□p ⟶ □p

class LogicK extends Hilbert.Classical F, HasNecessitation F, HasAxiomK F

class LogicKD extends LogicK F, HasAxiomD F

class LogicKT extends LogicK F, HasAxiomT F

class LogicS4 extends LogicK F, HasAxiomT F, HasAxiom4 F

class LogicS5 extends LogicK F, HasAxiomT F, HasAxiom5 F

class LogicGL extends LogicK F, HasAxiomL F

class LogicS4Dot2 extends LogicS4 F, HasAxiomDot2 F

class LogicS4Dot3 extends LogicS4 F, HasAxiomDot3 F

class LogicS4Grz extends LogicS4 F, HasAxiomGrz F

end Axioms

namespace LogicK

variable {α : Type u}

inductive DerivationH : Finset (Formula α) → (Formula α) → Type _
  | axm {Γ p}            : p ∈ Γ → DerivationH Γ p
  | modus_ponens {Γ p q} : DerivationH Γ (p ⟶ q) → DerivationH Γ p → DerivationH Γ q
  | necessitation {Γ p}  : DerivationH Γ p → DerivationH Γ (□p)
  | verum (Γ)            : DerivationH Γ ⊤
  | imply₁ (Γ) (p q)     : DerivationH Γ (p ⟶ q ⟶ p)
  | imply₂ (Γ) (p q r)   : DerivationH Γ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  | conj₁ (Γ) (p q)      : DerivationH Γ (p ⋏ q ⟶ p)
  | conj₂ (Γ) (p q)      : DerivationH Γ (p ⋏ q ⟶ q)
  | conj₃ (Γ) (p q)      : DerivationH Γ (p ⟶ q ⟶ p ⋏ q)
  | disj₁ (Γ) (p q)      : DerivationH Γ (p ⟶ p ⋎ q)
  | disj₂ (Γ) (p q)      : DerivationH Γ (q ⟶ p ⋎ q)
  | disj₃ (Γ) (p q r)    : DerivationH Γ ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r))
  | explode (Γ p)        : DerivationH Γ (⊥ ⟶ p)
  | dne (Γ p)            : DerivationH Γ (~~p ⟶ p)
  | K (Γ) (p q)          : DerivationH Γ (□(p ⟶ q) ⟶ □p ⟶ □q)

instance : Hilbert (Formula α) := ⟨LogicK.DerivationH⟩

infixl:45 " ⊢ᴴ(𝗞) " => DerivationH

abbrev DerivableH (Γ : Finset (Formula α)) (p : Formula α) := Nonempty (Γ ⊢ᴴ(𝗞) p)

notation Γ " ⊢ᴴ(𝗞)! " p => DerivableH Γ p

abbrev ProofH (p : Formula α) := ∅ ⊢ᴴ(𝗞) p

prefix:45 "⊢ᴴ(𝗞) " => ProofH

abbrev ProvableH (p : Formula α) := Nonempty (⊢ᴴ(𝗞) p)

prefix:45 "⊢ᴴ(𝗞)! " => ProvableH

abbrev UnprovableH (p : Formula α) := IsEmpty (⊢ᴴ(𝗞) p)

prefix:45 "⊬ᴴ(𝗞)!" => UnprovableH

open DerivationH in
instance : LogicK (Formula α) where
  neg            := rfl
  axm            := by intro Γ p h; exact ⟨@axm _ Γ p h⟩
  modus_ponens   := by intro Γ p q hpq hp; exact ⟨@modus_ponens _ Γ p q hpq.some hp.some⟩;
  necessitation  := by intro Γ p hp; exact ⟨@necessitation _ Γ p hp.some⟩
  verum Γ        := ⟨verum Γ⟩
  imply₁ Γ p q   := ⟨imply₁ Γ p q⟩
  imply₂ Γ p q r := ⟨imply₂ Γ p q r⟩
  conj₁ Γ p q    := ⟨conj₁ Γ p q⟩
  conj₂ Γ p q    := ⟨conj₂ Γ p q⟩
  conj₃ Γ p q    := ⟨conj₃ Γ p q⟩
  disj₁ Γ p q    := ⟨disj₁ Γ p q⟩
  disj₂ Γ p q    := ⟨disj₂ Γ p q⟩
  disj₃ Γ p q r  := ⟨disj₃ Γ p q r⟩
  explode Γ p    := ⟨explode Γ p⟩
  dne Γ p        := ⟨dne Γ p⟩
  K Γ p q        := ⟨K Γ p q⟩

def DerivationH.length {Γ : Finset (Formula α)} {p : Formula α} : DerivationH Γ p → ℕ
  | modus_ponens d₁ d₂ => d₁.length + d₂.length + 1
  | necessitation d₁ => d₁.length + 1
  | _ => 0

namespace DerivationH

-- def length {Γ : Finset (Formula α)} {p : Formula α} : Γ ⊢ᴴ(𝗞) p → ℕ := DerivationH.length

protected def cast (d : Γ ⊢ᴴ(𝗞) p) (e₁ : Γ = Δ) (e₂ : p = q) : Δ ⊢ᴴ(𝗞) q := cast (by simp [e₁,e₂]) d

@[simp] lemma length_cast (d : Γ ⊢ᴴ(𝗞) p) (e₁ : Γ = Δ) (e₂ : p = q) : (d.cast e₁ e₂).length = d.length := by
  rcases e₁ with rfl; rcases e₂ with rfl; simp [DerivationH.cast]

def castL (d : Γ ⊢ᴴ(𝗞) p) (e₁ : Γ = Δ) : Δ ⊢ᴴ(𝗞) p := d.cast e₁ rfl

@[simp] lemma length_castL (d : Γ ⊢ᴴ(𝗞) p) (e₁ : Γ = Δ) : (d.castL e₁).length = d.length := length_cast d e₁ rfl

def castR (d : Γ ⊢ᴴ(𝗞) p) (e₂ : p = q) : Γ ⊢ᴴ(𝗞) q := d.cast rfl e₂

@[simp] lemma length_castR (d : Γ ⊢ᴴ(𝗞) p) (e₂ : p = q) : (d.castR e₂).length = d.length := length_cast d rfl e₂

end DerivationH

-- def ProofH.length {p : Formula α} : ⊢ᴴ(𝗞) p → ℕ := DerivationH.length

lemma ProvableH.dne : (⊢ᴴ(𝗞)! ~~p) → (⊢ᴴ(𝗞)! p) := by
  intro d;
  have h₁ := LogicK.DerivationH.dne ∅ p;
  have h₂ := d.some; simp [ProofH, DerivationH] at h₂;
  simp_all [ProvableH, ProofH, DerivationH];
  exact ⟨(LogicK.DerivationH.modus_ponens h₁ h₂)⟩

end LogicK

namespace LogicS4

variable {α : Type u}

inductive DerivationH : Finset (Formula α) → (Formula α) → Type _
  | drvK     : LogicK.DerivationH Γ p → DerivationH Γ p
  | T (Γ p)  : DerivationH Γ (□p ⟶ p)
  | A4 (Γ p) : DerivationH Γ (□p ⟶ □□p)

instance : Hilbert (Formula α) := ⟨LogicS4.DerivationH⟩

infixl:45 " ⊢ᴴ(𝗦𝟰) " => DerivationH

abbrev ProofH (p : Formula α) := ∅ ⊢ᴴ(𝗦𝟰) p

prefix:45 "⊢ᴴ(𝗦𝟰) " => ProofH

end LogicS4


namespace LogicS5

variable {α : Type u}

inductive DerivationH : Finset (Formula α) → (Formula α) → Type _
  | drvK : LogicK.DerivationH Γ p → DerivationH Γ p
  | T (Γ p) : DerivationH Γ (□p ⟶ p)
  | B (Γ p) : DerivationH Γ (p ⟶ □◇p)
  | A4 (Γ p) : DerivationH Γ (□p ⟶ □□p)

instance : Hilbert (Formula α) := ⟨LogicS5.DerivationH⟩

infixl:45 " ⊢ᴴ(𝗦𝟱) " => DerivationH

abbrev ProofH (p : Formula α) := ∅ ⊢ᴴ(𝗦𝟱) p

prefix:45 "⊢ᴴ(𝗦𝟱) " => ProofH

end LogicS5


namespace LogicGL

variable {α : Type u}

inductive DerivationH : Finset (Formula α) → (Formula α) → Type _
  | drvK : LogicK.DerivationH Γ p → DerivationH Γ p
  | L (Γ p) : DerivationH Γ (□(□p ⟶ p) ⟶ □p)

instance : Hilbert (Formula α) := ⟨LogicGL.DerivationH⟩



infixl:45 " ⊢ᴴ(𝗚𝗟) " => DerivationH

abbrev ProofH (p : Formula α) := ∅ ⊢ᴴ(𝗚𝗟) p

prefix:45 "⊢ᴴ(𝗚𝗟) " => ProofH

end LogicGL


namespace LogicS4Dot2

variable {α : Type u}

inductive DerivationH : Finset (Formula α) → (Formula α) → Type _
  | drvS4 : LogicS4.DerivationH Γ p → DerivationH Γ p
  | Dot2 (Γ p) : DerivationH Γ (◇□p ⟶ □◇p)

instance : Hilbert (Formula α) := ⟨LogicS4Dot2.DerivationH⟩

infixl:45 " ⊢ᴴ(𝗦𝟰.𝟮) " => DerivationH

abbrev ProofH (p : Formula α) := ∅ ⊢ᴴ(𝗦𝟰.𝟮) p

prefix:45 "⊢ᴴ(𝗦𝟰.𝟮) " => ProofH

end LogicS4Dot2


namespace LogicS4Dot3

variable {α : Type u}

inductive DerivationH : Finset (Formula α) → (Formula α) → Type _
  | drvS4 : LogicS4.DerivationH Γ p → DerivationH Γ p
  | Dot3 (Γ p) : DerivationH Γ (□(□p ⟶ □q) ⋎ □(□q ⟶ □p))

instance : Hilbert (Formula α) := ⟨LogicS4Dot3.DerivationH⟩

infixl:45 " ⊢ᴴ(𝗦𝟰.𝟯) " => DerivationH

abbrev ProofH (p : Formula α) := ∅ ⊢ᴴ(𝗦𝟰.𝟯) p

prefix:45 "⊢ᴴ(𝗦𝟰.𝟯) " => ProofH

end LogicS4Dot3


namespace LogicS4Grz

variable {α : Type u}

inductive DerivationH : Finset (Formula α) → (Formula α) → Type _
  | drvS4 : LogicS4.DerivationH Γ p → DerivationH Γ p
  | Grz (Γ p) : DerivationH Γ (□(□(p ⟶ □p) ⟶ p) ⟶ p)

instance : Hilbert (Formula α) := ⟨LogicS4Grz.DerivationH⟩

infixl:45 " ⊢ᴴ(𝗦𝟰𝗚𝗿𝘇) " => DerivationH

abbrev ProofH (p : Formula α) := ∅ ⊢ᴴ(𝗦𝟰𝗚𝗿𝘇) p

prefix:45 "⊢ᴴ(𝗦𝟰𝗚𝗿𝘇) " => ProofH

end LogicS4Grz

end Hilbert

end Modal

end LO
