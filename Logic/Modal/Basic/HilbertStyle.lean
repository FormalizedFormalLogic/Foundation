import Logic.Logic.HilbertStyle2
import Logic.Modal.Basic.Formula

namespace LO

namespace Modal

namespace Hilbert

section Axioms

variable (F : Type u) [ModalLogicSymbol F] [TwoSided F]

class HasNecessitation where
  necessitation {Γ : List F} {p : F} : (Γ ⊢ᴴ p) → (Γ ⊢ᴴ □p)

class HasAxiomK where
  K (Γ : List F) (p q : F) : Γ ⊢ᴴ □(p ⟶ q) ⟶ □p ⟶ □q

class HasAxiomT where
  T (Γ : List F) (p : F) : Γ ⊢ᴴ □p ⟶ p

class HasAxiomD where
  D (Γ : List F) (p : F) : Γ ⊢ᴴ □p ⟶ ◇p

class HasAxiomB where
  B (Γ : List F) (p q : F) : Γ ⊢ᴴ p ⟶ □◇p

class HasAxiom4 where
  A4 (Γ : List F) (p : F) : Γ ⊢ᴴ □p ⟶ □□p

class HasAxiom5 where
  A5 (Γ : List F) (p q : F) : Γ ⊢ᴴ ◇p ⟶ □◇p

class HasAxiomL where
  L (Γ : List F) (p : F) : Γ ⊢ᴴ □(□p ⟶ p) ⟶ □p

class HasAxiomDot2 where
  Dot2 (Γ : List F) (p : F) : Γ ⊢ᴴ ◇□p ⟶ □◇p

class HasAxiomDot3 where
  Dot3 (Γ : List F) (p : F) : Γ ⊢ᴴ □(□p ⟶ □q) ⋎ □(□q ⟶ □p)

class HasAxiomGrz where
  Grz (Γ : List F) (p : F) : Γ ⊢ᴴ □(□(p ⟶ □p) ⟶ p) ⟶ p

/-- McKinsey Axiom -/
class HasAxiomM where
  M (Γ : List F) (p : F) : Γ ⊢ᴴ □◇p ⟶ ◇□p

class HasAxiomCD where
  CD (Γ : List F) (p : F) : Γ ⊢ᴴ ◇p ⟶ □p

class HasAxiomC4 where
  C4 (Γ : List F) (p : F) : Γ ⊢ᴴ □□p ⟶ □p

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

inductive DerivationH' : List (Formula α) → List (Formula α) → Type _
  | axm {Γ p}            : p ∈ Γ → DerivationH' Γ [p]
  | modus_ponens {Γ p q} : DerivationH' Γ [p ⟶ q] → DerivationH' Γ [p] → DerivationH' Γ [q]
  | verum (Γ)            : DerivationH' Γ [⊤]
  | imply₁ (Γ) (p q)     : DerivationH' Γ [p ⟶ q ⟶ p]
  | imply₂ (Γ) (p q r)   : DerivationH' Γ [(p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r]
  | conj₁ (Γ) (p q)      : DerivationH' Γ [p ⋏ q ⟶ p]
  | conj₂ (Γ) (p q)      : DerivationH' Γ [p ⋏ q ⟶ q]
  | conj₃ (Γ) (p q)      : DerivationH' Γ [p ⟶ q ⟶ p ⋏ q]
  | disj₁ (Γ) (p q)      : DerivationH' Γ [p ⟶ p ⋎ q]
  | disj₂ (Γ) (p q)      : DerivationH' Γ [q ⟶ p ⋎ q]
  | disj₃ (Γ) (p q r)    : DerivationH' Γ [(p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)]
  | explode (Γ) (p)      : DerivationH' Γ [⊥ ⟶ p]
  | em (Γ) (p)           : DerivationH' Γ [p ⋎ ~p]
  | necessitation {Γ p}  : DerivationH' Γ [p] → DerivationH' Γ [□p]
  | K (Γ) (p q)          : DerivationH' Γ [□(p ⟶ q) ⟶ □p ⟶ □q]

instance : TwoSided (Formula α) := ⟨LogicK.DerivationH'⟩

def DerivationH (Γ : List (Formula α)) (p : Formula α) := LogicK.DerivationH' Γ [p]

infixl:45 " ⊢ᴴ(𝗞) " => DerivationH

abbrev DerivableH (Γ : List (Formula α)) (p : Formula α) := Nonempty (Γ ⊢ᴴ(𝗞) p)

notation Γ " ⊢ᴴ(𝗞)! " p => DerivableH Γ p

abbrev ProofH (p : Formula α) := ∅ ⊢ᴴ(𝗞) p

prefix:45 "⊢ᴴ(𝗞) " => ProofH

abbrev ProvableH (p : Formula α) := Nonempty (⊢ᴴ(𝗞) p)

prefix:45 "⊢ᴴ(𝗞)! " => ProvableH

abbrev UnprovableH (p : Formula α) := IsEmpty (⊢ᴴ(𝗞) p)

prefix:45 "⊬ᴴ(𝗞)!" => UnprovableH

instance : LogicK (Formula α) where
  neg := rfl
  necessitation := LogicK.DerivationH'.necessitation
  K := LogicK.DerivationH'.K
  axm := LogicK.DerivationH'.axm
  modus_ponens := LogicK.DerivationH'.modus_ponens
  verum := LogicK.DerivationH'.verum
  imply₁ := LogicK.DerivationH'.imply₁
  imply₂ := LogicK.DerivationH'.imply₂
  conj₁ := LogicK.DerivationH'.conj₁
  conj₂ := LogicK.DerivationH'.conj₂
  conj₃ := LogicK.DerivationH'.conj₃
  disj₁ := LogicK.DerivationH'.disj₁
  disj₂ := LogicK.DerivationH'.disj₂
  disj₃ := LogicK.DerivationH'.disj₃
  explode := LogicK.DerivationH'.explode
  em := LogicK.DerivationH'.em

def DerivationH'.length {Γ Δ : List (Formula α)} : DerivationH' Γ Δ → ℕ
  | modus_ponens d₁ d₂ => d₁.length + d₂.length + 1
  | necessitation d₁ => d₁.length + 1
  | _ => 0

namespace DerivationH

def length {Γ : List (Formula α)} {p : Formula α} : Γ ⊢ᴴ(𝗞) p → ℕ := DerivationH'.length

protected def cast (d : Γ ⊢ᴴ(𝗞) p) (e₁ : Γ = Δ) (e₂ : p = q) : Δ ⊢ᴴ(𝗞) q := cast (by simp [e₁,e₂]) d

@[simp] lemma length_cast (d : Γ ⊢ᴴ(𝗞) p) (e₁ : Γ = Δ) (e₂ : p = q) : (d.cast e₁ e₂).length = d.length := by
  rcases e₁ with rfl; rcases e₂ with rfl; simp [DerivationH.cast]

def castL (d : Γ ⊢ᴴ(𝗞) p) (e₁ : Γ = Δ) : Δ ⊢ᴴ(𝗞) p := d.cast e₁ rfl

@[simp] lemma length_castL (d : Γ ⊢ᴴ(𝗞) p) (e₁ : Γ = Δ) : (d.castL e₁).length = d.length := length_cast d e₁ rfl

def castR (d : Γ ⊢ᴴ(𝗞) p) (e₂ : p = q) : Γ ⊢ᴴ(𝗞) q := d.cast rfl e₂

@[simp] lemma length_castR (d : Γ ⊢ᴴ(𝗞) p) (e₂ : p = q) : (d.castR e₂).length = d.length := length_cast d rfl e₂

end DerivationH

def ProofH.length {p : Formula α} : ⊢ᴴ(𝗞) p → ℕ := DerivationH.length

end LogicK

namespace LogicS4

variable {α : Type u}

inductive DerivationH' : List (Formula α) → List (Formula α) → Type _
  | drvK : LogicK.DerivationH' Γ Δ → DerivationH' Γ Δ
  | T (Γ) (p) : DerivationH' Γ [□p ⟶ p]
  | A4 (Γ) (p) : DerivationH' Γ [□p ⟶ □□p]

instance : TwoSided (Formula α) := ⟨LogicS4.DerivationH'⟩

def DerivationH (Γ : List (Formula α)) (p : Formula α) := DerivationH' Γ [p]

infixl:45 " ⊢ᴴ(𝗦𝟰) " => DerivationH

abbrev ProofH (p : Formula α) := ∅ ⊢ᴴ(𝗦𝟰) p

prefix:45 "⊢ᴴ(𝗦𝟰) " => ProofH

end LogicS4


namespace LogicS5

variable {α : Type u}

inductive DerivationH' : List (Formula α) → List (Formula α) → Type _
  | drvK : LogicK.DerivationH' Γ Δ → DerivationH' Γ Δ
  | T (Γ) (p) : DerivationH' Γ [□p ⟶ p]
  | B (Γ) (p) : DerivationH' Γ [p ⟶ □◇p]
  | A4 (Γ) (p) : DerivationH' Γ [□p ⟶ □□p]

instance : TwoSided (Formula α) := ⟨LogicS5.DerivationH'⟩

def DerivationH (Γ : List (Formula α)) (p : Formula α) := DerivationH' Γ [p]

infixl:45 " ⊢ᴴ(𝗦𝟱) " => DerivationH

abbrev ProofH (p : Formula α) := ∅ ⊢ᴴ(𝗦𝟱) p

prefix:45 "⊢ᴴ(𝗦𝟱) " => ProofH


/-
instance : LogicS5 (Formula α) where
  necessitation := LogicS5.DerivationH'.necessitation
  K := LogicS5.DerivationH'.K _ _ _
  T := LogicS5.DerivationH'.T _ _
  B := LogicS5.DerivationH'.B _ _
  A4 := LogicS5.DerivationH'.A4 _ _
-/

end LogicS5


namespace LogicGL

variable {α : Type u}

inductive DerivationH' : List (Formula α) → List (Formula α) → Type _
  | modus_ponens {Γ p q} : (DerivationH' Γ [p ⟶ q]) → (DerivationH' Γ [p]) → (DerivationH' Γ [q])
  | necessitation {Γ p} : (DerivationH' Γ [p]) → (DerivationH' Γ [□p])
  | verum (Γ) : DerivationH' Γ [⊤]
  | K (Γ) (p q) : DerivationH' Γ [□(p ⟶ q) ⟶ □p ⟶ □q]
  | L (Γ) (p) : DerivationH' Γ [□(□p ⟶ p) ⟶ □p]

instance : TwoSided (Formula α) := ⟨LogicGL.DerivationH'⟩

def DerivationH (Γ : List (Formula α)) (p : Formula α) := DerivationH' Γ [p]

infixl:45 " ⊢ᴴ(𝗚𝗟) " => DerivationH

abbrev ProofH (p : Formula α) := ∅ ⊢ᴴ(𝗚𝗟) p

prefix:45 "⊢ᴴ(𝗚𝗟) " => ProofH


/-
instance : LogicGL (Formula α) where
  necessitation := LogicGL.DerivationH'.necessitation
  K := LogicGL.DerivationH'.K _ _ _
  L := LogicGL.DerivationH'.L _ _
-/

end LogicGL


namespace LogicS4Dot2

variable {α : Type u}

inductive DerivationH' : List (Formula α) → List (Formula α) → Type _
  | modus_ponens {Γ p q} : (DerivationH' Γ [p ⟶ q]) → (DerivationH' Γ [p]) → (DerivationH' Γ [q])
  | necessitation {Γ p} : (DerivationH' Γ [p]) → (DerivationH' Γ [□p])
  | verum (Γ) : DerivationH' Γ [⊤]
  | K (Γ) (p q) : DerivationH' Γ [□(p ⟶ q) ⟶ □p ⟶ □q]
  | T (Γ) (p) : DerivationH' Γ [□p ⟶ p]
  | B (Γ) (p) : DerivationH' Γ [p ⟶ □◇p]
  | A4 (Γ) (p) : DerivationH' Γ [□p ⟶ □□p]
  | Dot2 (Γ) (p) : DerivationH' Γ [◇□p ⟶ □◇p]

instance : TwoSided (Formula α) := ⟨LogicS4Dot2.DerivationH'⟩

def DerivationH (Γ : List (Formula α)) (p : Formula α) := DerivationH' Γ [p]

infixl:45 " ⊢ᴴ(𝗦𝟰.𝟮) " => DerivationH

abbrev ProofH (p : Formula α) := ∅ ⊢ᴴ(𝗦𝟰.𝟮) p

prefix:45 "⊢ᴴ(𝗦𝟰.𝟮) " => ProofH

/-
instance : LogicS4Dot2 (Formula α) where
  necessitation := LogicS4Dot2.DerivationH'.necessitation
  K := LogicS4Dot2.DerivationH'.K _ _ _
  T := LogicS4Dot2.DerivationH'.T _ _
  A4 := LogicS4Dot2.DerivationH'.A4 _ _
  Dot2 := LogicS4Dot2.DerivationH'.Dot2 _ _
-/

end LogicS4Dot2


namespace LogicS4Dot3

variable {α : Type u}

inductive DerivationH' : List (Formula α) → List (Formula α) → Type _
  | modus_ponens {Γ p q} : (DerivationH' Γ [p ⟶ q]) → (DerivationH' Γ [p]) → (DerivationH' Γ [q])
  | necessitation {Γ p} : (DerivationH' Γ [p]) → (DerivationH' Γ [□p])
  | verum (Γ) : DerivationH' Γ [⊤]
  | K (Γ) (p q) : DerivationH' Γ [□(p ⟶ q) ⟶ □p ⟶ □q]
  | T (Γ) (p) : DerivationH' Γ [□p ⟶ p]
  | A4 (Γ) (p) : DerivationH' Γ [□p ⟶ □□p]
  | Dot3 (Γ) (p) : DerivationH' Γ [□(□p ⟶ □q) ⋎ □(□q ⟶ □p)]

instance : TwoSided (Formula α) := ⟨LogicS4Dot3.DerivationH'⟩

def DerivationH (Γ : List (Formula α)) (p : Formula α) := DerivationH' Γ [p]

infixl:45 " ⊢ᴴ(𝗦𝟰.𝟯) " => DerivationH

abbrev ProofH (p : Formula α) := ∅ ⊢ᴴ(𝗦𝟰.𝟯) p

prefix:45 "⊢ᴴ(𝗦𝟰.𝟯) " => ProofH

/-
instance : LogicS4Dot3 (Formula α) where
  necessitation := LogicS4Dot3.DerivationH'.necessitation
  K := LogicS4Dot3.DerivationH'.K _ _ _
  T := LogicS4Dot3.DerivationH'.T _ _
  A4 := LogicS4Dot3.DerivationH'.A4 _ _
  Dot3 := LogicS4Dot3.DerivationH'.Dot3 _ _
-/

end LogicS4Dot3


namespace LogicS4Grz

variable {α : Type u}

inductive DerivationH' : List (Formula α) → List (Formula α) → Type _
  | modus_ponens {Γ p q} : (DerivationH' Γ [p ⟶ q]) → (DerivationH' Γ [p]) → (DerivationH' Γ [q])
  | necessitation {Γ p} : (DerivationH' Γ [p]) → (DerivationH' Γ [□p])
  | verum (Γ) : DerivationH' Γ [⊤]
  | K (Γ) (p q) : DerivationH' Γ [□(p ⟶ q) ⟶ □p ⟶ □q]
  | T (Γ) (p) : DerivationH' Γ [□p ⟶ p]
  | A4 (Γ) (p) : DerivationH' Γ [□p ⟶ □□p]
  | Grz (Γ) (p) : DerivationH' Γ [□(□(p ⟶ □p) ⟶ p) ⟶ p]

instance : TwoSided (Formula α) := ⟨LogicS4Grz.DerivationH'⟩

def DerivationH (Γ : List (Formula α)) (p : Formula α) := DerivationH' Γ [p]

infixl:45 " ⊢ᴴ(𝗦𝟰𝗚𝗿𝘇) " => DerivationH

abbrev ProofH (p : Formula α) := ∅ ⊢ᴴ(𝗦𝟰𝗚𝗿𝘇) p

prefix:45 "⊢ᴴ(𝗦𝟰𝗚𝗿𝘇) " => ProofH

/-
instance : LogicS4Grz (Formula α) where
  necessitation := LogicS4Grz.DerivationH'.necessitation
  K := LogicS4Grz.DerivationH'.K _ _ _
  T := LogicS4Grz.DerivationH'.T _ _
  A4 := LogicS4Grz.DerivationH'.A4 _ _
  Grz := LogicS4Grz.DerivationH'.Grz _ _
-/

end LogicS4Grz

end Hilbert

end Modal

end LO
