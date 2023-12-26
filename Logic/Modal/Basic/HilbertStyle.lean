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

class LogicK extends Hilbert.Classical F, HasNecessitation F, HasAxiomK F

class HasAxiomT where
  T (Γ : List F) (p : F) : Γ ⊢ᴴ □p ⟶ p

class HasAxiomD where
  D (Γ : List F) (p : F) : Γ ⊢ᴴ □p ⟶ ◇p

class HasAxiomB where
  B (Γ : List F) (p q : F) : Γ ⊢ᴴ p ⟶ □◇p

class HasAxiom4 where
  A4 (Γ : List F) (p : F) : Γ ⊢ᴴ □p ⟶ □□p

class LogicS4 extends LogicK F, HasAxiomT F, HasAxiom4 F

class LogicS5 extends LogicS4 F, HasAxiomB F

class HasAxiom5 where
  A5 (Γ : List F) (p q : F) : Γ ⊢ᴴ ◇p ⟶ □◇p

class HasAxiomL where
  L (Γ : List F) (p : F) : Γ ⊢ᴴ □(□p ⟶ p) ⟶ □p

class LogicGL extends LogicK F, HasAxiomL F

class HasAxiomDot2 where
  Dot2 (Γ : List F) (p : F) : Γ ⊢ᴴ ◇□p ⟶ □◇p

class LogicS4Dot2 extends LogicS4 F, HasAxiomDot2 F

class HasAxiomDot3 where
  Dot3 (Γ : List F) (p : F) : Γ ⊢ᴴ □(□p ⟶ □q) ⋎ □(□q ⟶ □p)

class LogicS4Dot3 extends LogicS4 F, HasAxiomDot3 F

class HasAxiomGrz where
  Grz (Γ : List F) (p : F) : Γ ⊢ᴴ □(□(p ⟶ □p) ⟶ p) ⟶ p

class LogicS4Grz extends LogicS4 F, HasAxiomGrz F

end Axioms


namespace LogicK

variable {α : Type u}

inductive Derives' : List (Formula α) → List (Formula α) → Type _
  | axm (Γ p)            : p ∈ Γ → Derives' Γ [p]
  | modus_ponens {Γ p q} : Derives' Γ [p ⟶ q] → Derives' Γ [p] → Derives' Γ [q]
  | verum (Γ)            : Derives' Γ [⊤]
  | imply₁ (Γ) (p q)     : Derives' Γ [p ⟶ q ⟶ p]
  | imply₂ (Γ) (p q r)   : Derives' Γ [(p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r]
  | conj₁ (Γ) (p q)      : Derives' Γ [p ⋏ q ⟶ p]
  | conj₂ (Γ) (p q)      : Derives' Γ [p ⋏ q ⟶ q]
  | conj₃ (Γ) (p q)      : Derives' Γ [p ⟶ q ⟶ p ⋏ q]
  | disj₁ (Γ) (p q)      : Derives' Γ [p ⟶ p ⋎ q]
  | disj₂ (Γ) (p q)      : Derives' Γ [q ⟶ p ⋎ q]
  | disj₃ (Γ) (p q r)    : Derives' Γ [(p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)]
  | explode (Γ) (p)      : Derives' Γ [⊥ ⟶ p]
  | em (Γ) (p)           : Derives' Γ [p ⋎ ~p]
  | necessitation {Γ p}  : Derives' Γ [p] → Derives' Γ [□p]
  | K (Γ) (p q)          : Derives' Γ [□(p ⟶ q) ⟶ □p ⟶ □q]

instance : TwoSided (Formula α) := ⟨LogicK.Derives'⟩

def Derives (Γ : List (Formula α)) (p : Formula α) := LogicK.Derives' Γ [p]

infixl:45 " ⊢ᴴ(𝗞) " => Derives

abbrev Proves (p : Formula α) := ∅ ⊢ᴴ(𝗞) p

prefix:45 "⊢ᴴ(𝗞) " => Proves

instance : LogicK (Formula α) where
  necessitation := LogicK.Derives'.necessitation
  K := LogicK.Derives'.K
  axm := LogicK.Derives'.axm
  modus_ponens := LogicK.Derives'.modus_ponens
  verum := LogicK.Derives'.verum
  imply₁ := LogicK.Derives'.imply₁
  imply₂ := LogicK.Derives'.imply₂
  conj₁ := LogicK.Derives'.conj₁
  conj₂ := LogicK.Derives'.conj₂
  conj₃ := LogicK.Derives'.conj₃
  disj₁ := LogicK.Derives'.disj₁
  disj₂ := LogicK.Derives'.disj₂
  disj₃ := LogicK.Derives'.disj₃
  explode := LogicK.Derives'.explode
  em := LogicK.Derives'.em

def Derives'.length {Γ Δ : List (Formula α)} : Derives' Γ Δ → ℕ
  | axm _ _ _ => 0
  | modus_ponens d₁ d₂ => d₁.length + d₂.length + 1
  | necessitation d₁ => d₁.length + 1
  | verum _ => 0
  | imply₁ _ _ _ => 0
  | imply₂ _ _ _ _ => 0
  | conj₁ _ _ _ => 0
  | conj₂ _ _ _ => 0
  | conj₃ _ _ _ => 0
  | disj₁ _ _ _ => 0
  | disj₂ _ _ _ => 0
  | disj₃ _ _ _ _ => 0
  | explode _ _ => 0
  | em _ _ => 0
  | K _ _ _ => 0

def Derives.length {Γ : List (Formula α)} {p : Formula α} : Γ ⊢ᴴ(𝗞) p → ℕ := Derives'.length

def Proves.length {p : Formula α} : ⊢ᴴ(𝗞) p → ℕ := Derives.length

lemma Derives.length_lt_imp1 (d₁ : Derives Γ (p ⟶ q)) (d₂ : Derives Γ p) : d₁.length > d₂.length := by sorry;

lemma Derives.length_lt_imp2 (d₁ : Derives Γ (p ⟶ q)) (d₂ : Derives Γ q) : d₁.length > d₂.length := by sorry;

end LogicK

namespace LogicS4

variable {α : Type u}

inductive Derives' : List (Formula α) → List (Formula α) → Type _
  | modus_ponens {Γ p q} : (Derives' Γ [p ⟶ q]) → (Derives' Γ [p]) → (Derives' Γ [q])
  | verum (Γ) : Derives' Γ [⊤]
  | imply₁ (Γ) (p q) : Derives' Γ [p ⟶ q ⟶ p]
  | imply₂ (Γ) (p q r) : Derives' Γ [(p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r]
  | conj₁ (Γ) (p q) : Derives' Γ [p ⋏ q ⟶ p]
  | conj₂ (Γ) (p q) : Derives' Γ [p ⋏ q ⟶ q]
  | conj₃ (Γ) (p q) : Derives' Γ [p ⟶ q ⟶ p ⋏ q]
  | disj₁ (Γ) (p q) : Derives' Γ [p ⟶ p ⋎ q]
  | disj₂ (Γ) (p q) : Derives' Γ [q ⟶ p ⋎ q]
  | disj₃ (Γ) (p q r) : Derives' Γ [(p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)]
  | explode (Γ) (p) : Derives' Γ [⊥ ⟶ p]
  | em (Γ) (p) : Derives' Γ [p ⋎ ~p]
  | necessitation {Γ p} : (Derives' Γ [p]) → (Derives' Γ [□p])
  | K (Γ) (p q) : Derives' Γ [□(p ⟶ q) ⟶ □p ⟶ □q]
  | T (Γ) (p) : Derives' Γ [□p ⟶ p]
  | A4 (Γ) (p) : Derives' Γ [□p ⟶ □□p]

instance : TwoSided (Formula α) := ⟨LogicS4.Derives'⟩

def Derives (Γ : List (Formula α)) (p : Formula α) := Derives' Γ [p]

infixl:45 " ⊢ᴴ(𝗦𝟰) " => Derives

abbrev Proves (p : Formula α) := ∅ ⊢ᴴ(𝗦𝟰) p

prefix:45 "⊢ᴴ(𝗦𝟰) " => Proves


end LogicS4


namespace LogicS5

variable {α : Type u}

inductive Derives' : List (Formula α) → List (Formula α) → Type _
  | modus_ponens {Γ p q} : (Derives' Γ [p ⟶ q]) → (Derives' Γ [p]) → (Derives' Γ [q])
  | necessitation {Γ p} : (Derives' Γ [p]) → (Derives' Γ [□p])
  | verum (Γ) : Derives' Γ [⊤]
  | K (Γ) (p q) : Derives' Γ [□(p ⟶ q) ⟶ □p ⟶ □q]
  | T (Γ) (p) : Derives' Γ [□p ⟶ p]
  | B (Γ) (p) : Derives' Γ [p ⟶ □◇p]
  | A4 (Γ) (p) : Derives' Γ [□p ⟶ □□p]

instance : TwoSided (Formula α) := ⟨LogicS5.Derives'⟩

def Derives (Γ : List (Formula α)) (p : Formula α) := Derives' Γ [p]

infixl:45 " ⊢ᴴ(𝗦𝟱) " => Derives

abbrev Proves (p : Formula α) := ∅ ⊢ᴴ(𝗦𝟱) p

prefix:45 "⊢ᴴ(𝗦𝟱) " => Proves


/-
instance : LogicS5 (Formula α) where
  necessitation := LogicS5.Derives'.necessitation
  K := LogicS5.Derives'.K _ _ _
  T := LogicS5.Derives'.T _ _
  B := LogicS5.Derives'.B _ _
  A4 := LogicS5.Derives'.A4 _ _
-/

end LogicS5


namespace LogicGL

variable {α : Type u}

inductive Derives' : List (Formula α) → List (Formula α) → Type _
  | modus_ponens {Γ p q} : (Derives' Γ [p ⟶ q]) → (Derives' Γ [p]) → (Derives' Γ [q])
  | necessitation {Γ p} : (Derives' Γ [p]) → (Derives' Γ [□p])
  | verum (Γ) : Derives' Γ [⊤]
  | K (Γ) (p q) : Derives' Γ [□(p ⟶ q) ⟶ □p ⟶ □q]
  | L (Γ) (p) : Derives' Γ [□(□p ⟶ p) ⟶ □p]

instance : TwoSided (Formula α) := ⟨LogicGL.Derives'⟩

def Derives (Γ : List (Formula α)) (p : Formula α) := Derives' Γ [p]

infixl:45 " ⊢ᴴ(𝗚𝗟) " => Derives

abbrev Proves (p : Formula α) := ∅ ⊢ᴴ(𝗚𝗟) p

prefix:45 "⊢ᴴ(𝗚𝗟) " => Proves


/-
instance : LogicGL (Formula α) where
  necessitation := LogicGL.Derives'.necessitation
  K := LogicGL.Derives'.K _ _ _
  L := LogicGL.Derives'.L _ _
-/

end LogicGL


namespace LogicS4Dot2

variable {α : Type u}

inductive Derives' : List (Formula α) → List (Formula α) → Type _
  | modus_ponens {Γ p q} : (Derives' Γ [p ⟶ q]) → (Derives' Γ [p]) → (Derives' Γ [q])
  | necessitation {Γ p} : (Derives' Γ [p]) → (Derives' Γ [□p])
  | verum (Γ) : Derives' Γ [⊤]
  | K (Γ) (p q) : Derives' Γ [□(p ⟶ q) ⟶ □p ⟶ □q]
  | T (Γ) (p) : Derives' Γ [□p ⟶ p]
  | B (Γ) (p) : Derives' Γ [p ⟶ □◇p]
  | A4 (Γ) (p) : Derives' Γ [□p ⟶ □□p]
  | Dot2 (Γ) (p) : Derives' Γ [◇□p ⟶ □◇p]

instance : TwoSided (Formula α) := ⟨LogicS4Dot2.Derives'⟩

def Derives (Γ : List (Formula α)) (p : Formula α) := Derives' Γ [p]

infixl:45 " ⊢ᴴ(𝗦𝟰.𝟮) " => Derives

abbrev Proves (p : Formula α) := ∅ ⊢ᴴ(𝗦𝟰.𝟮) p

prefix:45 "⊢ᴴ(𝗦𝟰.𝟮) " => Proves

/-
instance : LogicS4Dot2 (Formula α) where
  necessitation := LogicS4Dot2.Derives'.necessitation
  K := LogicS4Dot2.Derives'.K _ _ _
  T := LogicS4Dot2.Derives'.T _ _
  A4 := LogicS4Dot2.Derives'.A4 _ _
  Dot2 := LogicS4Dot2.Derives'.Dot2 _ _
-/

end LogicS4Dot2


namespace LogicS4Dot3

variable {α : Type u}

inductive Derives' : List (Formula α) → List (Formula α) → Type _
  | modus_ponens {Γ p q} : (Derives' Γ [p ⟶ q]) → (Derives' Γ [p]) → (Derives' Γ [q])
  | necessitation {Γ p} : (Derives' Γ [p]) → (Derives' Γ [□p])
  | verum (Γ) : Derives' Γ [⊤]
  | K (Γ) (p q) : Derives' Γ [□(p ⟶ q) ⟶ □p ⟶ □q]
  | T (Γ) (p) : Derives' Γ [□p ⟶ p]
  | A4 (Γ) (p) : Derives' Γ [□p ⟶ □□p]
  | Dot3 (Γ) (p) : Derives' Γ [□(□p ⟶ □q) ⋎ □(□q ⟶ □p)]

instance : TwoSided (Formula α) := ⟨LogicS4Dot3.Derives'⟩

def Derives (Γ : List (Formula α)) (p : Formula α) := Derives' Γ [p]

infixl:45 " ⊢ᴴ(𝗦𝟰.𝟯) " => Derives

abbrev Proves (p : Formula α) := ∅ ⊢ᴴ(𝗦𝟰.𝟯) p

prefix:45 "⊢ᴴ(𝗦𝟰.𝟯) " => Proves

/-
instance : LogicS4Dot3 (Formula α) where
  necessitation := LogicS4Dot3.Derives'.necessitation
  K := LogicS4Dot3.Derives'.K _ _ _
  T := LogicS4Dot3.Derives'.T _ _
  A4 := LogicS4Dot3.Derives'.A4 _ _
  Dot3 := LogicS4Dot3.Derives'.Dot3 _ _
-/

end LogicS4Dot3


namespace LogicS4Grz

variable {α : Type u}

inductive Derives' : List (Formula α) → List (Formula α) → Type _
  | modus_ponens {Γ p q} : (Derives' Γ [p ⟶ q]) → (Derives' Γ [p]) → (Derives' Γ [q])
  | necessitation {Γ p} : (Derives' Γ [p]) → (Derives' Γ [□p])
  | verum (Γ) : Derives' Γ [⊤]
  | K (Γ) (p q) : Derives' Γ [□(p ⟶ q) ⟶ □p ⟶ □q]
  | T (Γ) (p) : Derives' Γ [□p ⟶ p]
  | A4 (Γ) (p) : Derives' Γ [□p ⟶ □□p]
  | Grz (Γ) (p) : Derives' Γ [□(□(p ⟶ □p) ⟶ p) ⟶ p]

instance : TwoSided (Formula α) := ⟨LogicS4Grz.Derives'⟩

def Derives (Γ : List (Formula α)) (p : Formula α) := Derives' Γ [p]

infixl:45 " ⊢ᴴ(𝗦𝟰𝗚𝗿𝘇) " => Derives

abbrev Proves (p : Formula α) := ∅ ⊢ᴴ(𝗦𝟰𝗚𝗿𝘇) p

prefix:45 "⊢ᴴ(𝗦𝟰𝗚𝗿𝘇) " => Proves

/-
instance : LogicS4Grz (Formula α) where
  necessitation := LogicS4Grz.Derives'.necessitation
  K := LogicS4Grz.Derives'.K _ _ _
  T := LogicS4Grz.Derives'.T _ _
  A4 := LogicS4Grz.Derives'.A4 _ _
  Grz := LogicS4Grz.Derives'.Grz _ _
-/

end LogicS4Grz

end Hilbert

end Modal

end LO
