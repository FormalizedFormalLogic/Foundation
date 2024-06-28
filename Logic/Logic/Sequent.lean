import Logic.Logic.System

/-!
# Sequent calculus and variants

-/

namespace LO

class Sequent {F : outParam Type*} (L R : outParam Type*) [Collection F L] [Collection F R] (S : Type*) where
  Seq : S → L → R → Type*

notation:45 Δ:45 " ⟹[" 𝓢 "] " Γ:46 => Sequent.Seq 𝓢 Δ Γ

namespace Sequent

variable {F : Type*} {L R : Type*} [Collection F L] [Collection F R] {S : Type*} [Sequent L R S]

scoped infixr:60 " ∷ " => Cons.cons

abbrev SingleConseq (𝓢 : S) (Γ : L) (A : F) := Γ ⟹[𝓢] {A}

notation:45 Γ:45 " ⟹[" 𝓢 "]. " A:46 => SingleConseq 𝓢 Γ A

abbrev SingleAntecedent (𝓢 : S) (A : F) (Γ : R) := {A} ⟹[𝓢] Γ

notation:45 A:45 " .⟹[" 𝓢 "] " Γ:46 => SingleAntecedent 𝓢 A Γ

abbrev SingleAntecedentConseq (𝓢 : S) (A B : F) := {A} ⟹[𝓢] {B}

notation:45 A:45 " .⟹[" 𝓢 "]. " B:46 => SingleAntecedentConseq 𝓢 A B

class Closed (𝓢 : S) where
  closed {Γ Δ} (A : F) : A ∈ Γ → A ∈ Δ → Γ ⟹[𝓢] Δ

class IRefl (𝓢 : S) where
  irefl (A) : A .⟹[𝓢]. A

class ICut (𝓢 : S) where
  icut {Γ A Λ} : Γ ⟹[𝓢]. A → A .⟹[𝓢] Λ → Γ ⟹[𝓢] Λ

class Weakening (𝓢 : S) where
  wk {Γ₁ Γ₂ Δ₁ Δ₂} : Γ₁ ⊆ Γ₂ → Δ₁ ⊆ Δ₂ → Γ₁ ⟹[𝓢] Δ₁ → Γ₂ ⟹[𝓢] Δ₂

variable [LogicalConnective F] [Cons F L]

class LJ (𝓢 : S) extends IRefl 𝓢, Weakening 𝓢 where
  verum (Γ)            : Γ ⟹[𝓢]. ⊤
  falsum               : ⊥ .⟹[𝓢] ∅
  negLeft {Γ A}        : Γ ⟹[𝓢]. A → ~A ∷ Γ ⟹[𝓢] ∅
  negRight {Γ A}       : A ∷ Γ ⟹[𝓢]. ⊥ → Γ ⟹[𝓢]. ~A
  andLeft₁ {Γ A B}     : A ∷ Γ ⟹[𝓢]. C → A ⋏ B ∷ Γ ⟹[𝓢] Δ
  andLeft₂ {Γ A B}     : B ∷ Γ ⟹[𝓢]. C → A ⋏ B ∷ Γ ⟹[𝓢] Δ
  andRight {Γ A B}     : Γ ⟹[𝓢]. A → Γ ⟹[𝓢]. B → Γ ⟹[𝓢]. A ⋏ B
  orLeft {Γ A B}       : A ∷ Γ ⟹[𝓢]. C → B ∷ Γ ⟹[𝓢]. C → A ⋎ B ∷ Γ ⟹[𝓢]. C
  orRight₁ {Γ A B}     : Γ ⟹[𝓢]. A → Γ ⟹[𝓢]. A ⋎ B
  orRight₂ {Γ A B}     : Γ ⟹[𝓢]. B → Γ ⟹[𝓢]. A ⋎ B
  implyLeft {Γ A B C}  : Γ ⟹[𝓢]. A → B ∷ Γ ⟹[𝓢]. C → (A ⟶ B) ∷ Γ ⟹[𝓢]. C
  implyRight {Γ A B}   : A ∷ Γ ⟹[𝓢]. B → Γ ⟹[𝓢]. (A ⟶ B)

variable [Cons F R]

class LK (𝓢 : S) extends IRefl 𝓢, Weakening 𝓢 where
  verum (Γ Δ)          : Γ ⟹[𝓢] ⊤ ∷ Δ
  falsum (Γ Δ)         : ⊥ ∷ Γ ⟹[𝓢] Δ
  negLeft {A Γ Δ}      : Γ ⟹[𝓢] A ∷ Δ → ~A ∷ Γ ⟹[𝓢] Δ
  negRight {A Γ Δ}     : A ∷ Γ ⟹[𝓢] Δ → Γ ⟹[𝓢] ~A ∷ Δ
  andLeft {A B Γ Δ}    : A ∷ B ∷ Γ ⟹[𝓢] Δ → A ⋏ B ∷ Γ ⟹[𝓢] Δ
  andRight {A B Γ Δ}   : Γ ⟹[𝓢] A ∷ Δ → Γ ⟹[𝓢] B ∷ Δ → Γ ⟹[𝓢] A ⋏ B ∷ Δ
  orLeft {A B Γ Δ}     : A ∷ Γ ⟹[𝓢] Δ → B ∷ Γ ⟹[𝓢] Δ → A ⋎ B ∷ Γ ⟹[𝓢] Δ
  orRight {A B Γ Δ}    : Γ ⟹[𝓢] A ∷ B ∷ Δ → Γ ⟹[𝓢] A ⋎ B ∷ Δ
  implyLeft {A B Γ Δ}  : Γ ⟹[𝓢] A ∷ Δ → B ∷ Γ ⟹[𝓢] Δ → (A ⟶ B) ∷ Γ ⟹[𝓢] Δ
  implyRight {A B Γ Δ} : A ∷ Γ ⟹[𝓢] B ∷ Δ → Γ ⟹[𝓢] (A ⟶ B) ∷ Δ

end Sequent
