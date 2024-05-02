import Logic.Logic.HilbertStyle
import Logic.Logic.Context
import Logic.Modal.Normal.LogicSymbol
import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Axioms

namespace LO.System

open LO.Modal.Normal

variable {S F : Type*} [LogicalConnective F] [StandardModalLogicalConnective F] [System F S]
variable (𝓢 : S)

class Necessitation where
  nec {p q : F} : 𝓢 ⊢ p → 𝓢 ⊢ □p

class HasAxiomK where
  K (p q : F) : 𝓢 ⊢ axiomK p q

class HasAxiomT where
  T (p : F) : 𝓢 ⊢ axiomT p

class HasAxiomD where
  D (p : F) : 𝓢 ⊢ axiomD p

class HasAxiomB where
  B (p : F) : 𝓢 ⊢ axiomB p

class HasAxiomFour where
  Four (p : F) : 𝓢 ⊢ axiomFour p

class HasAxiomFive where
  Five (p : F) : 𝓢 ⊢ axiomFive p

class HasAxiomL where
  L (p : F) : 𝓢 ⊢ axiomL p

class HasAxiomDot2 where
  Dot2 (p : F) : 𝓢 ⊢ axiomDot2 p

class HasAxiomDot3 where
  Dot3 (p q : F) : 𝓢 ⊢ axiomDot3 p q

class HasAxiomGrz where
  Grz (p : F) : 𝓢 ⊢ axiomGrz p

class K extends Classical 𝓢, Necessitation 𝓢, HasAxiomK 𝓢

class KT extends K 𝓢, HasAxiomT 𝓢

class KD extends K 𝓢, HasAxiomD 𝓢

class K4 extends K 𝓢, HasAxiomFour 𝓢

class S4 extends K 𝓢, HasAxiomT 𝓢, HasAxiomFour 𝓢

class S5 extends K 𝓢, HasAxiomT 𝓢, HasAxiomFive 𝓢

class S4Dot2 extends S4 𝓢, HasAxiomDot2 𝓢

class S4Dot3 extends S4 𝓢, HasAxiomDot3 𝓢

class S4Grz extends S4 𝓢, HasAxiomGrz 𝓢

class GL extends K 𝓢, HasAxiomL 𝓢

end LO.System

namespace LO.Modal.Normal

variable {α : Type*} [DecidableEq α]

inductive Deduction (Λ : AxiomSet α) : (Formula α) → Type _
  | maxm {p}     : p ∈ Λ → Deduction Λ p
  | mdp {p q}    : Deduction Λ (p ⟶ q) → Deduction Λ p → Deduction Λ q
  | nec {p}      : Deduction Λ p → Deduction Λ (□p)
  | verum        : Deduction Λ ⊤
  | imply₁ p q   : Deduction Λ (p ⟶ q ⟶ p)
  | imply₂ p q r : Deduction Λ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  | conj₁ p q    : Deduction Λ (p ⋏ q ⟶ p)
  | conj₂ p q    : Deduction Λ (p ⋏ q ⟶ q)
  | conj₃ p q    : Deduction Λ (p ⟶ q ⟶ p ⋏ q)
  | disj₁ p q    : Deduction Λ (p ⟶ p ⋎ q)
  | disj₂ p q    : Deduction Λ (q ⟶ p ⋎ q)
  | disj₃ p q r  : Deduction Λ ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r))
  | dne p        : Deduction Λ (~~p ⟶ p)

instance : System (Formula α) (AxiomSet α) := ⟨Deduction⟩

open Deduction

instance : System.Classical (Λ : AxiomSet α) where
  mdp := mdp
  verum := verum
  imply₁ := imply₁
  imply₂ := imply₂
  conj₁ := conj₁
  conj₂ := conj₂
  conj₃ := conj₃
  disj₁ := disj₁
  disj₂ := disj₂
  disj₃ := disj₃
  dne := dne

instance : System.Necessitation (Λ : AxiomSet α) where
  nec := nec

instance (hK : 𝐊 ⊆ Λ := by simp) : System.K (Λ : AxiomSet α) where
  K _ _ := maxm $ Set.mem_of_subset_of_mem hK (by simp);

end LO.Modal.Normal


namespace LO.System

variable {S : Type*}
variable [LogicalConnective F]
variable [System F S]

structure Derivation (𝓢 : S) (T : Set F) (p : F) where
  ctx : List F
  subset : ∀ p ∈ ctx, p ∈ T
  derivation : System.Context.Prf 𝓢 ctx p

notation:45 T:80 " ⊢[" 𝓢 "] " p:80 => Derivation 𝓢 T p

section

variable (𝓢 : S) (T : Set F) (p : F)

def Derivable := Nonempty (T ⊢[𝓢] p)

abbrev Underivable := ¬Derivable 𝓢 T p

notation:45 T:80 " ⊢[" 𝓢 "]! " p:80 => Derivable 𝓢 T p

notation:45 T:80 " ⊬[" 𝓢 "]! " p:80 => Underivable 𝓢 T p

end

end LO.System


namespace LO.Modal.Normal

structure Derivation (Λ : AxiomSet α) (T : Theory α) (p : Formula α) where
  context : List (Formula α)
  subset : ∀ p ∈ context, p ∈ T
  derivation : System.Context.Prf Λ context p

instance (Λ : AxiomSet α) : System (Formula α) (Theory α) := ⟨(· ⊢[Λ] ·)⟩

end LO.Modal.Normal
