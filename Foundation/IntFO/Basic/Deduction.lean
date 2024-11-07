import Foundation.IntFO.Basic.Rew

namespace LO.FirstOrder

abbrev Sequentᵢ (L : Language) := List (SyntacticFormulaᵢ L)

open Semiformulaᵢ

variable {L : Language} {T : Theory L}

structure Hilbertᵢ (L : Language) where
  axiomSet : Set (SyntacticFormulaᵢ L)
  shift_closed {φ : SyntacticFormulaᵢ L} : φ ∈ axiomSet → Rewriting.shift φ ∈ axiomSet

instance : SetLike (Hilbertᵢ L) (SyntacticFormulaᵢ L) where
  coe := Hilbertᵢ.axiomSet
  coe_injective' := by rintro ⟨T, _⟩ ⟨U, _⟩; simp

namespace Hilbertᵢ

def Minimal : Hilbertᵢ L := ⟨∅, by simp⟩

notation "𝐌𝐢𝐧¹" => Minimal

def Intuitionistic : Hilbertᵢ L := ⟨{⊥ ➝ φ | φ}, by rintro _ ⟨φ, rfl⟩; exact ⟨Rewriting.shift φ, by simp⟩⟩

notation "𝐈𝐧𝐭¹" => Intuitionistic

def Classical : Hilbertᵢ L := ⟨{⊥ ➝ φ | φ} ∪ {φ ⋎ ∼φ | φ}, by
  rintro _ (⟨φ, rfl⟩ | ⟨φ, rfl⟩)
  · exact Or.inl ⟨Rewriting.shift φ, by simp⟩
  · exact Or.inr ⟨Rewriting.shift φ, by simp⟩⟩

notation "𝐂𝐥¹" => Classical

lemma minimal_le (Λ : Hilbertᵢ L) : (Minimal : Hilbertᵢ L) ≤ Λ := by rintro _ ⟨⟩

lemma intuitionistic_le_classical : (Intuitionistic : Hilbertᵢ L) ≤ Classical := by rintro _ ⟨φ, rfl⟩; exact .inl ⟨φ, rfl⟩

end Hilbertᵢ

inductive HilbertProofᵢ (Λ : Hilbertᵢ L) : SyntacticFormulaᵢ L → Type _
  | eaxm {φ}     : φ ∈ Λ → HilbertProofᵢ Λ φ
  | mdp {φ ψ}    : HilbertProofᵢ Λ (φ ➝ ψ) → HilbertProofᵢ Λ φ → HilbertProofᵢ Λ ψ
  | gen {φ}      : HilbertProofᵢ Λ (Rewriting.free φ) → HilbertProofᵢ Λ (∀' φ)
  | verum        : HilbertProofᵢ Λ ⊤
  | imply₁ φ ψ   : HilbertProofᵢ Λ <| φ ➝ ψ ➝ φ
  | imply₂ φ ψ χ : HilbertProofᵢ Λ <| (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ
  | and₁ φ ψ     : HilbertProofᵢ Λ <| φ ⋏ ψ ➝ φ
  | and₂ φ ψ     : HilbertProofᵢ Λ <| φ ⋏ ψ ➝ ψ
  | and₃ φ ψ     : HilbertProofᵢ Λ <| φ ➝ ψ ➝ φ ⋏ ψ
  | or₁ φ ψ      : HilbertProofᵢ Λ <| φ ➝ φ ⋎ ψ
  | or₂ φ ψ      : HilbertProofᵢ Λ <| ψ ➝ φ ⋎ ψ
  | or₃ φ ψ χ    : HilbertProofᵢ Λ <| (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)
  | all₁ φ t     : HilbertProofᵢ Λ <| ∀' φ ➝ φ/[t]
  | all₂ φ ψ     : HilbertProofᵢ Λ <| ∀' (φ/[] ➝ ψ) ➝ φ ➝ ∀' ψ
  | ex₁ t φ      : HilbertProofᵢ Λ <| φ/[t] ➝ ∃' φ
  | ex₂ φ ψ      : HilbertProofᵢ Λ <| ∀' (φ ➝ ψ/[]) ➝ ∃' φ ➝ ψ

instance : System (SyntacticFormulaᵢ L) (Hilbertᵢ L) := ⟨HilbertProofᵢ⟩

namespace HilbertProofᵢ

open System.FiniteContext Rewriting LawfulRewriting

variable (Λ : Hilbertᵢ L)

instance : System.ModusPonens Λ := ⟨mdp⟩

instance : System.HasAxiomAndInst Λ := ⟨and₃⟩

instance : System.HasAxiomImply₁ Λ := ⟨imply₁⟩

instance : System.HasAxiomImply₂ Λ := ⟨imply₂⟩

instance : System.Minimal Λ where
  mdp := mdp
  verum := verum
  imply₁ := imply₁
  imply₂ := imply₂
  and₁ := and₁
  and₂ := and₂
  and₃ := and₃
  or₁ := or₁
  or₂ := or₂
  or₃ := or₃
  neg_equiv _ := System.iffId _

variable {Λ} [L.DecidableEq]

def specialize {φ} (b : Λ ⊢ ∀' φ) (t) : Λ ⊢ φ/[t] := all₁ φ t ⨀ b

def implyAll {φ ψ} (b : Λ ⊢ shift φ ➝ free ψ) : Λ ⊢ φ ➝ ∀' ψ :=
  have : Λ ⊢ ∀' (φ/[] ➝ ψ) := gen <| by simpa using b
  all₂ φ ψ ⨀ this

def genOverFiniteContext {Γ φ} (b : Γ⁺ ⊢[Λ] free φ) : Γ ⊢[Λ] ∀' φ :=
  ofDef <| implyAll <| by simpa [shift_conj₂] using toDef b

def specializeOverContext {Γ φ} (b : Γ ⊢[Λ] ∀' φ) (t) : Γ ⊢[Λ] φ/[t] :=
  ofDef <| System.impTrans'' (toDef b) (all₁ φ t)

def allImplyAllOfAllImply (φ ψ) : Λ ⊢ ∀' (φ ➝ ψ) ➝ ∀' φ ➝ ∀' ψ := by
  apply deduct'
  apply deduct
  apply genOverFiniteContext
  have b₁ : [∀' shift φ, ∀' (shift φ ➝ shift ψ)] ⊢[Λ] free φ ➝ free ψ :=
    System.cast (by simp) (specializeOverContext (nthAxm 1) &0)
  have b₂ : [∀' shift φ, ∀' (shift φ ➝ shift ψ)] ⊢[Λ] free φ :=
    System.cast (by simp) (specializeOverContext (nthAxm 0) &0)
  have : [∀' φ, ∀' (φ ➝ ψ)]⁺ ⊢[Λ] free ψ := cast (by simp) (b₁ ⨀ b₂)
  exact this

def allIffAllOfIff {φ ψ} (b : Λ ⊢ free φ ⭤ free ψ) : Λ ⊢ ∀' φ ⭤ ∀' ψ := System.andIntro
  (allImplyAllOfAllImply φ ψ ⨀ gen (System.cast (by simp) (System.andLeft b)))
  (allImplyAllOfAllImply ψ φ ⨀ gen (System.cast (by simp) (System.andRight b)))

set_option profiler true in
def dneOfNegative : {φ : SyntacticFormulaᵢ L} → φ.IsNegative → Λ ⊢ ∼∼φ ➝ φ
  | ⊥,     _ => System.falsumDNE
  | φ ⋏ ψ, h =>
    have ihφ : Λ ⊢ ∼∼φ ➝ φ := dneOfNegative (by simp [by simpa using h])
    have ihψ : Λ ⊢ ∼∼ψ ➝ ψ := dneOfNegative (by simp [by simpa using h])
    have : Λ ⊢ ∼φ ➝ ∼(φ ⋏ ψ) := System.contra₀' System.and₁
    have dφ : [∼∼(φ ⋏ ψ)] ⊢[Λ] φ := of ihφ ⨀ (deduct <| byAxm₁ ⨀ (of this ⨀ byAxm₀))
    have : Λ ⊢ ∼ψ ➝ ∼(φ ⋏ ψ) := System.contra₀' System.and₂
    have dψ : [∼∼(φ ⋏ ψ)] ⊢[Λ] ψ := of ihψ ⨀ (deduct <| byAxm₁ ⨀ (of this ⨀ byAxm₀))
    deduct' (System.andIntro dφ dψ)
  | φ ➝ ψ, h =>
    let ihψ : Λ ⊢ ∼∼ψ ➝ ψ := dneOfNegative (by simp [by simpa using h])
    have : [∼ψ, φ, ∼∼(φ ➝ ψ)] ⊢[Λ] ∼(φ ➝ ψ) := deduct <| byAxm₁ ⨀ (byAxm₀ ⨀ byAxm₂)
    have : [∼ψ, φ, ∼∼(φ ➝ ψ)] ⊢[Λ] ⊥ := byAxm₂ ⨀ this
    have : [φ, ∼∼(φ ➝ ψ)] ⊢[Λ] ψ := (of ihψ) ⨀ (deduct this)
    deduct' (deduct this)
  | ∀' φ,  h =>
    have ihφ : Λ ⊢ ∼∼(free φ) ➝ free φ := dneOfNegative (by simp [by simpa using h])
    have : [∀' shift φ, ∼(free φ), ∼∼(∀' shift φ)] ⊢[Λ] ⊥ :=
      have : [∀' shift φ, ∼(free φ), ∼∼(∀' shift φ)] ⊢[Λ] ∀' shift φ := byAxm₀
      byAxm₁ ⨀ System.cast (by simp) (specializeOverContext this &0)
    have : [∼∼(∀' shift φ)] ⊢[Λ] free φ := of ihφ ⨀ deduct (byAxm₁ ⨀ deduct this)
    implyAll (System.cast (by simp) (deduct' this))
  termination_by φ _ => φ.complexity

def ofDNOfNegative {φ : SyntacticFormulaᵢ L} {Γ} (b : Γ ⊢[Λ] ∼∼φ) (h : φ.IsNegative) : Γ ⊢[Λ] φ :=
  System.impTrans'' (toDef b) (dneOfNegative h)

def dnOfNegative {φ : SyntacticFormulaᵢ L} (h : φ.IsNegative) : Λ ⊢ ∼∼φ ⭤ φ :=
  System.andIntro (dneOfNegative h) System.dni

def efqOfNegative : {φ : SyntacticFormulaᵢ L} → φ.IsNegative → Λ ⊢ ⊥ ➝ φ
  | ⊥,     _ => System.impId ⊥
  | φ ⋏ ψ, h =>
    have ihφ : Λ ⊢ ⊥ ➝ φ := efqOfNegative (by simp [by simpa using h])
    have ihψ : Λ ⊢ ⊥ ➝ ψ := efqOfNegative (by simp [by simpa using h])
    System.implyAnd ihφ ihψ
  | φ ➝ ψ, h =>
    have ihψ : Λ ⊢ ⊥ ➝ ψ := efqOfNegative (by simp [by simpa using h])
    System.impTrans'' ihψ System.imply₁
  | ∀' φ,  h =>
    have ihφ : Λ ⊢ ⊥ ➝ free φ := efqOfNegative (by simp [by simpa using h])
    implyAll <| System.cast (by simp) ihφ
  termination_by φ _ => φ.complexity

def iffnegOfNegIff {φ ψ : SyntacticFormulaᵢ L} (h : φ.IsNegative) (b : Λ ⊢ ∼φ ⭤ ψ) : Λ ⊢ φ ⭤ ∼ψ :=
  System.iffTrans'' (System.iffComm' <| dnOfNegative h) (System.negReplaceIff' b)

end HilbertProofᵢ


end LO.FirstOrder
