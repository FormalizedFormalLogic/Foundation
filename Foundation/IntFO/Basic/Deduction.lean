import Foundation.IntFO.Basic.Rew

namespace LO.FirstOrder

abbrev Sequentᵢ (L : Language) := List (SyntacticFormulaᵢ L)

open Semiformulaᵢ

variable {L : Language} {T : Theory L}

structure Hilbertᵢ (L : Language) where
  axiomSet : Set (SyntacticFormulaᵢ L)
  rewrite_closed {φ : SyntacticFormulaᵢ L} : φ ∈ axiomSet → ∀ f : ℕ → SyntacticTerm L, Rew.rewrite f ▹ φ ∈ axiomSet

instance : SetLike (Hilbertᵢ L) (SyntacticFormulaᵢ L) where
  coe := Hilbertᵢ.axiomSet
  coe_injective' := by rintro ⟨T, _⟩ ⟨U, _⟩; simp

namespace Hilbertᵢ

def Minimal : Hilbertᵢ L := ⟨∅, by simp⟩

notation "𝐌𝐢𝐧¹" => Minimal

def Intuitionistic : Hilbertᵢ L := ⟨{⊥ ➝ φ | φ}, by rintro _ ⟨φ, rfl⟩ f; exact ⟨Rew.rewrite f ▹ φ, by simp⟩⟩

notation "𝐈𝐧𝐭¹" => Intuitionistic

def Classical : Hilbertᵢ L := ⟨{⊥ ➝ φ | φ} ∪ {φ ⋎ ∼φ | φ}, by
  rintro _ (⟨φ, rfl⟩ | ⟨φ, rfl⟩) f
  · exact Or.inl ⟨Rew.rewrite f ▹ φ, by simp⟩
  · exact Or.inr ⟨Rew.rewrite f ▹ φ, by simp⟩⟩

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

open System.FiniteContext Rewriting LawfulSyntacticRewriting

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

variable {Λ}

protected def cast {φ ψ} (b : Λ ⊢ φ) (e : φ = ψ) : Λ ⊢ ψ := e ▸ b

def depth {φ} : Λ ⊢ φ → ℕ
  | mdp b d => max (depth b) (depth d) + 1
  | gen b   => depth b + 1
  | _       => 0

scoped notation "‖" d "‖" => depth d

@[simp] lemma depth_eaxm (h : φ ∈ Λ) : ‖eaxm h‖ = 0 := rfl
@[simp] lemma depth_mdp (b : Λ ⊢ φ ➝ ψ) (d : Λ ⊢ φ) : ‖mdp b d‖ = max ‖b‖ ‖d‖ + 1 := rfl
@[simp] lemma depth_gen (b : Λ ⊢ Rewriting.free φ) : ‖gen b‖ = ‖b‖ + 1 := rfl
@[simp] lemma depth_verum : ‖(verum : Λ ⊢ ⊤)‖ = 0 := rfl
@[simp] lemma depth_imply₁ (φ ψ) : ‖imply₁ (Λ := Λ) φ ψ‖ = 0 := rfl
@[simp] lemma depth_imply₂ (φ ψ χ) : ‖imply₂ (Λ := Λ) φ ψ χ‖ = 0 := rfl
@[simp] lemma depth_and₁ (φ ψ) : ‖and₁ (Λ := Λ) φ ψ‖ = 0 := rfl
@[simp] lemma depth_and₂ (φ ψ) : ‖and₂ (Λ := Λ) φ ψ‖ = 0 := rfl
@[simp] lemma depth_and₃ (φ ψ) : ‖and₃ (Λ := Λ) φ ψ‖ = 0 := rfl
@[simp] lemma depth_or₁ (φ ψ) : ‖or₁ (Λ := Λ) φ ψ‖ = 0 := rfl
@[simp] lemma depth_or₂ (φ ψ) : ‖or₂ (Λ := Λ) φ ψ‖ = 0 := rfl
@[simp] lemma depth_or₃ (φ ψ χ) : ‖or₃ (Λ := Λ) φ ψ χ‖ = 0 := rfl
@[simp] lemma depth_all₁ (φ t) : ‖all₁ (Λ := Λ) φ t‖ = 0 := rfl
@[simp] lemma depth_all₂ (φ ψ) : ‖all₂ (Λ := Λ) φ ψ‖ = 0 := rfl
@[simp] lemma depth_ex₁ (t φ) : ‖ex₁ (Λ := Λ) t φ‖ = 0 := rfl
@[simp] lemma depth_ex₂ (φ ψ) : ‖ex₂ (Λ := Λ) φ ψ‖ = 0 := rfl

@[simp] lemma depth_cast (b : Λ ⊢ φ) (e : φ = ψ) : ‖HilbertProofᵢ.cast b e‖ = ‖b‖ := by rcases e; rfl

@[simp] lemma depth_mdp' (b : Λ ⊢ φ ➝ ψ) (d : Λ ⊢ φ) : ‖b ⨀ d‖ = max ‖b‖ ‖d‖ + 1 := rfl

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

set_option diagnostics true in
set_option profiler true in
def dneOfNegative [L.DecidableEq] : {φ : SyntacticFormulaᵢ L} → φ.IsNegative → Λ ⊢ ∼∼φ ➝ φ
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

def ofDNOfNegative [L.DecidableEq] {φ : SyntacticFormulaᵢ L} {Γ} (b : Γ ⊢[Λ] ∼∼φ) (h : φ.IsNegative) : Γ ⊢[Λ] φ :=
  System.impTrans'' (toDef b) (dneOfNegative h)

def dnOfNegative [L.DecidableEq] {φ : SyntacticFormulaᵢ L} (h : φ.IsNegative) : Λ ⊢ ∼∼φ ⭤ φ :=
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

def iffnegOfNegIff [L.DecidableEq] {φ ψ : SyntacticFormulaᵢ L} (h : φ.IsNegative) (b : Λ ⊢ ∼φ ⭤ ψ) : Λ ⊢ φ ⭤ ∼ψ :=
  System.iffTrans'' (System.iffComm' <| dnOfNegative h) (System.negReplaceIff' b)

def rewrite (f : ℕ → SyntacticTerm L) : Λ ⊢ φ → Λ ⊢ Rew.rewrite f ▹ φ
  | mdp b d        => rewrite f b ⨀ rewrite f d
  | gen (φ := φ) b =>
    let d : Λ ⊢ free ((Rew.rewrite f).q ▹ φ) :=
      HilbertProofᵢ.cast (rewrite (&0 :>ₙ fun x ↦ Rew.shift (f x)) b)
        (by simp [Rew.q_rewrite, Function.comp_def, free_rewrite_eq])
    gen d
  | eaxm h         => eaxm (Λ.rewrite_closed h f)
  | verum          => verum
  | imply₁ _ _     => imply₁ _ _
  | imply₂ _ _ _   => imply₂ _ _ _
  | and₁ _ _       => and₁ _ _
  | and₂ _ _       => and₂ _ _
  | and₃ _ _       => and₃ _ _
  | or₁ _ _        => or₁ _ _
  | or₂ _ _        => or₂ _ _
  | or₃ _ _ _      => or₃ _ _ _
  | all₁ φ t       => HilbertProofᵢ.cast
    (all₁ (Rew.rewrite (⇑Rew.bShift ∘ f) ▹ φ) (Rew.rewrite f t))
    (by simp [Rew.q_rewrite, rewrite_subst_eq])
  | all₂ φ ψ       => HilbertProofᵢ.cast
    (all₂ (Rew.rewrite f ▹ φ) (Rew.rewrite (⇑Rew.bShift ∘ f) ▹ ψ))
    (by simp [Rew.q_rewrite, rewrite_substs_nil])
  | ex₁ t φ        => HilbertProofᵢ.cast
    (ex₁ (Rew.rewrite f t) (Rew.rewrite (⇑Rew.bShift ∘ f) ▹ φ))
    (by simp [Rew.q_rewrite, rewrite_subst_eq])
  | ex₂ φ ψ        => HilbertProofᵢ.cast
    (ex₂ (Rew.rewrite (⇑Rew.bShift ∘ f) ▹ φ) (Rew.rewrite f ▹ ψ))
    (by simp [Rew.q_rewrite, rewrite_substs_nil])

@[simp] lemma depth_rewrite (f : ℕ → SyntacticTerm L) (b : Λ ⊢ φ) : ‖rewrite f b‖ = ‖b‖ := by
  induction b generalizing f <;> simp [rewrite, *]

end HilbertProofᵢ

end LO.FirstOrder
