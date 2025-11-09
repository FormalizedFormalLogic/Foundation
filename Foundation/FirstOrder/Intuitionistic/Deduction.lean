import Foundation.FirstOrder.Intuitionistic.Rew

namespace LO.FirstOrder

abbrev Sequentᵢ (L : Language) := List (SyntacticFormulaᵢ L)

open Semiformulaᵢ

variable {L : Language.{u}} {T : Theory L}

structure Hilbertᵢ (L : Language) where
  axiomSet : Set (SyntacticFormulaᵢ L)
  rewrite_closed {φ : SyntacticFormulaᵢ L} : φ ∈ axiomSet → ∀ f : ℕ → SyntacticTerm L, Rew.rewrite f ▹ φ ∈ axiomSet

namespace Hilbertᵢ

instance : SetLike (Hilbertᵢ L) (SyntacticFormulaᵢ L) where
  coe := Hilbertᵢ.axiomSet
  coe_injective' := by rintro ⟨T, _⟩ ⟨U, _⟩; simp

@[simp] lemma mem_mk (s : Set (SyntacticFormulaᵢ L)) (h) : φ ∈ Hilbertᵢ.mk s h ↔ φ ∈ s := by rfl

def Minimal : Hilbertᵢ L := ⟨∅, by simp⟩

notation "𝗠𝗶𝗻¹" => Minimal

def Intuitionistic : Hilbertᵢ L := ⟨{Axioms.EFQ φ | φ}, by rintro _ ⟨φ, rfl⟩ f; exact ⟨Rew.rewrite f ▹ φ, by simp⟩⟩

notation "𝗜𝗻𝘁¹" => Intuitionistic

def Classical : Hilbertᵢ L := ⟨{⊥ ➝ φ | φ} ∪ {φ ⋎ ∼φ | φ}, by
  rintro _ (⟨φ, rfl⟩ | ⟨φ, rfl⟩) f
  · exact Or.inl ⟨Rew.rewrite f ▹ φ, by simp⟩
  · exact Or.inr ⟨Rew.rewrite f ▹ φ, by simp⟩⟩

notation "𝗖𝗹¹" => Classical

@[simp] lemma minimal_le (Λ : Hilbertᵢ L) : (Minimal : Hilbertᵢ L) ≤ Λ := by rintro _ ⟨⟩

@[simp] lemma intuitionistic_le_classical : (Intuitionistic : Hilbertᵢ L) ≤ Classical := by rintro _ ⟨φ, rfl⟩; exact .inl ⟨φ, rfl⟩

end Hilbertᵢ

inductive HilbertProofᵢ (Λ : Hilbertᵢ L) : SyntacticFormulaᵢ L → Type _
  | eaxm {φ}     : φ ∈ Λ → HilbertProofᵢ Λ φ
  | mdp {φ ψ}    : HilbertProofᵢ Λ (φ ➝ ψ) → HilbertProofᵢ Λ φ → HilbertProofᵢ Λ ψ
  | gen {φ}      : HilbertProofᵢ Λ (Rewriting.free φ) → HilbertProofᵢ Λ (∀' φ)
  | verum        : HilbertProofᵢ Λ ⊤
  | implyK φ ψ   : HilbertProofᵢ Λ <| φ ➝ ψ ➝ φ
  | implyS φ ψ χ : HilbertProofᵢ Λ <| (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ
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

instance : Entailment (Hilbertᵢ L) (SyntacticFormulaᵢ L) := ⟨HilbertProofᵢ⟩

namespace HilbertProofᵢ

open Entailment.FiniteContext Rewriting LawfulSyntacticRewriting

variable (Λ : Hilbertᵢ L)

instance : Entailment.ModusPonens Λ := ⟨mdp⟩

instance : Entailment.HasAxiomAndInst Λ := ⟨and₃ _ _⟩

instance : Entailment.HasAxiomImplyK Λ := ⟨implyK _ _⟩

instance : Entailment.HasAxiomImplyS Λ := ⟨implyS _ _ _⟩

instance : Entailment.Minimal Λ where
  mdp := mdp
  verum := verum
  implyK := implyK _ _
  implyS := implyS _ _ _
  and₁ := and₁ _ _
  and₂ := and₂ _ _
  and₃ := and₃ _ _
  or₁ := or₁ _ _
  or₂ := or₂ _ _
  or₃ := or₃ _ _ _
  negEquiv := Entailment.E_Id

variable {Λ}

instance : Entailment.Int (𝗜𝗻𝘁¹ : Hilbertᵢ L) where
  efq := eaxm <| by simp [Hilbertᵢ.Intuitionistic]

protected def cast {φ ψ} (b : Λ ⊢! φ) (e : φ = ψ) : Λ ⊢! ψ := e ▸ b

def depth {φ} : Λ ⊢! φ → ℕ
  | mdp b d => max (depth b) (depth d) + 1
  | gen b   => depth b + 1
  | _       => 0

scoped notation "‖" d "‖" => depth d

@[simp] lemma depth_eaxm (h : φ ∈ Λ) : ‖eaxm h‖ = 0 := rfl
@[simp] lemma depth_mdp (b : Λ ⊢! φ ➝ ψ) (d : Λ ⊢! φ) : ‖mdp b d‖ = max ‖b‖ ‖d‖ + 1 := rfl
@[simp] lemma depth_gen (b : Λ ⊢! Rewriting.free φ) : ‖gen b‖ = ‖b‖ + 1 := rfl
@[simp] lemma depth_verum : ‖(verum : Λ ⊢! ⊤)‖ = 0 := rfl
@[simp] lemma depth_implyK (φ ψ) : ‖implyK (Λ := Λ) φ ψ‖ = 0 := rfl
@[simp] lemma depth_implyS (φ ψ χ) : ‖implyS (Λ := Λ) φ ψ χ‖ = 0 := rfl
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

@[simp] lemma depth_cast (b : Λ ⊢! φ) (e : φ = ψ) : ‖HilbertProofᵢ.cast b e‖ = ‖b‖ := by rcases e; rfl

@[simp] lemma depth_mdp' (b : Λ ⊢! φ ➝ ψ) (d : Λ ⊢! φ) : ‖b ⨀ d‖ = max ‖b‖ ‖d‖ + 1 := rfl

def specialize {φ} (b : Λ ⊢! ∀' φ) (t) : Λ ⊢! φ/[t] := all₁ φ t ⨀ b

def implyAll {φ ψ} (b : Λ ⊢! shift φ ➝ free ψ) : Λ ⊢! φ ➝ ∀' ψ :=
  have : Λ ⊢! ∀' (φ/[] ➝ ψ) := gen <| by simpa using b
  all₂ φ ψ ⨀ this

def geNOverFiniteContext {Γ φ} (b : Γ⁺ ⊢[Λ]! free φ) : Γ ⊢[Λ]! ∀' φ :=
  ofDef <| implyAll <| by simpa [shift_conj₂] using toDef b

def specializeOverContext {Γ φ} (b : Γ ⊢[Λ]! ∀' φ) (t) : Γ ⊢[Λ]! φ/[t] :=
  ofDef <| Entailment.C_trans (toDef b) (all₁ φ t)

def allImplyAllOfAllImply (φ ψ) : Λ ⊢! ∀' (φ ➝ ψ) ➝ ∀' φ ➝ ∀' ψ := by
  apply deduct'
  apply deduct
  apply geNOverFiniteContext
  have b₁ : [∀' shift φ, ∀' (shift φ ➝ shift ψ)] ⊢[Λ]! free φ ➝ free ψ :=
    Entailment.cast (by simp) (specializeOverContext (nthAxm 1) &0)
  have b₂ : [∀' shift φ, ∀' (shift φ ➝ shift ψ)] ⊢[Λ]! free φ :=
    Entailment.cast (by simp) (specializeOverContext (nthAxm 0) &0)
  have : [∀' φ, ∀' (φ ➝ ψ)]⁺ ⊢[Λ]! free ψ := cast (by simp) (b₁ ⨀ b₂)
  exact this

def allIffAllOfIff {φ ψ} (b : Λ ⊢! free φ ⭤ free ψ) : Λ ⊢! ∀' φ ⭤ ∀' ψ := Entailment.K_intro
  (allImplyAllOfAllImply φ ψ ⨀ gen (Entailment.cast (by simp) (Entailment.K_left b)))
  (allImplyAllOfAllImply ψ φ ⨀ gen (Entailment.cast (by simp) (Entailment.K_right b)))

set_option diagnostics true in
set_option profiler true in
def dneOfNegative [L.DecidableEq] : {φ : SyntacticFormulaᵢ L} → φ.IsNegative → Λ ⊢! ∼∼φ ➝ φ
  | ⊥,     _ => Entailment.CNNOO
  | φ ⋏ ψ, h =>
    have ihφ : Λ ⊢! ∼∼φ ➝ φ := dneOfNegative (by simp [by simpa using h])
    have ihψ : Λ ⊢! ∼∼ψ ➝ ψ := dneOfNegative (by simp [by simpa using h])
    have : Λ ⊢! ∼φ ➝ ∼(φ ⋏ ψ) := Entailment.contra Entailment.and₁
    have dφ : [∼∼(φ ⋏ ψ)] ⊢[Λ]! φ := of ihφ ⨀ (deduct <| byAxm₁ ⨀ (of this ⨀ byAxm₀))
    have : Λ ⊢! ∼ψ ➝ ∼(φ ⋏ ψ) := Entailment.contra Entailment.and₂
    have dψ : [∼∼(φ ⋏ ψ)] ⊢[Λ]! ψ := of ihψ ⨀ (deduct <| byAxm₁ ⨀ (of this ⨀ byAxm₀))
    deduct' (Entailment.K_intro dφ dψ)
  | φ ➝ ψ, h =>
    let ihψ : Λ ⊢! ∼∼ψ ➝ ψ := dneOfNegative (by simp [by simpa using h])
    have : [∼ψ, φ, ∼∼(φ ➝ ψ)] ⊢[Λ]! ∼(φ ➝ ψ) := deduct <| byAxm₁ ⨀ (byAxm₀ ⨀ byAxm₂)
    have : [∼ψ, φ, ∼∼(φ ➝ ψ)] ⊢[Λ]! ⊥ := byAxm₂ ⨀ this
    have : [φ, ∼∼(φ ➝ ψ)] ⊢[Λ]! ψ := (of ihψ) ⨀ (deduct this)
    deduct' (deduct this)
  | ∀' φ,  h =>
    have ihφ : Λ ⊢! ∼∼(free φ) ➝ free φ := dneOfNegative (by simp [by simpa using h])
    have : [∀' shift φ, ∼(free φ), ∼∼(∀' shift φ)] ⊢[Λ]! ⊥ :=
      have : [∀' shift φ, ∼(free φ), ∼∼(∀' shift φ)] ⊢[Λ]! ∀' shift φ := byAxm₀
      byAxm₁ ⨀ Entailment.cast (by simp) (specializeOverContext this &0)
    have : [∼∼(∀' shift φ)] ⊢[Λ]! free φ := of ihφ ⨀ deduct (byAxm₁ ⨀ deduct this)
    implyAll (Entailment.cast (by simp) (deduct' this))
  termination_by φ _ => φ.complexity

def ofDNOfNegative [L.DecidableEq] {φ : SyntacticFormulaᵢ L} {Γ} (b : Γ ⊢[Λ]! ∼∼φ) (h : φ.IsNegative) : Γ ⊢[Λ]! φ :=
  Entailment.C_trans (toDef b) (dneOfNegative h)

def DN_of_isNegative [L.DecidableEq] {φ : SyntacticFormulaᵢ L} (h : φ.IsNegative) : Λ ⊢! ∼∼φ ⭤ φ :=
  Entailment.K_intro (dneOfNegative h) Entailment.dni

def efqOfNegative : {φ : SyntacticFormulaᵢ L} → φ.IsNegative → Λ ⊢! ⊥ ➝ φ
  | ⊥,     _ => Entailment.C_id ⊥
  | φ ⋏ ψ, h =>
    have ihφ : Λ ⊢! ⊥ ➝ φ := efqOfNegative (by simp [by simpa using h])
    have ihψ : Λ ⊢! ⊥ ➝ ψ := efqOfNegative (by simp [by simpa using h])
    Entailment.CK_of_C_of_C ihφ ihψ
  | φ ➝ ψ, h =>
    have ihψ : Λ ⊢! ⊥ ➝ ψ := efqOfNegative (by simp [by simpa using h])
    Entailment.C_trans ihψ Entailment.implyK
  | ∀' φ,  h =>
    have ihφ : Λ ⊢! ⊥ ➝ free φ := efqOfNegative (by simp [by simpa using h])
    implyAll <| Entailment.cast (by simp) ihφ
  termination_by φ _ => φ.complexity

def iffnegOfNegIff [L.DecidableEq] {φ ψ : SyntacticFormulaᵢ L} (h : φ.IsNegative) (b : Λ ⊢! ∼φ ⭤ ψ) : Λ ⊢! φ ⭤ ∼ψ :=
  Entailment.E_trans (Entailment.E_symm <| DN_of_isNegative h) (Entailment.ENN_of_E b)

def rewrite (f : ℕ → SyntacticTerm L) : Λ ⊢! φ → Λ ⊢! Rew.rewrite f ▹ φ
  | mdp b d        => rewrite f b ⨀ rewrite f d
  | gen (φ := φ) b =>
    let d : Λ ⊢! free ((Rew.rewrite f).q ▹ φ) :=
      HilbertProofᵢ.cast (rewrite (&0 :>ₙ fun x ↦ Rew.shift (f x)) b)
        (by simp [Rew.q_rewrite, Function.comp_def, free_rewrite_eq])
    gen d
  | eaxm h         => eaxm (Λ.rewrite_closed h f)
  | verum          => verum
  | implyK {_ _}     => implyK {_ _}
  | implyS {_ _ _}   => implyS {_ _ _}
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
    (by simp [Rew.q_rewrite, rewrite_subst_nil])
  | ex₁ t φ        => HilbertProofᵢ.cast
    (ex₁ (Rew.rewrite f t) (Rew.rewrite (⇑Rew.bShift ∘ f) ▹ φ))
    (by simp [Rew.q_rewrite, rewrite_subst_eq])
  | ex₂ φ ψ        => HilbertProofᵢ.cast
    (ex₂ (Rew.rewrite (⇑Rew.bShift ∘ f) ▹ φ) (Rew.rewrite f ▹ ψ))
    (by simp [Rew.q_rewrite, rewrite_subst_nil])

@[simp] lemma depth_rewrite (f : ℕ → SyntacticTerm L) (b : Λ ⊢! φ) : ‖rewrite f b‖ = ‖b‖ := by
  induction b generalizing f <;> simp [rewrite, *]

def ofLE {Λ₁ Λ₂ : Hilbertᵢ L} (h : Λ₁ ≤ Λ₂) : Λ₁ ⊢! φ → Λ₂ ⊢! φ
  | mdp b d => (ofLE h b).mdp (ofLE h d)
  | gen b => (ofLE h b).gen
  | eaxm hφ => eaxm <| h hφ
  | verum => verum
  | implyK {_ _} => implyK {_ _}
  | implyS {_ _ _} => implyS {_ _ _}
  | and₁ _ _ => and₁ _ _
  | and₂ _ _ => and₂ _ _
  | and₃ _ _ => and₃ _ _
  | or₁ _ _ => or₁ _ _
  | or₂ _ _ => or₂ _ _
  | or₃ _ _ _ => or₃ _ _ _
  | all₁ _ _ => all₁ _ _
  | all₂ _ _ => all₂ _ _
  | ex₁ _ _ => ex₁ _ _
  | ex₂ _ _ => ex₂ _ _

lemma of_le {Λ₁ Λ₂ : Hilbertᵢ L} (h : Λ₁ ≤ Λ₂) : Λ₁ ⊢ φ → Λ₂ ⊢ φ := fun b ↦ ⟨ofLE h b.get⟩

open Entailment

end HilbertProofᵢ

variable (L)

@[ext] structure Theoryᵢ (𝓗 : Hilbertᵢ L) where
  theory : Set (Sentenceᵢ L)

variable {L}

namespace Theoryᵢ

open LO.Entailment

variable {𝓗 : Hilbertᵢ L} {T : Theoryᵢ L 𝓗}

instance : SetLike (Theoryᵢ L 𝓗) (Sentenceᵢ L) where
  coe := theory
  coe_injective' _ _ := Theoryᵢ.ext

lemma mem_def : φ ∈ T ↔ φ ∈ T.theory := by rfl

@[simp] lemma mem_mk_iff (s : Set (Sentenceᵢ L)) : φ ∈ (⟨s⟩ : Theoryᵢ L 𝓗) ↔ φ ∈ s := by rfl

instance : AdjunctiveSet (Sentenceᵢ L) (Theoryᵢ L 𝓗) where
  Subset T U := ∀ φ ∈ T, φ ∈ U
  emptyCollection := ⟨∅⟩
  adjoin φ T := ⟨adjoin φ T.theory⟩
  subset_iff := by simp
  not_mem_empty := by simp
  mem_cons_iff := by simp [mem_def]

@[simp] lemma empty_eq_empty : ((∅ : Theoryᵢ L 𝓗) : Set (Sentenceᵢ L)) = ∅  := by rfl

@[simp] lemma adjoin_theory_def : (adjoin φ T).theory = insert φ T.theory := rfl

def Proof (T : Theoryᵢ L 𝓗) (φ : Sentenceᵢ L) :=
  (Rewriting.emb '' T.theory) *⊢[𝓗]! (Rewriting.emb φ : SyntacticFormulaᵢ L)

instance : Entailment (Theoryᵢ L 𝓗) (Sentenceᵢ L) := ⟨Theoryᵢ.Proof⟩

lemma provable_def {φ : Sentenceᵢ L} : T ⊢ φ ↔ (Rewriting.emb '' T.theory) *⊢[𝓗] ↑φ := by rfl

def Proof.cast! (e : φ = ψ) : T ⊢! φ → T ⊢! ψ := fun b ↦ e ▸ b

def Proof.weakening! [L.DecidableEq] (ss : T ⊆ U) : T ⊢! φ → U ⊢! φ :=
  Context.weakening (Set.image_mono ss)

open Context

variable [L.DecidableEq]

instance : Axiomatized (Theoryᵢ L 𝓗) where
  prfAxm {T} φ h := by
    show (Rewriting.emb '' T.theory) *⊢[𝓗]! ↑φ
    exact Context.byAxm (Set.mem_image_of_mem _ (by simpa [mem_def] using h))
  weakening {φ T U} ss b := by
    show (Rewriting.emb '' U.theory) *⊢[𝓗]! ↑φ
    apply Context.weakening ?_ b
    exact Set.image_mono ss

def ofHilbert {φ : Sentenceᵢ L} : 𝓗 ⊢! ↑φ → T ⊢! φ := Context.of

def deduct! {φ ψ} (b : adjoin φ T ⊢! ψ) : T ⊢! φ ➝ ψ :=
  have : (Rewriting.emb '' T.theory) *⊢[𝓗]! ↑φ ➝ ↑ψ :=
    Context.deduct <| Context.weakening (by simp [-Set.image_subset_iff, Set.image_insert_eq]) b
  this

def deductInv! {φ ψ} (b : T ⊢! φ ➝ ψ) : adjoin φ T ⊢! ψ :=
  have : insert ↑φ (Rewriting.emb '' T.theory) *⊢[𝓗]! ↑ψ := Context.deductInv b
  Context.weakening (by simp [Set.image_insert_eq]) this

instance : Deduction (Theoryᵢ L 𝓗) where
  ofInsert := deduct!
  inv := deductInv!

variable (𝓗)

instance : Entailment.Minimal T :=
  Minimal.ofEquiv (Context.mk (Rewriting.emb '' T.theory)) T (Rewriting.app Rew.emb)
    fun φ ↦ (Equiv.refl ((Rewriting.emb '' T.theory) *⊢[𝓗]! ↑φ))

instance minimal [Entailment.Int 𝓗] : Entailment.Int T where
  efq := ofHilbert <| efq

instance cl [Entailment.Cl 𝓗] : Entailment.Cl T where
  dne := ofHilbert <| dne

end Theoryᵢ

end LO.FirstOrder
