import Foundation.Logic.Entailment
import Foundation.Logic.HilbertStyle.Basic

namespace LO

namespace Entailment

variable (F : Type*) {S : Type*}

structure FiniteContext (𝓢 : S) where
  ctx : List F

variable {F}

namespace FiniteContext

variable {𝓢 : S}

instance : Coe (List F) (FiniteContext F 𝓢) := ⟨mk⟩

abbrev conj [LogicalConnective F] (Γ : FiniteContext F 𝓢) : F := ⋀Γ.ctx

abbrev disj [LogicalConnective F] (Γ : FiniteContext F 𝓢) : F := ⋁Γ.ctx

instance : EmptyCollection (FiniteContext F 𝓢) := ⟨⟨[]⟩⟩

instance : Membership F (FiniteContext F 𝓢) := ⟨λ Γ x => (x ∈ Γ.ctx)⟩

instance : HasSubset (FiniteContext F 𝓢) := ⟨(·.ctx ⊆ ·.ctx)⟩

instance : Adjoin F (FiniteContext F 𝓢) := ⟨(· :: ·.ctx)⟩

lemma mem_def {φ : F} {Γ : FiniteContext F 𝓢} : φ ∈ Γ ↔ φ ∈ Γ.ctx := iff_of_eq rfl

@[simp] lemma coe_subset_coe_iff {Γ Δ : List F} : (Γ : FiniteContext F 𝓢) ⊆ Δ ↔ Γ ⊆ Δ := iff_of_eq rfl

@[simp] lemma mem_coe_iff {φ : F} {Γ : List F} : φ ∈ (Γ : FiniteContext F 𝓢) ↔ φ ∈ Γ := iff_of_eq rfl

@[simp] lemma not_mem_empty (φ : F) : ¬φ ∈ (∅ : FiniteContext F 𝓢) := by simp [EmptyCollection.emptyCollection]

instance : AdjunctiveSet F (FiniteContext F 𝓢) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin, mem_def]

variable [Entailment S F] [LogicalConnective F]

instance (𝓢 : S) : Entailment (FiniteContext F 𝓢) F := ⟨(𝓢 ⊢! ·.conj ➝ ·)⟩

abbrev Prf (𝓢 : S) (Γ : List F) (φ : F) : Type _ := (Γ : FiniteContext F 𝓢) ⊢! φ

abbrev Provable (𝓢 : S) (Γ : List F) (φ : F) : Prop := (Γ : FiniteContext F 𝓢) ⊢ φ

abbrev Unprovable (𝓢 : S) (Γ : List F) (φ : F) : Prop := (Γ : FiniteContext F 𝓢) ⊬ φ

abbrev PrfSet (𝓢 : S) (Γ : List F) (s : Set F) : Type _ := (Γ : FiniteContext F 𝓢) ⊢!* s

abbrev ProvableSet (𝓢 : S) (Γ : List F) (s : Set F) : Prop := (Γ : FiniteContext F 𝓢) ⊢* s

notation Γ:45 " ⊢[" 𝓢 "]! " φ:46 => Prf 𝓢 Γ φ

notation Γ:45 " ⊢[" 𝓢 "] " φ:46 => Provable 𝓢 Γ φ

notation Γ:45 " ⊬[" 𝓢 "] " φ:46 => Unprovable 𝓢 Γ φ

notation Γ:45 " ⊢[" 𝓢 "]!* " s:46 => PrfSet 𝓢 Γ s

notation Γ:45 " ⊢[" 𝓢 "]* " s:46 => ProvableSet 𝓢 Γ s

lemma entailment_def (Γ : FiniteContext F 𝓢) (φ : F) : (Γ ⊢! φ) = (𝓢 ⊢! Γ.conj ➝ φ) := rfl

def ofDef {Γ : List F} {φ : F} (b : 𝓢 ⊢! ⋀Γ ➝ φ) : Γ ⊢[𝓢]! φ := b

def toDef {Γ : List F} {φ : F} (b : Γ ⊢[𝓢]! φ) : 𝓢 ⊢! ⋀Γ ➝ φ := b

lemma toₛ! (b : Γ ⊢[𝓢] φ) : 𝓢 ⊢ ⋀Γ ➝ φ := b

lemma provable_iff {φ : F} : Γ ⊢[𝓢] φ ↔ 𝓢 ⊢ ⋀Γ ➝ φ := iff_of_eq rfl

def cast {Γ φ} (d : Γ ⊢[𝓢]! φ) (eΓ : Γ = Γ') (eφ : φ = φ') : Γ' ⊢[𝓢]! φ' := eΓ ▸ eφ ▸ d

section

variable {Γ Δ E : List F}
variable [Entailment.Minimal 𝓢]

instance [DecidableEq F] : Axiomatized (FiniteContext F 𝓢) where
  prfAxm := fun hp ↦ left_Conj₂_intro hp
  weakening := fun H b ↦ C_trans (CConj₂Conj₂ H) b

instance : Compact (FiniteContext F 𝓢) where
  Γ := fun {Γ} _ _ ↦ Γ
  ΓPrf := id
  Γ_subset := by simp
  Γ_finite := by rintro ⟨Γ⟩; simp [AdjunctiveSet.Finite, AdjunctiveSet.set]

def nthAxm {Γ} (n : ℕ) (h : n < Γ.length := by simp) : Γ ⊢[𝓢]! Γ[n] := conj₂Nth Γ n h
lemma nth_axm! {Γ} (n : ℕ) (h : n < Γ.length := by simp) : Γ ⊢[𝓢] Γ[n] := ⟨nthAxm n h⟩

def byAxm [DecidableEq F] {φ} (h : φ ∈ Γ := by simp) : Γ ⊢[𝓢]! φ := Axiomatized.prfAxm (by simpa)

lemma by_axm! [DecidableEq F] {φ} (h : φ ∈ Γ := by simp) : Γ ⊢[𝓢] φ := Axiomatized.provable_axm _ (by simpa)

def weakening [DecidableEq F] (h : Γ ⊆ Δ) {φ} : Γ ⊢[𝓢]! φ → Δ ⊢[𝓢]! φ := Axiomatized.weakening (by simpa)

lemma weakening! [DecidableEq F] (h : Γ ⊆ Δ) {φ} : Γ ⊢[𝓢] φ → Δ ⊢[𝓢] φ := fun h ↦
  (Axiomatized.le_of_subset (by simpa)).subset h

def of {φ : F} (b : 𝓢 ⊢! φ) : Γ ⊢[𝓢]! φ := C_of_conseq (ψ := ⋀Γ) b

def emptyPrf {φ : F} : [] ⊢[𝓢]! φ → 𝓢 ⊢! φ := fun b ↦ b ⨀ verum

def provable_iff_provable {φ : F} : 𝓢 ⊢ φ ↔ [] ⊢[𝓢] φ :=
  ⟨fun b ↦ ⟨of b.some⟩, fun b ↦ ⟨emptyPrf b.some⟩⟩

lemma of'! [DecidableEq F] (h : 𝓢 ⊢ φ) : Γ ⊢[𝓢] φ := weakening! (by simp) $ provable_iff_provable.mp h

def id : [φ] ⊢[𝓢]! φ := nthAxm 0
@[simp] lemma id! : [φ] ⊢[𝓢] φ := nth_axm! 0

def byAxm₀ : (φ :: Γ) ⊢[𝓢]! φ := nthAxm 0
lemma by_axm₀! : (φ :: Γ) ⊢[𝓢] φ := nth_axm! 0

def byAxm₁ : (φ :: ψ :: Γ) ⊢[𝓢]! ψ := nthAxm 1
lemma by_axm₁! : (φ :: ψ :: Γ) ⊢[𝓢] ψ := nth_axm! 1

def byAxm₂ : (φ :: ψ :: χ :: Γ) ⊢[𝓢]! χ := nthAxm 2
lemma by_axm₂! : (φ :: ψ :: χ :: Γ) ⊢[𝓢] χ := nth_axm! 2

instance (Γ : FiniteContext F 𝓢) : Entailment.ModusPonens Γ := ⟨mdp₁⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomVerum Γ := ⟨of verum⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomImply₁ Γ := ⟨fun _ _ ↦ of imply₁⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomImply₂ Γ := ⟨fun _ _ _ ↦ of imply₂⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomAndElim Γ := ⟨fun _ _ ↦ of and₁, fun _ _ ↦ of and₂⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomAndInst Γ := ⟨fun _ _ ↦ of and₃⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomOrInst Γ := ⟨fun _ _ ↦ of or₁, fun _ _ ↦ of or₂⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomOrElim Γ := ⟨fun _ _ _ ↦ of or₃⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.NegationEquiv Γ := ⟨fun _ ↦ of negEquiv⟩

instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : Entailment.Minimal Γ where


def mdp' [DecidableEq F] (bΓ : Γ ⊢[𝓢]! φ ➝ ψ) (bΔ : Δ ⊢[𝓢]! φ) : (Γ ++ Δ) ⊢[𝓢]! ψ :=
  wk (by simp) bΓ ⨀ wk (by simp) bΔ

def deduct {φ ψ : F} : {Γ : List F} → (φ :: Γ) ⊢[𝓢]! ψ → Γ ⊢[𝓢]! φ ➝ ψ
  | .nil => fun b ↦ ofDef <| C_of_conseq (toDef b)
  | .cons _ _ => fun b ↦ ofDef <| CC_of_CK (C_trans (CKK _ _) (toDef b))

lemma deduct! (h : (φ :: Γ) ⊢[𝓢] ψ) :  Γ ⊢[𝓢] φ ➝ ψ  := ⟨FiniteContext.deduct h.some⟩

def deductInv {φ ψ : F} : {Γ : List F} → Γ ⊢[𝓢]! φ ➝ ψ → (φ :: Γ) ⊢[𝓢]! ψ
  | .nil => λ b => ofDef <| (toDef b) ⨀ verum
  | .cons _ _ => λ b => ofDef <| (C_trans (CKK _ _) (CK_of_CC (toDef b)))

lemma deductInv! (h : Γ ⊢[𝓢] φ ➝ ψ) : (φ :: Γ) ⊢[𝓢] ψ := ⟨FiniteContext.deductInv h.some⟩

lemma deduct_iff {φ ψ : F} {Γ : List F} : Γ ⊢[𝓢] φ ➝ ψ ↔ (φ :: Γ) ⊢[𝓢] ψ :=
  ⟨fun h ↦ ⟨deductInv h.some⟩, fun h ↦ ⟨deduct h.some⟩⟩

def deduct' : [φ] ⊢[𝓢]! ψ → 𝓢 ⊢! φ ➝ ψ := fun b ↦ emptyPrf <| deduct b

lemma deduct'! (h : [φ] ⊢[𝓢] ψ) : 𝓢 ⊢ φ ➝ ψ := ⟨FiniteContext.deduct' h.some⟩


def deductInv' : 𝓢 ⊢! φ ➝ ψ → [φ] ⊢[𝓢]! ψ := fun b ↦ deductInv <| of b

lemma deductInv'! (h : 𝓢 ⊢ φ ➝ ψ) : [φ] ⊢[𝓢] ψ := ⟨FiniteContext.deductInv' h.some⟩


instance deduction : Deduction (FiniteContext F 𝓢) where
  ofInsert := deduct
  inv := deductInv

instance [DecidableEq F] : StrongCut (FiniteContext F 𝓢) (FiniteContext F 𝓢) :=
  ⟨fun {Γ Δ _} bΓ bΔ ↦
    have : Γ ⊢! Δ.conj := Conj₂_intro _ (fun _ hp ↦ bΓ hp)
    ofDef <| C_trans (toDef this) (toDef bΔ)⟩

instance [HasAxiomEFQ 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomEFQ Γ := ⟨fun _ ↦ of efq⟩

instance [HasAxiomEFQ 𝓢] : DeductiveExplosion (FiniteContext F 𝓢) := inferInstance
instance [Entailment.Int 𝓢] (Γ : FiniteContext F 𝓢) : Entailment.Int Γ where

instance [HasAxiomDNE 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomDNE Γ := ⟨fun φ ↦ of (HasAxiomDNE.dne φ)⟩
instance [Entailment.Cl 𝓢] (Γ : FiniteContext F 𝓢) : Entailment.Cl Γ where

end

end FiniteContext


variable (F)

structure Context (𝓢 : S) where
  ctx : Set F

variable {F}


namespace Context

variable {𝓢 : S}

instance : Coe (Set F) (Context F 𝓢) := ⟨mk⟩

instance : EmptyCollection (Context F 𝓢) := ⟨⟨∅⟩⟩

instance : Membership F (Context F 𝓢) := ⟨λ Γ x => (x ∈ Γ.ctx)⟩

instance : HasSubset (Context F 𝓢) := ⟨(·.ctx ⊆ ·.ctx)⟩

instance : Adjoin F (Context F 𝓢) := ⟨(⟨insert · ·.ctx⟩)⟩

lemma mem_def {φ : F} {Γ : Context F 𝓢} : φ ∈ Γ ↔ φ ∈ Γ.ctx := iff_of_eq rfl

@[simp] lemma coe_subset_coe_iff {Γ Δ : Set F} : (Γ : Context F 𝓢) ⊆ Δ ↔ Γ ⊆ Δ := iff_of_eq rfl

@[simp] lemma mem_coe_iff {φ : F} {Γ : Set F} : φ ∈ (Γ : Context F 𝓢) ↔ φ ∈ Γ := iff_of_eq rfl

@[simp] lemma not_mem_empty (φ : F) : ¬φ ∈ (∅ : Context F 𝓢) := by exact fun a ↦ a

instance : AdjunctiveSet F (Context F 𝓢) where
  subset_iff := by rintro ⟨s⟩ ⟨u⟩; simp [Set.subset_def]
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin, mem_def]

variable [LogicalConnective F] [Entailment S F]

structure Proof (Γ : Context F 𝓢) (φ : F) where
  ctx : List F
  subset : ∀ ψ ∈ ctx, ψ ∈ Γ
  prf : ctx ⊢[𝓢]! φ

instance (𝓢 : S) : Entailment (Context F 𝓢) F := ⟨Proof⟩

variable (𝓢)

abbrev Prf (Γ : Set F) (φ : F) : Type _ := (Γ : Context F 𝓢) ⊢! φ

abbrev Provable (Γ : Set F) (φ : F) : Prop := (Γ : Context F 𝓢) ⊢ φ

abbrev Unprovable (Γ : Set F) (φ : F) : Prop := (Γ : Context F 𝓢) ⊬ φ

abbrev PrfSet (Γ : Set F) (s : Set F) : Type _ := (Γ : Context F 𝓢) ⊢!* s

abbrev ProvableSet (Γ : Set F) (s : Set F) : Prop := (Γ : Context F 𝓢) ⊢* s

notation Γ:45 " *⊢[" 𝓢 "]! " φ:46 => Prf 𝓢 Γ φ

notation Γ:45 " *⊢[" 𝓢 "] " φ:46 => Provable 𝓢 Γ φ

notation Γ:45 " *⊬[" 𝓢 "] " φ:46 => Unprovable 𝓢 Γ φ

notation Γ:45 " *⊢[" 𝓢 "]!* " s:46 => PrfSet 𝓢 Γ s

notation Γ:45 " *⊢[" 𝓢 "]* " s:46 => ProvableSet 𝓢 Γ s

section

variable {𝓢}

lemma provable_iff {φ : F} : Γ *⊢[𝓢] φ ↔ ∃ Δ : List F, (∀ ψ ∈ Δ, ψ ∈ Γ) ∧ Δ ⊢[𝓢] φ :=
  ⟨by rintro ⟨⟨Δ, h, b⟩⟩; exact ⟨Δ, h, ⟨b⟩⟩, by rintro ⟨Δ, h, ⟨d⟩⟩; exact ⟨⟨Δ, h, d⟩⟩⟩

section minimal

variable [Entailment.Minimal 𝓢]

instance [DecidableEq F] : Axiomatized (Context F 𝓢) where
  prfAxm := fun {Γ φ} hp ↦ ⟨[φ], by simpa using hp, byAxm (by simp [AdjunctiveSet.set])⟩
  weakening := fun h b ↦ ⟨b.ctx, fun φ hp ↦ AdjunctiveSet.subset_iff.mp h φ (b.subset φ hp), b.prf⟩

def byAxm [DecidableEq F] {Γ : Set F} {φ : F} (h : φ ∈ Γ) : Γ *⊢[𝓢]! φ := Axiomatized.prfAxm (by simpa)

lemma by_axm [DecidableEq F] {Γ : Set F} {φ : F} (h : φ ∈ Γ) : Γ *⊢[𝓢] φ := Axiomatized.provable_axm _ (by simpa)

instance : Compact (Context F 𝓢) where
  Γ := fun b ↦ AdjunctiveSet.set b.ctx
  ΓPrf := fun b ↦ ⟨b.ctx, by simp [AdjunctiveSet.set], b.prf⟩
  Γ_subset := by rintro ⟨Γ⟩ φ b; exact b.subset
  Γ_finite := by rintro ⟨Γ⟩; simp [AdjunctiveSet.Finite, AdjunctiveSet.set]

-- lemma provable_iff' [DecidableEq F] {φ : F} : Γ *⊢[𝓢] φ ↔ ∃ Δ : Finset F, (↑Δ ⊆ Γ) ∧ Δ *⊢[𝓢] φ

def deduct [DecidableEq F] {φ ψ : F} {Γ : Set F} : (insert φ Γ) *⊢[𝓢]! ψ → Γ *⊢[𝓢]! φ ➝ ψ
  | ⟨Δ, h, b⟩ =>
    have h : ∀ ψ ∈ Δ, ψ = φ ∨ ψ ∈ Γ := by simpa using h
    let b' : (φ :: Δ.filter (· ≠ φ)) ⊢[𝓢]! ψ :=
      FiniteContext.weakening
        (by simp [List.subset_def, List.mem_filter]; rintro χ hr; simp [hr]; tauto)
        b
    ⟨ Δ.filter (· ≠ φ), by
      intro ψ; simp [List.mem_filter]
      intro hq ne
      rcases h ψ hq
      · contradiction
      · assumption,
      FiniteContext.deduct b' ⟩
lemma deduct! [DecidableEq F] (h : (insert φ Γ) *⊢[𝓢] ψ) : Γ *⊢[𝓢] φ ➝ ψ := ⟨Context.deduct h.some⟩

def deductInv {φ ψ : F} {Γ : Set F} : Γ *⊢[𝓢]! φ ➝ ψ → (insert φ Γ) *⊢[𝓢]! ψ
  | ⟨Δ, h, b⟩ => ⟨φ :: Δ, by simp; intro χ hr; exact Or.inr (h χ hr), FiniteContext.deductInv b⟩
lemma deductInv! [DecidableEq F] (h : Γ *⊢[𝓢] φ ➝ ψ) : (insert φ Γ) *⊢[𝓢] ψ := ⟨Context.deductInv h.some⟩

instance deduction [DecidableEq F] : Deduction (Context F 𝓢) where
  ofInsert := deduct
  inv := deductInv

def weakening [DecidableEq F] (h : Γ ⊆ Δ) {φ : F} : Γ *⊢[𝓢]! φ → Δ *⊢[𝓢]! φ := Axiomatized.weakening (by simpa)
lemma weakening! [DecidableEq F] (h : Γ ⊆ Δ) {φ : F} : Γ *⊢[𝓢] φ → Δ *⊢[𝓢] φ := fun h ↦ (Axiomatized.le_of_subset (by simpa)).subset h

def of {φ : F} (b : 𝓢 ⊢! φ) : Γ *⊢[𝓢]! φ := ⟨[], by simp, FiniteContext.of b⟩

lemma of! (b : 𝓢 ⊢ φ) : Γ *⊢[𝓢] φ := ⟨Context.of b.some⟩

def mdp [DecidableEq F] {Γ : Set F} (bpq : Γ *⊢[𝓢]! φ ➝ ψ) (bp : Γ *⊢[𝓢]! φ) : Γ *⊢[𝓢]! ψ :=
  ⟨ bpq.ctx ++ bp.ctx, by
    simp; rintro χ (hr | hr)
    · exact bpq.subset χ hr
    · exact bp.subset χ hr,
    FiniteContext.mdp' bpq.prf bp.prf ⟩

lemma by_axm! [DecidableEq F] (h : φ ∈ Γ) : Γ *⊢[𝓢] φ := Entailment.by_axm _ (by simpa)

def emptyPrf {φ : F} : ∅ *⊢[𝓢]! φ → 𝓢 ⊢! φ := by
  rintro ⟨Γ, hΓ, h⟩;
  have := List.eq_nil_iff_forall_not_mem.mpr hΓ;
  subst this;
  exact FiniteContext.emptyPrf h;

lemma emptyPrf! {φ : F} : ∅ *⊢[𝓢] φ → 𝓢 ⊢ φ := fun h ↦ ⟨emptyPrf h.some⟩

lemma provable_iff_provable {φ : F} : 𝓢 ⊢ φ ↔ ∅ *⊢[𝓢] φ := ⟨of!, emptyPrf!⟩

lemma iff_provable_context_provable_finiteContext_toList [DecidableEq F] {Δ : Finset F} : ↑Δ *⊢[𝓢] φ ↔ Δ.toList ⊢[𝓢] φ := by
  constructor;
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply FiniteContext.weakening! ?_ hΓ₂;
    intro ψ hψ;
    simpa using hΓ₁ ψ hψ;
  . intro h;
    apply Context.provable_iff.mpr;
    use Δ.toList;
    constructor;
    . simp;
    . assumption;

instance minimal [DecidableEq F] (Γ : Context F 𝓢) : Entailment.Minimal Γ where
  mdp := mdp
  verum := of verum
  imply₁ := fun _ _ ↦ of imply₁
  imply₂ := fun _ _ _ ↦ of imply₂
  and₁ := fun _ _ ↦ of and₁
  and₂ := fun _ _ ↦ of and₂
  and₃ := fun _ _ ↦ of and₃
  or₁ := fun _ _ ↦ of or₁
  or₂ := fun _ _ ↦ of or₂
  or₃ := fun _ _ _ ↦ of or₃
  negEquiv := fun _ ↦ of negEquiv

instance [HasAxiomEFQ 𝓢] (Γ : Context F 𝓢) : HasAxiomEFQ Γ := ⟨fun _ ↦ of efq⟩

instance [HasAxiomDNE 𝓢] (Γ : Context F 𝓢) : HasAxiomDNE Γ := ⟨fun φ ↦ of (HasAxiomDNE.dne φ)⟩

instance [HasAxiomEFQ 𝓢] : DeductiveExplosion (FiniteContext F 𝓢) := inferInstance

end minimal

instance [DecidableEq F] [Entailment.Int 𝓢] (Γ : Context F 𝓢) : Entailment.Int Γ where

instance [DecidableEq F] [Entailment.Cl 𝓢] (Γ : Context F 𝓢) : Entailment.Cl Γ where

end

end Context

end Entailment

end LO
