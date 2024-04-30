import Logic.Logic.System
import Logic.Logic.HilbertStyle

namespace LO

namespace System

variable (F : Type*) [LogicalConnective F] [DecidableEq F] {S : Type*} [System F S]

structure Context (𝓢 : S) where
  ctx : List F

variable {F}

namespace Context

variable {𝓢 : S}

instance : Coe (List F) (Context F 𝓢) := ⟨mk⟩

abbrev conj (Γ : Context F 𝓢) : F := Γ.ctx.conj

abbrev disj (Γ : Context F 𝓢) : F := Γ.ctx.disj

instance : EmptyCollection (Context F 𝓢) := ⟨⟨[]⟩⟩

instance : Membership F (Context F 𝓢) := ⟨(· ∈ ·.ctx)⟩

instance : HasSubset (Context F 𝓢) := ⟨(·.ctx ⊆ ·.ctx)⟩

instance : Cons F (Context F 𝓢) := ⟨(· :: ·.ctx)⟩

lemma mem_def {p : F} {Γ : Context F 𝓢} : p ∈ Γ ↔ p ∈ Γ.ctx := iff_of_eq rfl

@[simp] lemma coe_subset_coe_iff {Γ Δ : List F} : (Γ : Context F 𝓢) ⊆ Δ ↔ Γ ⊆ Δ := iff_of_eq rfl

@[simp] lemma mem_coe_iff {p : F} {Γ : List F} : p ∈ (Γ : Context F 𝓢) ↔ p ∈ Γ := iff_of_eq rfl

@[simp] lemma not_mem_empty (p : F) : ¬p ∈ (∅ : Context F 𝓢) := by simp [EmptyCollection.emptyCollection]

instance : Collection F (Context F 𝓢) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons, mem_def]

instance (𝓢 : S) : System F (Context F 𝓢) := ⟨(𝓢 ⊢ ·.conj ⟶ ·)⟩

abbrev Prf (𝓢 : S) (Γ : List F) (p : F) := (Γ : Context F 𝓢) ⊢ p

abbrev Provable (𝓢 : S) (Γ : List F) (p : F) := (Γ : Context F 𝓢) ⊢! p

local notation Γ:45 " ⊢[" 𝓢 "] " p:46 => Prf 𝓢 Γ p

local notation Γ:45 " ⊢[" 𝓢 "]! " p:46 => Provable 𝓢 Γ p

lemma system_def (Γ : Context F 𝓢) (p : F) : (Γ ⊢ p) = (𝓢 ⊢ Γ.conj ⟶ p) := rfl

def of {Γ : List F} {p : F} (b : 𝓢 ⊢ Γ.conj ⟶ p) : Γ ⊢[𝓢] p := b

def toₛ {Γ : List F} {p : F} (b : Γ ⊢[𝓢] p) : 𝓢 ⊢ Γ.conj ⟶ p := b

lemma provable_iff {p : F} : Γ ⊢[𝓢]! p ↔ 𝓢 ⊢! Γ.conj ⟶ p := iff_of_eq rfl

section minimal

variable [Minimal 𝓢] {Γ Δ E : List F}

instance : Axiomatized (Context F 𝓢) where
  prfAxm := fun _ _ hp ↦ generalConj hp
  weakening := fun H b ↦ impTrans (conjImplyConj H) b

def byAxm {p} (h : p ∈ Γ) : Γ ⊢[𝓢] p := Axiomatized.prfAxm _ (by simpa)

lemma by_axm! {p} (h : p ∈ Γ) : Γ ⊢[𝓢]! p := Axiomatized.provable_axm _ (by simpa)

def weakening (h : Γ ⊆ Δ) {p} : Γ ⊢[𝓢] p → Δ ⊢[𝓢] p := Axiomatized.weakening (by simpa)

lemma weakening! (h : Γ ⊆ Δ) {p} : Γ ⊢[𝓢]! p → Δ ⊢[𝓢]! p := fun h ↦ Axiomatized.le_of_subset_axm (by simpa) h

def of' {p : F} (b : 𝓢 ⊢ p) (Γ : List F) : Γ ⊢[𝓢] p := dhyp Γ.conj b

def emptyPrf {p : F} : [] ⊢[𝓢] p → 𝓢 ⊢ p := fun b ↦ b ⨀ verum

def provable_iff_provable {p : F} : 𝓢 ⊢! p ↔ [] ⊢[𝓢]! p :=
  ⟨fun b ↦ ⟨of' b.some _⟩, fun b ↦ ⟨emptyPrf b.some⟩⟩

instance minimal (Γ : Context F 𝓢) : Minimal Γ where
  mdp := mdp₁
  verum := of' verum _
  imply₁ := fun _ _ ↦ of' imply₁ _
  imply₂ := fun _ _ _ ↦ of' imply₂ _
  conj₁ := fun _ _ ↦ of' conj₁ _
  conj₂ := fun _ _ ↦ of' conj₂ _
  conj₃ := fun _ _ ↦ of' conj₃ _
  disj₁ := fun _ _ ↦ of' disj₁ _
  disj₂ := fun _ _ ↦ of' disj₂ _
  disj₃ := fun _ _ _ ↦ of' disj₃ _

def deduct {p q : F} {Γ : List F} : (p :: Γ) ⊢[𝓢] q → Γ ⊢[𝓢] p ⟶ q := fun b ↦
  of <| andLeft (andImplyIffImplyImply Γ.conj p q) ⨀ impTrans (andComm Γ.conj p) (toₛ b)

def deductInv {p q : F} {Γ : List F} : Γ ⊢[𝓢] p ⟶ q → (p :: Γ) ⊢[𝓢] q := fun b ↦
  of <| impTrans (andComm p Γ.conj) <| andRight (andImplyIffImplyImply Γ.conj p q) ⨀ toₛ b

lemma deduct_iff {p q : F} {Γ : List F} : Γ ⊢[𝓢]! p ⟶ q ↔ (p :: Γ) ⊢[𝓢]! q :=
  ⟨fun h ↦ ⟨deductInv h.some⟩, fun h ↦ ⟨deduct h.some⟩⟩

instance deduction : Deduction (Context F 𝓢) where
  ofInsert := deduct
  inv := deductInv

instance hasEFQ [HasEFQ 𝓢] (Γ : Context F 𝓢) : HasEFQ Γ := ⟨fun _ ↦ of <| dhyp Γ.conj efq⟩

instance hasWeakLEM [HasWeakLEM 𝓢] (Γ : Context F 𝓢) : HasWeakLEM Γ := ⟨fun p ↦ of <| dhyp Γ.conj (HasWeakLEM.wlem p)⟩

instance dummett [Dummett 𝓢] (Γ : Context F 𝓢) : Dummett Γ := ⟨fun p q ↦ of <| dhyp Γ.conj (Dummett.dummett p q)⟩

instance hasDNE [HasDNE 𝓢] (Γ : Context F 𝓢) : HasDNE Γ := ⟨fun p ↦ of <| dhyp Γ.conj (HasDNE.dne p)⟩

end minimal

instance intuitionistic [Intuitionistic 𝓢] (Γ : Context F 𝓢) : Intuitionistic Γ where

instance weakLEM [WeakLEM 𝓢] (Γ : Context F 𝓢) : WeakLEM Γ where

instance gd [GD 𝓢] (Γ : Context F 𝓢) : GD Γ where

instance classical [Classical 𝓢] (Γ : Context F 𝓢) : Classical Γ where

end Context

end System

end LO
