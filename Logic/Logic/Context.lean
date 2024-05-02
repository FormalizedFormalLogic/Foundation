import Logic.Logic.System
import Logic.Logic.HilbertStyle

namespace LO

namespace System

variable (F : Type*) [LogicalConnective F] [DecidableEq F] {S : Type*} [System F S]

structure FiniteContext (𝓢 : S) where
  ctx : List F

variable {F}

namespace FiniteContext

variable {𝓢 : S}

instance : Coe (List F) (FiniteContext F 𝓢) := ⟨mk⟩

abbrev conj (Γ : FiniteContext F 𝓢) : F := Γ.ctx.conj

abbrev disj (Γ : FiniteContext F 𝓢) : F := Γ.ctx.disj

instance : EmptyCollection (FiniteContext F 𝓢) := ⟨⟨[]⟩⟩

instance : Membership F (FiniteContext F 𝓢) := ⟨(· ∈ ·.ctx)⟩

instance : HasSubset (FiniteContext F 𝓢) := ⟨(·.ctx ⊆ ·.ctx)⟩

instance : Cons F (FiniteContext F 𝓢) := ⟨(· :: ·.ctx)⟩

lemma mem_def {p : F} {Γ : FiniteContext F 𝓢} : p ∈ Γ ↔ p ∈ Γ.ctx := iff_of_eq rfl

@[simp] lemma coe_subset_coe_iff {Γ Δ : List F} : (Γ : FiniteContext F 𝓢) ⊆ Δ ↔ Γ ⊆ Δ := iff_of_eq rfl

@[simp] lemma mem_coe_iff {p : F} {Γ : List F} : p ∈ (Γ : FiniteContext F 𝓢) ↔ p ∈ Γ := iff_of_eq rfl

@[simp] lemma not_mem_empty (p : F) : ¬p ∈ (∅ : FiniteContext F 𝓢) := by simp [EmptyCollection.emptyCollection]

instance : Collection F (FiniteContext F 𝓢) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons, mem_def]

instance (𝓢 : S) : System F (FiniteContext F 𝓢) := ⟨(𝓢 ⊢ ·.conj ⟶ ·)⟩

abbrev Prf (𝓢 : S) (Γ : List F) (p : F) := (Γ : FiniteContext F 𝓢) ⊢ p

abbrev Provable (𝓢 : S) (Γ : List F) (p : F) := (Γ : FiniteContext F 𝓢) ⊢! p

notation Γ:45 " ⊢[" 𝓢 "] " p:46 => Prf 𝓢 Γ p

notation Γ:45 " ⊢[" 𝓢 "]! " p:46 => Provable 𝓢 Γ p

lemma system_def (Γ : FiniteContext F 𝓢) (p : F) : (Γ ⊢ p) = (𝓢 ⊢ Γ.conj ⟶ p) := rfl

def of {Γ : List F} {p : F} (b : 𝓢 ⊢ Γ.conj ⟶ p) : Γ ⊢[𝓢] p := b

def toₛ {Γ : List F} {p : F} (b : Γ ⊢[𝓢] p) : 𝓢 ⊢ Γ.conj ⟶ p := b

lemma provable_iff {p : F} : Γ ⊢[𝓢]! p ↔ 𝓢 ⊢! Γ.conj ⟶ p := iff_of_eq rfl

section minimal

variable [Minimal 𝓢] {Γ Δ E : List F}

instance : Axiomatized (FiniteContext F 𝓢) where
  prfAxm := fun hp ↦ generalConj hp
  weakening := fun H b ↦ impTrans (conjImplyConj H) b

def byAxm {p} (h : p ∈ Γ) : Γ ⊢[𝓢] p := Axiomatized.prfAxm (by simpa)

lemma by_axm! {p} (h : p ∈ Γ) : Γ ⊢[𝓢]! p := Axiomatized.provable_axm _ (by simpa)

def weakening (h : Γ ⊆ Δ) {p} : Γ ⊢[𝓢] p → Δ ⊢[𝓢] p := Axiomatized.weakening (by simpa)

lemma weakening! (h : Γ ⊆ Δ) {p} : Γ ⊢[𝓢]! p → Δ ⊢[𝓢]! p := fun h ↦ Axiomatized.le_of_subset_axm (by simpa) h

def of' {p : F} (b : 𝓢 ⊢ p) : Γ ⊢[𝓢] p := dhyp Γ.conj b

def emptyPrf {p : F} : [] ⊢[𝓢] p → 𝓢 ⊢ p := fun b ↦ b ⨀ verum

def provable_iff_provable {p : F} : 𝓢 ⊢! p ↔ [] ⊢[𝓢]! p :=
  ⟨fun b ↦ ⟨of' b.some⟩, fun b ↦ ⟨emptyPrf b.some⟩⟩

instance minimal (Γ : FiniteContext F 𝓢) : Minimal Γ where
  mdp := mdp₁
  verum := of' verum
  imply₁ := fun _ _ ↦ of' imply₁
  imply₂ := fun _ _ _ ↦ of' imply₂
  conj₁ := fun _ _ ↦ of' conj₁
  conj₂ := fun _ _ ↦ of' conj₂
  conj₃ := fun _ _ ↦ of' conj₃
  disj₁ := fun _ _ ↦ of' disj₁
  disj₂ := fun _ _ ↦ of' disj₂
  disj₃ := fun _ _ _ ↦ of' disj₃

def mdp' (bΓ : Γ ⊢[𝓢] p ⟶ q) (bΔ : Δ ⊢[𝓢] p) : (Γ ++ Δ) ⊢[𝓢] q := wk (by simp) bΓ ⨀ wk (by simp) bΔ

def deduct {p q : F} {Γ : List F} : (p :: Γ) ⊢[𝓢] q → Γ ⊢[𝓢] p ⟶ q := fun b ↦
  of <| andLeft (andImplyIffImplyImply Γ.conj p q) ⨀ impTrans (andComm Γ.conj p) (toₛ b)

def deductInv {p q : F} {Γ : List F} : Γ ⊢[𝓢] p ⟶ q → (p :: Γ) ⊢[𝓢] q := fun b ↦
  of <| impTrans (andComm p Γ.conj) <| andRight (andImplyIffImplyImply Γ.conj p q) ⨀ toₛ b

lemma deduct_iff {p q : F} {Γ : List F} : Γ ⊢[𝓢]! p ⟶ q ↔ (p :: Γ) ⊢[𝓢]! q :=
  ⟨fun h ↦ ⟨deductInv h.some⟩, fun h ↦ ⟨deduct h.some⟩⟩

instance deduction : Deduction (FiniteContext F 𝓢) where
  ofInsert := deduct
  inv := deductInv

instance [HasEFQ 𝓢] (Γ : FiniteContext F 𝓢) : HasEFQ Γ := ⟨fun _ ↦ of' efq⟩

instance [HasWeakLEM 𝓢] (Γ : FiniteContext F 𝓢) : HasWeakLEM Γ := ⟨fun p ↦ of' (HasWeakLEM.wlem p)⟩

instance [Dummett 𝓢] (Γ : FiniteContext F 𝓢) : Dummett Γ := ⟨fun p q ↦ of' (Dummett.dummett p q)⟩

instance [HasDNE 𝓢] (Γ : FiniteContext F 𝓢) : HasDNE Γ := ⟨fun p ↦ of' (HasDNE.dne p)⟩

end minimal

instance [Intuitionistic 𝓢] (Γ : FiniteContext F 𝓢) : Intuitionistic Γ where

instance [WeakLEM 𝓢] (Γ : FiniteContext F 𝓢) : WeakLEM Γ where

instance [GD 𝓢] (Γ : FiniteContext F 𝓢) : GD Γ where

instance [Classical 𝓢] (Γ : FiniteContext F 𝓢) : Classical Γ where

end FiniteContext

variable (F)

structure Context (𝓢 : S) where
  ctx : Set F

variable {F}

namespace Context

variable {𝓢 : S}

instance : Coe (Set F) (Context F 𝓢) := ⟨mk⟩

instance : EmptyCollection (Context F 𝓢) := ⟨⟨∅⟩⟩

instance : Membership F (Context F 𝓢) := ⟨(· ∈ ·.ctx)⟩

instance : HasSubset (Context F 𝓢) := ⟨(·.ctx ⊆ ·.ctx)⟩

instance : Cons F (Context F 𝓢) := ⟨(⟨insert · ·.ctx⟩)⟩

lemma mem_def {p : F} {Γ : Context F 𝓢} : p ∈ Γ ↔ p ∈ Γ.ctx := iff_of_eq rfl

@[simp] lemma coe_subset_coe_iff {Γ Δ : Set F} : (Γ : Context F 𝓢) ⊆ Δ ↔ Γ ⊆ Δ := iff_of_eq rfl

@[simp] lemma mem_coe_iff {p : F} {Γ : Set F} : p ∈ (Γ : Context F 𝓢) ↔ p ∈ Γ := iff_of_eq rfl

@[simp] lemma not_mem_empty (p : F) : ¬p ∈ (∅ : Context F 𝓢) := by simp [EmptyCollection.emptyCollection, Set.mem_def]

instance : Collection F (Context F 𝓢) where
  subset_iff := by rintro ⟨s⟩ ⟨u⟩; simp [Set.subset_def]
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons, mem_def]

structure Proof (Γ : Context F 𝓢) (p : F) where
  ctx : List F
  subset : ∀ q ∈ ctx, q ∈ Γ
  prf : ctx ⊢[𝓢] p

instance (𝓢 : S) : System F (Context F 𝓢) := ⟨Proof⟩

variable (𝓢)

abbrev Prf (Γ : Set F) (p : F) : Type _ := (Γ : Context F 𝓢) ⊢ p

abbrev Provable (Γ : Set F) (p : F) : Prop := (Γ : Context F 𝓢) ⊢! p

notation Γ:45 " *⊢[" 𝓢 "] " p:46 => Prf 𝓢 Γ p

notation Γ:45 " *⊢[" 𝓢 "]! " p:46 => Provable 𝓢 Γ p

variable {𝓢}

lemma provable_iff {p : F} : Γ *⊢[𝓢]! p ↔ ∃ Δ : List F, (∀ q ∈ Δ, q ∈ Γ) ∧ Δ ⊢[𝓢]! p :=
  ⟨by rintro ⟨⟨Δ, h, b⟩⟩; exact ⟨Δ, h, ⟨b⟩⟩, by rintro ⟨Δ, h, ⟨d⟩⟩; exact ⟨⟨Δ, h, d⟩⟩⟩

section minimal

variable [Minimal 𝓢]

instance : Axiomatized (Context F 𝓢) where
  prfAxm := fun {Γ p} hp ↦ ⟨[p], by simpa using hp, byAxm (by simp [Collection.set])⟩
  weakening := fun h b ↦ ⟨b.ctx, fun p hp ↦ Collection.subset_iff.mp h p (b.subset p hp), b.prf⟩

def deduct [DecidableEq F] {p q : F} {Γ : Set F} : (insert p Γ) *⊢[𝓢] q → Γ *⊢[𝓢] p ⟶ q
  | ⟨Δ, h, b⟩ =>
    have h : ∀ q ∈ Δ, q = p ∨ q ∈ Γ := by simpa using h
    let b' : (p :: Δ.filter (· ≠ p)) ⊢[𝓢] q :=
      FiniteContext.weakening
        (by simp [List.subset_def, List.mem_filter]; rintro r hr; simp [hr]; tauto)
        b
    ⟨ Δ.filter (· ≠ p), by
      intro q; simp [List.mem_filter]
      intro hq ne
      rcases h q hq
      · contradiction
      · assumption,
      FiniteContext.deduct b' ⟩

def deductInv {p q : F} {Γ : Set F} : Γ *⊢[𝓢] p ⟶ q → (insert p Γ) *⊢[𝓢] q
  | ⟨Δ, h, b⟩ => ⟨p :: Δ, by simp; intro r hr; exact Or.inr (h r hr), FiniteContext.deductInv b⟩

instance deduction : Deduction (Context F 𝓢) where
  ofInsert := deduct
  inv := deductInv

def of {p : F} (b : 𝓢 ⊢ p) : Γ *⊢[𝓢] p := ⟨[], by simp, FiniteContext.of' b⟩

def mdp {Γ : Set F} (bpq : Γ *⊢[𝓢] p ⟶ q) (bp : Γ *⊢[𝓢] p) : Γ *⊢[𝓢] q :=
  ⟨ bpq.ctx ++ bp.ctx, by
    simp; rintro r (hr | hr)
    · exact bpq.subset r hr
    · exact bp.subset r hr,
    FiniteContext.mdp' bpq.prf bp.prf ⟩

instance minimal (Γ : Context F 𝓢) : Minimal Γ where
  mdp := mdp
  verum := of verum
  imply₁ := fun _ _ ↦ of imply₁
  imply₂ := fun _ _ _ ↦ of imply₂
  conj₁ := fun _ _ ↦ of conj₁
  conj₂ := fun _ _ ↦ of conj₂
  conj₃ := fun _ _ ↦ of conj₃
  disj₁ := fun _ _ ↦ of disj₁
  disj₂ := fun _ _ ↦ of disj₂
  disj₃ := fun _ _ _ ↦ of disj₃

instance [HasEFQ 𝓢] (Γ : Context F 𝓢) : HasEFQ Γ := ⟨fun _ ↦ of efq⟩

instance [HasWeakLEM 𝓢] (Γ : Context F 𝓢) : HasWeakLEM Γ := ⟨fun p ↦ of (HasWeakLEM.wlem p)⟩

instance [Dummett 𝓢] (Γ : Context F 𝓢) : Dummett Γ := ⟨fun p q ↦ of (Dummett.dummett p q)⟩

instance [HasDNE 𝓢] (Γ : Context F 𝓢) : HasDNE Γ := ⟨fun p ↦ of (HasDNE.dne p)⟩

end minimal

instance [Intuitionistic 𝓢] (Γ : Context F 𝓢) : Intuitionistic Γ where

instance [WeakLEM 𝓢] (Γ : Context F 𝓢) : WeakLEM Γ where

instance [GD 𝓢] (Γ : Context F 𝓢) : GD Γ where

instance [Classical 𝓢] (Γ : Context F 𝓢) : Classical Γ where

end Context

end System

end LO
