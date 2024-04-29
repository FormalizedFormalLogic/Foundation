import Logic.Logic.System
import Logic.Logic.HilbertStyle

namespace LO

namespace System

variable (F : Type*) [LogicalConnective F] {S : Type*} [System F S]

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

@[simp] lemma mem_coe_iff {p : F} {l : List F} : p ∈ (l : Context F 𝓢) ↔ p ∈ l := iff_of_eq rfl

@[simp] lemma not_mem_empty (p : F) : ¬p ∈ (∅ : Context F 𝓢) := by simp [EmptyCollection.emptyCollection]

instance : Collection F (Context F 𝓢) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons, mem_def]

instance (𝓢 : S) : System F (Context F 𝓢) := ⟨(𝓢 ⊢ ·.conj ⟶ ·)⟩

abbrev Prf (𝓢 : S) (Γ : List F) (p : F) := (Γ : Context F 𝓢) ⊢ p

abbrev Provable (𝓢 : S) (Γ : List F) (p : F) := (Γ : Context F 𝓢) ⊢! p

local notation Γ:45 " ⊢⟨" 𝓢 "⟩ " p:46 => Prf 𝓢 Γ p

local notation Γ:45 " ⊢⟨" 𝓢 "⟩! " p:46 => Provable 𝓢 Γ p

lemma system_def (Γ : Context F 𝓢) (p : F) : (Γ ⊢ p) = (𝓢 ⊢ Γ.conj ⟶ p) := rfl

variable {Γ Δ E : List F}

def prfOf {Γ : List F} {p : F} (b : 𝓢 ⊢ Γ.conj ⟶ p) : Γ ⊢⟨𝓢⟩ p := b

lemma provable_iff {p : F} : Γ ⊢⟨𝓢⟩! p ↔ 𝓢 ⊢! Γ.conj ⟶ p := iff_of_eq rfl

variable [DecidableEq F] [Minimal 𝓢]

instance : Axiomatized (Context F 𝓢) where
  prfAxm := fun _ _ hp ↦ generalConj hp
  weakening := fun H b ↦ impTrans (conjImplyConj H) b

def toContextPrf {p : F} {Γ} : 𝓢 ⊢ p → Γ ⊢⟨𝓢⟩ p := dhyp Γ.conj

def ofContextPrf {p : F} : [] ⊢⟨𝓢⟩ p → 𝓢 ⊢ p := fun b ↦ b ⨀ verum

def provable_iff_provable {p : F} : 𝓢 ⊢! p ↔ [] ⊢⟨𝓢⟩! p :=
  ⟨fun b ↦ ⟨toContextPrf b.some⟩, fun b ↦ ⟨ofContextPrf b.some⟩⟩

instance minimal (Γ : Context F 𝓢) : Minimal Γ where
  mdp := mdp₁
  verum := toContextPrf verum
  imply₁ := fun _ _ ↦ toContextPrf imply₁
  imply₂ := fun _ _ _ ↦ toContextPrf imply₂
  conj₁ := fun _ _ ↦ toContextPrf conj₁
  conj₂ := fun _ _ ↦ toContextPrf conj₂
  conj₃ := fun _ _ ↦ toContextPrf conj₃
  disj₁ := fun _ _ ↦ toContextPrf disj₁
  disj₂ := fun _ _ ↦ toContextPrf disj₂
  disj₃ := fun _ _ _ ↦ toContextPrf disj₃

end Context

end System

end LO
