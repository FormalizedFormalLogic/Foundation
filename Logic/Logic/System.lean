import Logic.Logic.LogicSymbol

namespace LO

structure System (F : Type*) where
  Prf : F → Type*

namespace System

variable {F : Type*}

section

variable (𝓢 : System F)

infix:50 " ⊫ " => System.Prf

def Provable (f : F) : Prop := Nonempty (𝓢 ⊫ f)

def Unprovable (f : F) : Prop := IsEmpty (𝓢 ⊫ f)

infix:50 " ⊫! " => Provable

infix:50 " ⊯! " => Unprovable

def theory : Set F := {f | 𝓢 ⊫! f}

end

instance : Preorder (System F) where
  le := fun 𝓢 𝓢' ↦ 𝓢.theory ⊆ 𝓢'.theory
  le_refl := fun 𝓢 ↦ Set.Subset.refl _
  le_trans := fun _ _ _ h₁ h₂ ↦ Set.Subset.trans h₁ h₂

lemma le_iff {𝓢 𝓢' : System F} : 𝓢 ≤ 𝓢' ↔ (∀ {f}, 𝓢 ⊫! f → 𝓢' ⊫! f) :=
  ⟨fun h _ hf ↦ h hf, fun h _ hf ↦ h hf⟩

def Equiv (𝓢 𝓢' : System F) : Prop := 𝓢.theory = 𝓢'.theory

@[simp, refl] protected lemma Equiv.refl (𝓢 : System F) : Equiv 𝓢 𝓢 := rfl

@[symm] lemma Equiv.symm {𝓢 𝓢' : System F} : Equiv 𝓢 𝓢' → Equiv 𝓢' 𝓢 := Eq.symm

@[trans] lemma Equiv.trans {𝓢 𝓢' 𝓢'' : System F} : Equiv 𝓢 𝓢' → Equiv 𝓢' 𝓢'' → Equiv 𝓢 𝓢'' := Eq.trans

lemma equiv_iff {𝓢 𝓢' : System F} : Equiv 𝓢 𝓢' ↔ (∀ f, 𝓢 ⊫! f ↔ 𝓢' ⊫! f) := by simp [Equiv, Set.ext_iff, theory]

lemma le_antisymm {𝓢 𝓢' : System F} (h : 𝓢 ≤ 𝓢') (h' : 𝓢' ≤ 𝓢) : Equiv 𝓢 𝓢' :=
  equiv_iff.mpr (fun _ ↦ ⟨fun hf ↦ le_iff.mp h hf, fun hf ↦ le_iff.mp h' hf⟩)

instance : BoundedOrder (System F) where
  top := ⟨fun _ ↦ PUnit⟩
  bot := ⟨fun _ ↦ PEmpty⟩
  le_top := fun _ _ _ ↦ ⟨PUnit.unit⟩
  bot_le := fun _ _ ↦ by rintro ⟨⟨⟩⟩

def topPrf {f : F} : ⊤ ⊫ f := PUnit.unit

@[simp] lemma top_provable {f : F} : ⊤ ⊫! f := ⟨PUnit.unit⟩

class Inconsistent (𝓢 : System F) : Prop where
  top_le : ⊤ ≤ 𝓢

class Consistent (𝓢 : System F) : Prop where
  lt_top : 𝓢 < ⊤

lemma inconsistent_iff_top_le {𝓢 : System F} :
    𝓢.Inconsistent ↔ ⊤ ≤ 𝓢 := ⟨by rintro ⟨h⟩; exact h, fun h ↦ ⟨h⟩⟩

lemma inconsistent_iff {𝓢 : System F} :
    𝓢.Inconsistent ↔ ∀ f, 𝓢 ⊫! f := by simp [inconsistent_iff_top_le, le_iff]

lemma consistent_iff_lt_top {𝓢 : System F} :
    𝓢.Consistent ↔ 𝓢 < ⊤ := ⟨by rintro ⟨h⟩; exact h, fun h ↦ ⟨h⟩⟩

lemma consistent_iff_not_Inconsistent {𝓢 : System F} :
    𝓢.Consistent ↔ ¬𝓢.Inconsistent := by simp [inconsistent_iff_top_le, consistent_iff_lt_top, lt_iff_le_not_le]

lemma inconsistent_iff_not_consistent {𝓢 : System F} :
    𝓢.Inconsistent ↔ ¬𝓢.Consistent := by simp [consistent_iff_not_Inconsistent]

variable [LogicalConnective F]

class ModusPonens (𝓢 : System F) where
  mdp {p q : F} : 𝓢 ⊫ (p ⟶ q) → 𝓢 ⊫ p → 𝓢 ⊫ q

class Minimal (𝓢 : System F) extends ModusPonens 𝓢 where
  verum              : 𝓢 ⊫ ⊤
  imply₁ (p q : F)   : 𝓢 ⊫ (p ⟶ (q ⟶ p))
  imply₂ (p q r : F) : 𝓢 ⊫ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  conj₁  (p q : F)   : 𝓢 ⊫ (p ⋏ q ⟶ p)
  conj₂  (p q : F)   : 𝓢 ⊫ (p ⋏ q ⟶ q)
  conj₃  (p q : F)   : 𝓢 ⊫ (p ⟶ q ⟶ p ⋏ q)
  disj₁  (p q : F)   : 𝓢 ⊫ (p ⟶ p ⋎ q)
  disj₂  (p q : F)   : 𝓢 ⊫ (q ⟶ p ⋎ q)
  disj₃  (p q r : F) : 𝓢 ⊫ ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q) ⟶ r)

end System

end LO
