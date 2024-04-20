import Logic.Logic.LogicSymbol

namespace LO

structure System (F : Type*) where
  Prf : F → Type*

namespace System

variable {F : Type*}

section

variable (𝓢 : System F)

infix:45 " ⊫ " => System.Prf

def Provable (f : F) : Prop := Nonempty (𝓢 ⊫ f)

def Unprovable (f : F) : Prop := IsEmpty (𝓢 ⊫ f)

infix:45 " ⊫! " => Provable

infix:45 " ⊯! " => Unprovable

def PrfSet (s : Set F) : Type _ := {f : F} → f ∈ s → 𝓢 ⊫ f

def ProvableSet (s : Set F) : Prop := ∀ f ∈ s, 𝓢 ⊫! f

infix:45 " ⊫* " => PrfSet

infix:45 " ⊫*! " => ProvableSet

def theory : Set F := {f | 𝓢 ⊫! f}

end

lemma not_provable_iff_unprovable {𝓢 : System F} {f : F} :
    ¬𝓢 ⊫! f ↔ 𝓢 ⊯! f := by simp [Provable, Unprovable]

lemma not_unprovable_iff_provable {𝓢 : System F} {f : F} :
    ¬𝓢 ⊯! f ↔ 𝓢 ⊫! f := by simp [Provable, Unprovable]

instance : Preorder (System F) where
  le := fun 𝓢 𝓢' ↦ 𝓢.theory ⊆ 𝓢'.theory
  le_refl := fun 𝓢 ↦ Set.Subset.refl _
  le_trans := fun _ _ _ h₁ h₂ ↦ Set.Subset.trans h₁ h₂

lemma le_iff {𝓢 𝓢' : System F} : 𝓢 ≤ 𝓢' ↔ (∀ {f}, 𝓢 ⊫! f → 𝓢' ⊫! f) :=
  ⟨fun h _ hf ↦ h hf, fun h _ hf ↦ h hf⟩

lemma lt_iff {𝓢 𝓢' : System F} : 𝓢 < 𝓢' ↔ (∀ {f}, 𝓢 ⊫! f → 𝓢' ⊫! f) ∧ (∃ f, 𝓢 ⊯! f ∧ 𝓢' ⊫! f) := by
  simp [lt_iff_le_not_le, le_iff]; intro _
  exact exists_congr (fun _ ↦ by simp [and_comm, not_provable_iff_unprovable])

lemma weakening {𝓢 𝓢' : System F} (h : 𝓢 ≤ 𝓢') {f} : 𝓢 ⊫! f → 𝓢' ⊫! f := le_iff.mp h

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

def topSys {f : F} : ⊤ ⊫ f := PUnit.unit

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

lemma not_Inconsistent_iff_Consistent {𝓢 : System F} :
    ¬𝓢.Inconsistent ↔ 𝓢.Consistent := by simp [inconsistent_iff_top_le, consistent_iff_lt_top, lt_iff_le_not_le]

lemma not_Consistent_iff_Inconsistent {𝓢 : System F} :
    ¬𝓢.Consistent ↔ 𝓢.Inconsistent := by simp [←not_Inconsistent_iff_Consistent]

structure Translation {F F'} (𝓢 : System F) (𝓢' : System F') where
  toFun : F → F'
  prf {f} : 𝓢 ⊫ f → 𝓢' ⊫ toFun f

variable [LogicalConnective F]

variable (𝓢 : System F)

def Complete : Prop := ∀ f, 𝓢 ⊫! f ∨ 𝓢 ⊫! ~f

def Undecidable (f : F) : Prop := 𝓢 ⊯! f ∧ 𝓢 ⊯! ~f

class ModusPonens (𝓢 : System F) where
  mdp {p q : F} : 𝓢 ⊫ (p ⟶ q) → 𝓢 ⊫ p → 𝓢 ⊫ q

class Minimal (𝓢 : System F) extends 𝓢.ModusPonens where
  verum              : 𝓢 ⊫ ⊤
  imply₁ (p q : F)   : 𝓢 ⊫ p ⟶ (q ⟶ p)
  imply₂ (p q r : F) : 𝓢 ⊫ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r
  conj₁  (p q : F)   : 𝓢 ⊫ p ⋏ q ⟶ p
  conj₂  (p q : F)   : 𝓢 ⊫ p ⋏ q ⟶ q
  conj₃  (p q : F)   : 𝓢 ⊫ p ⟶ q ⟶ p ⋏ q
  disj₁  (p q : F)   : 𝓢 ⊫ p ⟶ p ⋎ q
  disj₂  (p q : F)   : 𝓢 ⊫ q ⟶ p ⋎ q
  disj₃  (p q r : F) : 𝓢 ⊫ (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r

/-- Supplymental -/
class HasEFQ (𝓢 : System F) where
  efq (p : F) : 𝓢 ⊫ ⊥ ⟶ p

class HasWeakLEM (𝓢 : System F) where
  wlem (p : F) : 𝓢 ⊫ ~p ⋎ ~~p

class HasLEM (𝓢 : System F) where
  lem (p : F) : 𝓢 ⊫ p ⋎ ~p

class DNE (𝓢 : System F) where
  dne (p : F) : 𝓢 ⊫ ~~p ⟶ p

class Dummett (𝓢 : System F) where
  dummett (p q : F) : 𝓢 ⊫ (p ⟶ q) ⋎ (q ⟶ p)

class Peirce (𝓢 : System F) where
  peirce (p q : F) : 𝓢 ⊫ ((p ⟶ q) ⟶ p) ⟶ p

/--
  Intuitionistic Propositional Logic.

  Modal companion of `𝐒𝟒`
-/
class Intuitionistic (𝓢 : System F) extends 𝓢.Minimal, 𝓢.HasEFQ

/--
  Propositional Logic for Weak Law of Excluded Middle.

  Modal companion of `𝐒𝟒.𝟐`
-/
class WeakLEM (𝓢 : System F) extends 𝓢.Intuitionistic, 𝓢.HasWeakLEM

/--
  Gödel-Dummett Propositional Logic.

  Modal companion of `𝐒𝟒.𝟑`
-/
class GD (𝓢 : System F) extends 𝓢.Intuitionistic, 𝓢.Dummett

/--
  Classical Propositional Logic.

  Modal companion of `𝐒𝟓`
-/
class Classical (𝓢 : System F) extends 𝓢.Minimal, 𝓢.DNE

end System

end LO
