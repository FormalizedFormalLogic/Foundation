import Logic.Logic.LogicSymbol
import Logic.Logic.Semantics
/-!
# Basic definitions and properties of proof system related notions

This file defines a characterization of the system/proof/provability/calculus of formulas.
Also defines soundness and completeness.

## Main Definitions
* `LO.System`: Proof system of logic.
* `LO.Sound`: Soundness of the proof system.
* `LO.Complete`: Completeness of the proof system.

-/

namespace LO

class System (S : Type*) (F : outParam Type*) where
  Prf : S → F → Type*

infix:45 " ⊫ " => System.Prf

namespace System

variable {S : Type*} {F : Type*} [System S F]

section

variable (𝓢 : S)

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

lemma not_provable_iff_unprovable {𝓢 : S} {f : F} :
    ¬𝓢 ⊫! f ↔ 𝓢 ⊯! f := by simp [Provable, Unprovable]

lemma not_unprovable_iff_provable {𝓢 : S} {f : F} :
    ¬𝓢 ⊯! f ↔ 𝓢 ⊫! f := by simp [Provable, Unprovable]

instance : Preorder S where
  le := fun 𝓢 𝓢' ↦ theory 𝓢 ⊆ theory 𝓢'
  le_refl := fun 𝓢 ↦ Set.Subset.refl _
  le_trans := fun _ _ _ h₁ h₂ ↦ Set.Subset.trans h₁ h₂

lemma le_iff {𝓢 𝓢' : S} : 𝓢 ≤ 𝓢' ↔ (∀ {f}, 𝓢 ⊫! f → 𝓢' ⊫! f) :=
  ⟨fun h _ hf ↦ h hf, fun h _ hf ↦ h hf⟩

lemma lt_iff {𝓢 𝓢' : S} : 𝓢 < 𝓢' ↔ (∀ {f}, 𝓢 ⊫! f → 𝓢' ⊫! f) ∧ (∃ f, 𝓢 ⊯! f ∧ 𝓢' ⊫! f) := by
  simp [lt_iff_le_not_le, le_iff]; intro _
  exact exists_congr (fun _ ↦ by simp [and_comm, not_provable_iff_unprovable])

lemma weakening {𝓢 𝓢' : S} (h : 𝓢 ≤ 𝓢') {f} : 𝓢 ⊫! f → 𝓢' ⊫! f := le_iff.mp h

def Equiv (𝓢 𝓢' : S) : Prop := theory 𝓢 = theory 𝓢'

@[simp, refl] protected lemma Equiv.refl (𝓢 : S) : Equiv 𝓢 𝓢 := rfl

@[symm] lemma Equiv.symm {𝓢 𝓢' : S} : Equiv 𝓢 𝓢' → Equiv 𝓢' 𝓢 := Eq.symm

@[trans] lemma Equiv.trans {𝓢 𝓢' 𝓢'' : S} : Equiv 𝓢 𝓢' → Equiv 𝓢' 𝓢'' → Equiv 𝓢 𝓢'' := Eq.trans

lemma equiv_iff {𝓢 𝓢' : S} : Equiv 𝓢 𝓢' ↔ (∀ f, 𝓢 ⊫! f ↔ 𝓢' ⊫! f) := by simp [Equiv, Set.ext_iff, theory]

lemma le_antisymm {𝓢 𝓢' : S} (h : 𝓢 ≤ 𝓢') (h' : 𝓢' ≤ 𝓢) : Equiv 𝓢 𝓢' :=
  equiv_iff.mpr (fun _ ↦ ⟨fun hf ↦ le_iff.mp h hf, fun hf ↦ le_iff.mp h' hf⟩)

def Inconsistent (𝓢 : S) : Prop := ∀ f, 𝓢 ⊫! f

class Consistent (𝓢 : S) : Prop where
  lt_top : ¬Inconsistent 𝓢

lemma inconsistent_def {𝓢 : S} :
    Inconsistent 𝓢 ↔ ∀ f, 𝓢 ⊫! f := by simp [Inconsistent]

lemma not_Inconsistent_iff_Consistent {𝓢 : S} :
    ¬Inconsistent 𝓢 ↔ Consistent 𝓢 :=
  ⟨fun h ↦ ⟨h⟩, by rintro ⟨h⟩; exact h⟩

lemma not_Consistent_iff_Inconsistent {𝓢 : S} :
    ¬Consistent 𝓢 ↔ Inconsistent 𝓢 := by simp [←not_Inconsistent_iff_Consistent]

structure Translation {S S' F F'} [System S F] [System S' F'] (𝓢 : S) (𝓢' : S') where
  toFun : F → F'
  prf {f} : 𝓢 ⊫ f → 𝓢' ⊫ toFun f

infix:40 " ↝ " => Translation

namespace Translation

protected def id (𝓢 : S) : 𝓢 ↝ 𝓢 where
  toFun := id
  prf := id

variable {S S' S'' : Type*} {F F' F'' : Type*} [System S F] [System S' F'] [System S'' F'']

def comp {𝓢 : S} {𝓢' : S'} {𝓢'' : S''} (t' : 𝓢' ↝ 𝓢'') (t : 𝓢 ↝ 𝓢') : 𝓢 ↝ 𝓢'' where
  toFun := t'.toFun ∘ t.toFun
  prf := t'.prf ∘ t.prf

end Translation

variable [LogicalConnective F]

variable (𝓢 : S)

def Complete : Prop := ∀ f, 𝓢 ⊫! f ∨ 𝓢 ⊫! ~f

def Undecidable (f : F) : Prop := 𝓢 ⊯! f ∧ 𝓢 ⊯! ~f

class ModusPonens (𝓢 : S) where
  mdp {p q : F} : 𝓢 ⊫ p ⟶ q → 𝓢 ⊫ p → 𝓢 ⊫ q

class Minimal (𝓢 : S) extends ModusPonens 𝓢 where
  verum              : 𝓢 ⊫ ⊤
  imply₁ (p q : F)   : 𝓢 ⊫ p ⟶ q ⟶ p
  imply₂ (p q r : F) : 𝓢 ⊫ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r
  conj₁  (p q : F)   : 𝓢 ⊫ p ⋏ q ⟶ p
  conj₂  (p q : F)   : 𝓢 ⊫ p ⋏ q ⟶ q
  conj₃  (p q : F)   : 𝓢 ⊫ p ⟶ q ⟶ p ⋏ q
  disj₁  (p q : F)   : 𝓢 ⊫ p ⟶ p ⋎ q
  disj₂  (p q : F)   : 𝓢 ⊫ q ⟶ p ⋎ q
  disj₃  (p q r : F) : 𝓢 ⊫ (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r

/-- Supplymental -/
class HasEFQ (𝓢 : S) where
  efq (p : F) : 𝓢 ⊫ ⊥ ⟶ p

class HasWeakLEM (𝓢 : S) where
  wlem (p : F) : 𝓢 ⊫ ~p ⋎ ~~p

class HasLEM (𝓢 : S) where
  lem (p : F) : 𝓢 ⊫ p ⋎ ~p

class DNE (𝓢 : S) where
  dne (p : F) : 𝓢 ⊫ ~~p ⟶ p

class Dummett (𝓢 : S) where
  dummett (p q : F) : 𝓢 ⊫ (p ⟶ q) ⋎ (q ⟶ p)

class Peirce (𝓢 : S) where
  peirce (p q : F) : 𝓢 ⊫ ((p ⟶ q) ⟶ p) ⟶ p

/--
  Intuitionistic Propositional Logic.

  Modal companion of `𝐒𝟒`
-/
class Intuitionistic (𝓢 : S) extends Minimal 𝓢, HasEFQ 𝓢

/--
  Propositional Logic for Weak Law of Excluded Middle.

  Modal companion of `𝐒𝟒.𝟐`
-/
class WeakLEM (𝓢 : S) extends Intuitionistic 𝓢, HasWeakLEM 𝓢

/--
  Gödel-Dummett Propositional Logic.

  Modal companion of `𝐒𝟒.𝟑`
-/
class GD (𝓢 : S) extends Intuitionistic 𝓢, Dummett 𝓢

/--
  Classical Propositional Logic.

  Modal companion of `𝐒𝟓`
-/
class Classical (𝓢 : S) extends Minimal 𝓢, DNE 𝓢

end System

end LO
