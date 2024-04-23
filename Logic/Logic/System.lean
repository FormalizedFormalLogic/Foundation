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

infix:45 " ⊢ " => System.Prf

namespace System

variable {S : Type*} {F : Type*} [System S F]

section

variable (𝓢 : S)

def Provable (f : F) : Prop := Nonempty (𝓢 ⊢ f)

def Unprovable (f : F) : Prop := IsEmpty (𝓢 ⊢ f)

infix:45 " ⊢! " => Provable

infix:45 " ⊬! " => Unprovable

def PrfSet (s : Set F) : Type _ := {f : F} → f ∈ s → 𝓢 ⊢ f

def ProvableSet (s : Set F) : Prop := ∀ f ∈ s, 𝓢 ⊢! f

infix:45 " ⊢* " => PrfSet

infix:45 " ⊢*! " => ProvableSet

def theory : Set F := {f | 𝓢 ⊢! f}

end

lemma not_provable_iff_unprovable {𝓢 : S} {f : F} :
    ¬𝓢 ⊢! f ↔ 𝓢 ⊬! f := by simp [Provable, Unprovable]

lemma not_unprovable_iff_provable {𝓢 : S} {f : F} :
    ¬𝓢 ⊬! f ↔ 𝓢 ⊢! f := by simp [Provable, Unprovable]

instance : Preorder S where
  le := fun 𝓢 𝓢' ↦ theory 𝓢 ⊆ theory 𝓢'
  le_refl := fun 𝓢 ↦ Set.Subset.refl _
  le_trans := fun _ _ _ h₁ h₂ ↦ Set.Subset.trans h₁ h₂

lemma le_iff {𝓢 𝓢' : S} : 𝓢 ≤ 𝓢' ↔ (∀ {f}, 𝓢 ⊢! f → 𝓢' ⊢! f) :=
  ⟨fun h _ hf ↦ h hf, fun h _ hf ↦ h hf⟩

lemma lt_iff {𝓢 𝓢' : S} : 𝓢 < 𝓢' ↔ (∀ {f}, 𝓢 ⊢! f → 𝓢' ⊢! f) ∧ (∃ f, 𝓢 ⊬! f ∧ 𝓢' ⊢! f) := by
  simp [lt_iff_le_not_le, le_iff]; intro _
  exact exists_congr (fun _ ↦ by simp [and_comm, not_provable_iff_unprovable])

lemma weakening {𝓢 𝓢' : S} (h : 𝓢 ≤ 𝓢') {f} : 𝓢 ⊢! f → 𝓢' ⊢! f := le_iff.mp h

instance : Setoid S where
  r := fun 𝓢 𝓢' ↦ theory 𝓢 = theory 𝓢'
  iseqv := { refl := fun _ ↦ rfl, symm := Eq.symm, trans := Eq.trans }

lemma equiv_def {𝓢 𝓢' : S} : 𝓢 ≈ 𝓢' ↔ theory 𝓢 = theory 𝓢' := iff_of_eq rfl

lemma equiv_iff {𝓢 𝓢' : S} : 𝓢 ≈ 𝓢' ↔ (∀ f, 𝓢 ⊢! f ↔ 𝓢' ⊢! f) := by simp [equiv_def, Set.ext_iff, theory]

lemma le_antisymm {𝓢 𝓢' : S} (h : 𝓢 ≤ 𝓢') (h' : 𝓢' ≤ 𝓢) : 𝓢 ≈ 𝓢' :=
  equiv_iff.mpr (fun _ ↦ ⟨fun hf ↦ le_iff.mp h hf, fun hf ↦ le_iff.mp h' hf⟩)

def Inconsistent (𝓢 : S) : Prop := ∀ f, 𝓢 ⊢! f

class Consistent (𝓢 : S) : Prop where
  not_inconsistent : ¬Inconsistent 𝓢

lemma inconsistent_def {𝓢 : S} :
    Inconsistent 𝓢 ↔ ∀ f, 𝓢 ⊢! f := by simp [Inconsistent]

lemma not_inconsistent_iff_consistent {𝓢 : S} :
    ¬Inconsistent 𝓢 ↔ Consistent 𝓢 :=
  ⟨fun h ↦ ⟨h⟩, by rintro ⟨h⟩; exact h⟩

lemma not_consistent_iff_inconsistent {𝓢 : S} :
    ¬Consistent 𝓢 ↔ Inconsistent 𝓢 := by simp [←not_inconsistent_iff_consistent]

lemma consistent_iff_exists_unprovable {𝓢 : S} :
    Consistent 𝓢 ↔ ∃ f, 𝓢 ⊬! f := by
  simp [←not_inconsistent_iff_consistent, inconsistent_def, not_provable_iff_unprovable]

alias ⟨Consistent.exists_unprovable, _⟩ := consistent_iff_exists_unprovable

lemma Consistent.of_unprovable {𝓢 : S} {f} (h : 𝓢 ⊬! f) : Consistent 𝓢 :=
  ⟨fun hp ↦ not_provable_iff_unprovable.mpr h (hp f)⟩

structure Translation {S S' F F'} [System S F] [System S' F'] (𝓢 : S) (𝓢' : S') where
  toFun : F → F'
  prf {f} : 𝓢 ⊢ f → 𝓢' ⊢ toFun f

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

def Complete : Prop := ∀ f, 𝓢 ⊢! f ∨ 𝓢 ⊢! ~f

def Undecidable (f : F) : Prop := 𝓢 ⊬! f ∧ 𝓢 ⊬! ~f

class Axiom where
  axm : Set F → S
  ofAxm (T : Set F) : axm T ⊢* T
  weakening' {T U : Set F} : T ⊆ U → axm T ≤ axm U

end System

section

variable {S : Type*} {F : Type*} [LogicalConnective F] [System S F] {M : Type*} [Semantics M F]

class Sound (𝓢 : S) (𝓜 : M) : Prop where
  sound : ∀ {f : F}, 𝓢 ⊢! f → 𝓜 ⊧ f

class Complete (𝓢 : S) (𝓜 : M) : Prop where
  complete : ∀ {f : F}, 𝓜 ⊧ f → 𝓢 ⊢! f

namespace Sound

section

variable {𝓢 : S} {𝓜 : M} [Sound 𝓢 𝓜]

lemma not_provable_of_countermodel {p : F} (hp : ¬𝓜 ⊧ p) : 𝓢 ⊬! p :=
  System.not_provable_iff_unprovable.mp fun b ↦ hp (Sound.sound b)

lemma consistent_of_meaningful : Semantics.Meaningful 𝓜 → System.Consistent 𝓢 :=
  fun H ↦ ⟨fun h ↦ by rcases H with ⟨f, hf⟩; exact hf (Sound.sound (h f))⟩

lemma consistent_of_model [Semantics.Bot M] : System.Consistent 𝓢 :=
  consistent_of_meaningful (𝓜 := 𝓜) inferInstance

lemma realizeSet_of_prfSet {T : Set F} (b : 𝓢 ⊢*! T) : 𝓜 ⊧* T :=
  ⟨fun _ hf => sound (b _ hf)⟩

end

section

variable [∀ 𝓜 : M, Semantics.Meaningful 𝓜] {𝓢 : S} {T : Set F} [Sound 𝓢 (Semantics.models M T)]

lemma consequence {f : F} : 𝓢 ⊢! f → T ⊨[M] f := sound

lemma consistent_of_satisfiable : Semantics.Satisfiable M T → System.Consistent 𝓢 :=
  fun H ↦ consistent_of_meaningful (Semantics.meaningful_iff_satisfiableSet.mp H)

end

end Sound

namespace Complete

section

variable {𝓢 : S} {𝓜 : M} [Complete 𝓢 𝓜]

lemma meaningful_of_consistent : System.Consistent 𝓢 → Semantics.Meaningful 𝓜 := by
  contrapose; intro h
  simp [Semantics.not_meaningful_iff, System.not_consistent_iff_inconsistent] at h ⊢
  intro f; exact Complete.complete (h f)

end

section

variable [∀ 𝓜 : M, Semantics.Meaningful 𝓜] {𝓢 : S} {T : Set F} [Complete 𝓢 (Semantics.models M T)]

lemma consequence {f : F} : T ⊨[M] f → 𝓢 ⊢! f := complete

lemma consistent_of_satisfiable : System.Consistent 𝓢 → Semantics.Satisfiable M T :=
  fun H ↦ Semantics.meaningful_iff_satisfiableSet.mpr (meaningful_of_consistent H)

end

end Complete

end

namespace System

variable {S : Type*} {F : Type*} [System S F] [LogicalConnective F]

class ModusPonens (𝓢 : S) where
  mdp {p q : F} : 𝓢 ⊢ p ⟶ q → 𝓢 ⊢ p → 𝓢 ⊢ q

class Minimal (𝓢 : S) extends ModusPonens 𝓢 where
  verum              : 𝓢 ⊢ ⊤
  imply₁ (p q : F)   : 𝓢 ⊢ p ⟶ q ⟶ p
  imply₂ (p q r : F) : 𝓢 ⊢ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r
  conj₁  (p q : F)   : 𝓢 ⊢ p ⋏ q ⟶ p
  conj₂  (p q : F)   : 𝓢 ⊢ p ⋏ q ⟶ q
  conj₃  (p q : F)   : 𝓢 ⊢ p ⟶ q ⟶ p ⋏ q
  disj₁  (p q : F)   : 𝓢 ⊢ p ⟶ p ⋎ q
  disj₂  (p q : F)   : 𝓢 ⊢ q ⟶ p ⋎ q
  disj₃  (p q r : F) : 𝓢 ⊢ (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r

/-- Supplymental -/
class HasEFQ (𝓢 : S) where
  efq (p : F) : 𝓢 ⊢ ⊥ ⟶ p

class HasWeakLEM (𝓢 : S) where
  wlem (p : F) : 𝓢 ⊢ ~p ⋎ ~~p

class HasLEM (𝓢 : S) where
  lem (p : F) : 𝓢 ⊢ p ⋎ ~p

class DNE (𝓢 : S) where
  dne (p : F) : 𝓢 ⊢ ~~p ⟶ p

class Dummett (𝓢 : S) where
  dummett (p q : F) : 𝓢 ⊢ (p ⟶ q) ⋎ (q ⟶ p)

class Peirce (𝓢 : S) where
  peirce (p q : F) : 𝓢 ⊢ ((p ⟶ q) ⟶ p) ⟶ p

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
