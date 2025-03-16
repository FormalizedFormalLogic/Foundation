import Foundation.Vorspiel.Vorspiel
import Mathlib.Data.Fintype.Pigeonhole

section

variable {α : Sort*} (rel : α → α → Prop)
local infix:50 " ≺ " => rel

-- NOTE: `x ≺ y → x ≺ z → y ≺ z`とする流儀もある
def Euclidean := ∀ ⦃x y z⦄, x ≺ y → x ≺ z → z ≺ y
class IsEuclidean (α : Sort*) (r : α → α → Prop) : Prop where eucl : Euclidean r

def Serial := ∀ x, ∃ y, x ≺ y
class IsSerial (α : Sort*) (r : α → α → Prop) : Prop where serial : ∀ x, ∃ y, r x y

def Confluent := ∀ ⦃x y z⦄, ((x ≺ y ∧ x ≺ z) → ∃ w, (y ≺ w ∧ z ≺ w))
class IsConfluent (α : Sort*) (r : α → α → Prop) : Prop where confl : Confluent r

def WeakConfluent := ∀ ⦃x y z⦄, (x ≺ y ∧ x ≺ z ∧ y ≠ z) → (∃ w, y ≺ w ∧ z ≺ w)
class IsWeakConfluent (α : Sort*) (r : α → α → Prop) : Prop where weak_confl : WeakConfluent r

def Dense := ∀ ⦃x y⦄, x ≺ y → ∃z, x ≺ z ∧ z ≺ y

def Connected := ∀ ⦃x y z⦄, (x ≺ y ∧ x ≺ z) → (y ≺ z ∨ z ≺ y)
class IsConnected (α : Sort*) (r : α → α → Prop) : Prop where connected : Connected r

def WeakConnected := ∀ ⦃x y z⦄, (x ≺ y ∧ x ≺ z ∧ y ≠ z) → (y ≺ z ∨ z ≺ y)
class IsWeakConnected (α : Sort*) (r : α → α → Prop) : Prop where weak_connected : WeakConnected r

def Functional := ∀ ⦃x y z⦄, x ≺ y ∧ x ≺ z → y = z

def RightConvergent := ∀ ⦃x y z⦄, x ≺ y ∧ x ≺ z → y ≺ z ∨ z ≺ y ∨ y = z

def Coreflexive := ∀ ⦃x y⦄, x ≺ y → x = y
class IsCoreflexive (α : Sort*) (r : α → α → Prop) : Prop where corefl : Coreflexive r

def Equality := ∀ ⦃x y⦄, x ≺ y ↔ x = y
class IsEquality (α : Sort*) (r : α → α → Prop) : Prop where equal : Equality r

def Isolated := ∀ ⦃x y⦄, ¬(x ≺ y)
class IsIsolated (α : Sort*) (r : α → α → Prop) : Prop where isolated : Isolated r

def Asymmetric := ∀ ⦃x y⦄, (x ≺ y) → ¬(y ≺ x)

def Universal := ∀ ⦃x y⦄, x ≺ y
class IsUniversal (α : Sort*) (r : α → α → Prop) : Prop where universal : Universal r

attribute [mk_iff]
  IsRefl
  IsSerial
  IsSymm
  IsTrans
  IsEuclidean
  IsConfluent
  IsWeakConfluent
  IsConnected
  IsWeakConnected
  IsCoreflexive
  IsEquality
  IsUniversal
  IsIsolated
  IsPreorder
  IsEquiv
  IsAsymm
  IsAntisymm

end


section

variable {α : Type u}
variable {rel : α → α → Prop}


lemma serial_of_refl (hRefl : Reflexive rel) : Serial rel := by
  rintro w;
  existsi w;
  exact hRefl w;

lemma eucl_of_symm_trans (hSymm : Symmetric rel) (hTrans : Transitive rel) : Euclidean rel := by
  intro x y z Rxy Rxz;
  have Ryx := hSymm Rxy;
  exact hSymm $ hTrans Ryx Rxz;

lemma trans_of_symm_eucl (hSymm : Symmetric rel) (hEucl : Euclidean rel) : Transitive rel := by
  rintro x y z Rxy Ryz;
  exact hSymm $ hEucl (hSymm Rxy) Ryz;

lemma symm_of_refl_eucl (hRefl : Reflexive rel) (hEucl : Euclidean rel) : Symmetric rel := by
  intro x y Rxy;
  exact hEucl (hRefl x) Rxy;

lemma trans_of_refl_eucl (hRefl : Reflexive rel) (hEucl : Euclidean rel) : Transitive rel := by
  have hSymm := symm_of_refl_eucl hRefl hEucl;
  exact trans_of_symm_eucl hSymm hEucl;

lemma refl_of_symm_serial_eucl (hSymm : Symmetric rel) (hSerial : Serial rel) (hEucl : Euclidean rel) : Reflexive rel := by
  rintro x;
  obtain ⟨y, Rxy⟩ := hSerial x;
  have Ryx := hSymm Rxy;
  exact trans_of_symm_eucl hSymm hEucl Rxy Ryx;

lemma corefl_of_refl_assym_eucl (hRefl : Reflexive rel) (hAntisymm : AntiSymmetric rel) (hEucl : Euclidean rel) : Coreflexive rel := by
  intro x y Rxy;
  have Ryx := hEucl (hRefl x) Rxy;
  exact hAntisymm Rxy Ryx;

lemma equality_of_refl_corefl (hRefl : Reflexive rel) (hCorefl : Coreflexive rel) : Equality rel := by
  intro x y;
  constructor;
  . apply hCorefl;
  . rintro rfl; apply hRefl;

lemma equality_of_refl_assym_eucl (hRefl : Reflexive rel) (hAntisymm : AntiSymmetric rel) (hEucl : Euclidean rel) : Equality rel := by
  apply equality_of_refl_corefl;
  . assumption;
  . exact corefl_of_refl_assym_eucl hRefl hAntisymm hEucl;

lemma refl_of_equality (h : Equality rel) : Reflexive rel := by
  intro x;
  exact h.mpr rfl;

lemma corefl_of_equality (h : Equality rel) : Coreflexive rel := by
  intro x y Rxy;
  apply h.mp Rxy;

lemma irreflexive_of_assymetric (hAssym : Asymmetric rel) : Irreflexive rel := by
  intro x Rxx;
  have := hAssym Rxx;
  contradiction;

lemma refl_of_universal (h : Universal rel) : Reflexive rel := by
  intro x; exact @h x x;

lemma eucl_of_universal (h : Universal rel) : Euclidean rel := by
  rintro x y z _ _; exact @h z y;

lemma confluent_of_refl_connected (hRefl : Reflexive rel) (hConfl : Connected rel) : Confluent rel := by
  rintro x y z ⟨Rxy, Rxz⟩;
  rcases @hConfl x y z ⟨Rxy, Rxz⟩ with (Ryz | Rzy);
  . use z;
    constructor;
    . assumption;
    . apply hRefl;
  . use y;
    constructor;
    . apply hRefl;
    . assumption;

/-
@[simp]
lemma WellFounded.trivial_wellfounded : WellFounded (α := α) (λ _ _ => False) := by
  constructor; intro _;
  constructor; intro _ _;
  contradiction;
-/

end
