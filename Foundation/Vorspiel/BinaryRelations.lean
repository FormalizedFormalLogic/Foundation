import Foundation.Vorspiel.Vorspiel
import Mathlib.Data.Finite.Basic


section

variable {α : Type u} (rel : α → α → Prop)
local infix:50 " ≺ " => rel

-- NOTE: `x ≺ y → x ≺ z → y ≺ z`とする流儀もある
def Euclidean := ∀ ⦃x y z⦄, x ≺ y → x ≺ z → z ≺ y

def Serial := ∀ x, ∃ y, x ≺ y

def Confluent := ∀ ⦃x y z⦄, ((x ≺ y ∧ x ≺ z) → ∃ w, (y ≺ w ∧ z ≺ w))

def Dense := ∀ ⦃x y⦄, x ≺ y → ∃z, x ≺ z ∧ z ≺ y

def Connected := ∀ ⦃x y z⦄, x ≺ y ∧ x ≺ z → y ≺ z ∨ z ≺ y

def Functional := ∀ ⦃x y z⦄, x ≺ y ∧ x ≺ z → y = z

def RightConvergent := ∀ ⦃x y z⦄, x ≺ y ∧ x ≺ z → y ≺ z ∨ z ≺ y ∨ y = z

def Coreflexive := ∀ ⦃x y⦄, x ≺ y → x = y

def Equality := ∀ ⦃x y⦄, x ≺ y ↔ x = y

def Antisymmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y

def Isolated := ∀ ⦃x y⦄, ¬(x ≺ y)

def Assymetric := ∀ ⦃x y⦄, (x ≺ y) → ¬(y ≺ x)

def Universal := ∀ ⦃x y⦄, x ≺ y

abbrev ConverseWellFounded := WellFounded $ flip (· ≺ ·)

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

lemma corefl_of_refl_assym_eucl (hRefl : Reflexive rel) (hAntisymm : Antisymmetric rel) (hEucl : Euclidean rel) : Coreflexive rel := by
  intro x y Rxy;
  have Ryx := hEucl (hRefl x) Rxy;
  exact hAntisymm Rxy Ryx;

lemma equality_of_refl_corefl (hRefl : Reflexive rel) (hCorefl : Coreflexive rel) : Equality rel := by
  intro x y;
  constructor;
  . apply hCorefl;
  . rintro rfl; apply hRefl;

lemma equality_of_refl_assym_eucl (hRefl : Reflexive rel) (hAntisymm : Antisymmetric rel) (hEucl : Euclidean rel) : Equality rel := by
  apply equality_of_refl_corefl;
  . assumption;
  . exact corefl_of_refl_assym_eucl hRefl hAntisymm hEucl;

lemma refl_of_equality (h : Equality rel) : Reflexive rel := by
  intro x;
  exact h.mpr rfl;

lemma corefl_of_equality (h : Equality rel) : Coreflexive rel := by
  intro x y Rxy;
  apply h.mp Rxy;

lemma irreflexive_of_assymetric (hAssym : Assymetric rel) : Irreflexive rel := by
  intro x Rxx;
  have := hAssym Rxx;
  contradiction;

lemma refl_of_universal (h : Universal rel) : Reflexive rel := by
  intro x; exact @h x x;

lemma eucl_of_universal (h : Universal rel) : Euclidean rel := by
  rintro x y z _ _; exact @h z y;


section ConverseWellFounded

lemma ConverseWellFounded.iff_has_max : ConverseWellFounded r ↔ (∀ (s : Set α), Set.Nonempty s → ∃ m ∈ s, ∀ x ∈ s, ¬(r m x)) := by
  simp [ConverseWellFounded, WellFounded.wellFounded_iff_has_min, flip]

lemma Finite.converseWellFounded_of_trans_irrefl [Finite α] [IsTrans α rel] [IsIrrefl α rel] : ConverseWellFounded rel := by
  apply @Finite.wellFounded_of_trans_of_irrefl _ _ _
    ⟨by intro a b c rba rcb; exact IsTrans.trans c b a rcb rba⟩
    ⟨by simp [flip, IsIrrefl.irrefl]⟩

lemma Finite.converseWellFounded_of_trans_irrefl'
    (hFinite : Finite α) (hTrans : Transitive rel) (hIrrefl : Irreflexive rel) : ConverseWellFounded rel :=
  @Finite.wellFounded_of_trans_of_irrefl _ _ _
    ⟨by simp [flip]; intro a b c ba cb; exact hTrans cb ba;⟩
    ⟨by simp [flip]; exact hIrrefl⟩

end ConverseWellFounded


@[simp]
lemma WellFounded.trivial_wellfounded : WellFounded (α := α) (λ _ _ => False) := by
  constructor; intro _;
  constructor; intro _ _;
  contradiction;

def Relation.IrreflGen (R : α → α → Prop) := λ x y => x ≠ y ∧ R x y


abbrev WeaklyConverseWellFounded (R : α → α → Prop) := ConverseWellFounded (Relation.IrreflGen R)
alias WCWF := WeaklyConverseWellFounded


section

lemma dependent_choice {R : α → α → Prop} (h : ∃ s : Set α, s.Nonempty ∧ ∀ a ∈ s, ∃ b ∈ s, R a b)
  : ∃ f : ℕ → α, ∀ x, R (f x) (f (x + 1)) := by
  obtain ⟨s, ⟨x, hx⟩, h'⟩ := h;
  choose! f hfs hR using h';
  use fun n ↦ f^[n] x;
  intro n;
  simp only [Function.iterate_succ'];
  refine hR (f^[n] x) ?a;
  induction n with
  | zero => simpa;
  | succ n ih => simp only [Function.iterate_succ']; apply hfs _ ih;

lemma Finite.exists_ne_map_eq_of_infinite_lt {α β} [LinearOrder α] [Infinite α] [Finite β] (f : α → β)
  : ∃ x y : α, (x < y) ∧ f x = f y
  := by
    obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite f;
    rcases lt_trichotomy i j with (hij | _ | hij);
    . use i, j;
    . contradiction;
    . use j, i; simp [hij, e];

lemma antisymm_of_WCWF {R : α → α → Prop} : WCWF R → Antisymmetric R := by
  contrapose;
  simp [Antisymmetric];
  intro x y Rxy Ryz hxy;
  apply ConverseWellFounded.iff_has_max.not.mpr;
  push_neg;
  use {x, y};
  constructor;
  . simp;
  . intro z hz;
    by_cases z = x;
    . use y; simp_all [Relation.IrreflGen];
    . use x; simp_all [Relation.IrreflGen];

lemma WCWF_of_finite_trans_antisymm {R : α → α → Prop} (hFin : Finite α) (R_trans : Transitive R)
  : Antisymmetric R → WCWF R := by
    contrapose;
    intro hWCWF;
    replace hWCWF := ConverseWellFounded.iff_has_max.not.mp hWCWF;
    push_neg at hWCWF;
    obtain ⟨f, hf⟩ := dependent_choice hWCWF; clear hWCWF;
    simp [Relation.IrreflGen] at hf;

    simp [Antisymmetric];
    obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite_lt f;
    use (f i), (f (i + 1));
    have ⟨hi₁, hi₂⟩ := hf i;
    refine ⟨(by assumption), ?_, (by assumption)⟩;

    have : i + 1 < j := lt_iff_le_and_ne.mpr ⟨by omega, by aesop⟩;
    have H : ∀ i j, i < j → R (f i) (f j) := by
      intro i j hij
      induction hij with
      | refl => exact hf i |>.2;
      | step _ ih => exact R_trans ih $ hf _ |>.2;
    have := H (i + 1) j this;
    simpa [e];

end

end
