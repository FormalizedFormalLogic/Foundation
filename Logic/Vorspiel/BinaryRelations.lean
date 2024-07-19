import Mathlib.Init.Logic
import Mathlib.Data.Finite.Basic
import Mathlib.Tactic.Existsi

section

variable {α : Type u} (rel : α → α → Prop)
local infix:50 " ≺ " => rel

-- NOTE: `w₁ ≺ w₂ → w₁ ≺ w₃ → w₂ ≺ w₃`とする流儀もある
def Euclidean := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ → w₁ ≺ w₃ → w₃ ≺ w₂

def Serial := ∀ w₁, ∃ w₂, w₁ ≺ w₂

def Confluent := ∀ ⦃w₁ w₂ w₃⦄, ((w₁ ≺ w₂ ∧ w₁ ≺ w₃) → ∃ w₄, w₂ ≺ w₄ ∧ w₃ ≺ w₄)

def Dense := ∀ ⦃w₁ w₂⦄, w₁ ≺ w₂ → ∃w₃, w₁ ≺ w₃ ∧ w₃ ≺ w₂

def Connected := ∀ ⦃x y z⦄, x ≺ y ∧ x ≺ z → y ≺ z ∨ z ≺ y

def Functional := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ ∧ w₁ ≺ w₃ → w₂ = w₃

def RightConvergent := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ ∧ w₁ ≺ w₃ → w₂ ≺ w₃ ∨ w₃ ≺ w₂ ∨ w₂ = w₃

def Extensive := ∀ ⦃x y⦄, x ≺ y → x = y

def Antisymmetric := ∀ ⦃w₁ w₂⦄, w₁ ≺ w₂ → w₂ ≺ w₁ → w₁ = w₂

def Isolated := ∀ ⦃x y⦄, ¬(x ≺ y)

def Assymetric := ∀ ⦃x y⦄, (x ≺ y) → ¬(y ≺ x)

def Universal := ∀ ⦃x y⦄, x ≺ y

abbrev ConverseWellFounded := WellFounded $ flip (· ≺ ·)

end

section

variable {α : Type u}
variable {rel : α → α → Prop}
variable (hRefl : Reflexive rel) -- T
         (hSymm : Symmetric rel) -- B
         (hSerial : Serial rel) -- D
         (hTrans : Transitive rel) -- 4
         (hEucl : Euclidean rel) -- 5

-- T → D
lemma serial_of_refl : Serial rel := by
  rintro w;
  existsi w;
  exact hRefl w;

-- B + 4 → 5
lemma eucl_of_symm_trans : Euclidean rel := by
  intro w₁ w₂ w₃ r₁₂ r₁₃;
  have r₂₁ := hSymm r₁₂;
  exact hSymm $ hTrans r₂₁ r₁₃;

-- B + 5 → 4
lemma trans_of_symm_eucl : Transitive rel := by
  rintro w₁ w₂ w₃ r₁₂ r₂₃;
  exact hSymm $ hEucl (hSymm r₁₂) r₂₃;

-- T + 5 → B
lemma symm_of_refl_eucl : Symmetric rel := by
  intro w₁ w₂ r₁₂;
  exact hEucl (hRefl w₁) r₁₂;

-- T + 5 → 4
lemma trans_of_refl_eucl : Transitive rel := by
  have hSymm := symm_of_refl_eucl hRefl hEucl;
  exact trans_of_symm_eucl hSymm hEucl;

-- B + D + 5 → T
lemma refl_of_symm_serial_eucl : Reflexive rel := by
  rintro w₁;
  obtain ⟨w₂, r₁₂⟩ := hSerial w₁;
  have r₂₁ := hSymm r₁₂;
  exact trans_of_symm_eucl hSymm hEucl r₁₂ r₂₁;


section ConverseWellFounded

lemma ConverseWellFounded.iff_has_max : ConverseWellFounded r ↔ (∀ (s : Set α), Set.Nonempty s → ∃ m ∈ s, ∀ x ∈ s, ¬(r m x)) := by
  simp [ConverseWellFounded, WellFounded.wellFounded_iff_has_min, flip]

lemma Finite.converseWellFounded_of_trans_irrefl [Finite α] [IsTrans α rel] [IsIrrefl α rel] : ConverseWellFounded rel := by
  apply @Finite.wellFounded_of_trans_of_irrefl _ _ _
    ⟨by intro a b c rba rcb; exact IsTrans.trans c b a rcb rba⟩
    ⟨by simp [flip, IsIrrefl.irrefl]⟩

lemma Finite.converseWellFounded_of_trans_irrefl' (hFinite : Finite α) (hTrans : Transitive rel) (hIrrefl : Irreflexive rel) : ConverseWellFounded rel :=
  @Finite.wellFounded_of_trans_of_irrefl _ _ _
    ⟨by simp [flip]; intro a b c ba cb; exact hTrans cb ba;⟩
    ⟨by simp [flip]; exact hIrrefl⟩

end ConverseWellFounded


lemma extensive_of_reflex_antisymm_eucl (hRefl : Reflexive rel) (hAntisymm : Antisymmetric rel) (hEucl : Euclidean rel) : Extensive rel := by
  intro x y rxy;
  have rxx := hRefl x;
  exact hAntisymm rxy (hEucl rxx rxy);


lemma irreflexive_of_assymetric (hAssym : Assymetric rel) : Irreflexive rel := by
  intro x Rxx;
  have := hAssym Rxx;
  contradiction;


lemma refl_of_universal (h : Universal rel) : Reflexive rel := by
  intro x; exact @h x x;

lemma eucl_of_universal (h : Universal rel) : Euclidean rel := by
  rintro x y z _ _; exact @h z y;

end
