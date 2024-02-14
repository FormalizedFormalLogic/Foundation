import Mathlib.Init.Logic
import Mathlib.Data.Finite.Basic
import Mathlib.Tactic.Existsi

section

variable {α : Type u} (rel : α → α → Prop)
local infix:50 " ≺ " => rel

def Euclidean := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ → w₁ ≺ w₃ → (w₂ ≺ w₃)

def Serial := ∀w₁, ∃w₂, w₁ ≺ w₂

def Confluent := ∀ ⦃w₁ w₂ w₃⦄, ((w₁ ≺ w₂ ∧ w₂ ≺ w₃) → ∃ w₄, w₂ ≺ w₄ ∧ w₃ ≺ w₄)

def Dense := ∀ ⦃w₁ w₂⦄, w₁ ≺ w₂ → ∃w₃, w₁ ≺ w₃ ∧ w₃ ≺ w₂

def Functional := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ ∧ w₁ ≺ w₃ → w₂ = w₃

def RightConvergent := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ ∧ w₁ ≺ w₃ → w₂ ≺ w₃ ∨ w₃ ≺ w₂ ∨ w₂ = w₃

abbrev ConverseWellFounded := WellFounded $ flip (· ≺ ·)

end

section

variable {α : Type u}
variable {rel : α → α → Prop}

lemma serial_of_refl (hRefl : Reflexive rel) : Serial rel := by
  rintro w;
  existsi w;
  exact hRefl w;

lemma trans_of_symm_eucl (hSymm : Symmetric rel) (hEucl : Euclidean rel) : Transitive rel := by
  rintro w₁ w₂ w₃ r₁₂ r₂₃;
  exact hEucl (hSymm r₁₂) r₂₃;

lemma symm_of_refl_eucl (hRefl : Reflexive rel) (hEucl : Euclidean rel) : Symmetric rel := by
  intro w₁ w₂ r₁₂;
  exact hEucl r₁₂ (hRefl w₁);

lemma trans_of_refl_eucl (hRefl : Reflexive rel) (hEucl : Euclidean rel) : Transitive rel := by
  have hSymm := symm_of_refl_eucl hRefl hEucl;
  exact trans_of_symm_eucl hSymm hEucl;

lemma refl_of_serial_symm_eucl (hSer : Serial rel) (hSymm : Symmetric rel) (hEucl : Euclidean rel) : Reflexive rel := by
  rintro w₁;
  obtain ⟨w₂, r₁₂⟩ := hSer w₁;
  have r₂₁ := hSymm r₁₂;
  exact trans_of_symm_eucl hSymm hEucl r₁₂ r₂₁;

lemma eucl_of_symm_trans (hSymm : Symmetric rel) (hTrans : Transitive rel) : Euclidean rel := by
  intro w₁ w₂ w₃ r₁₂ r₁₃;
  have r₂₁ := hSymm r₁₂;
  exact hTrans r₂₁ r₁₃;

section ConverseWellFounded

lemma ConverseWellFounded.iff_has_max : ConverseWellFounded r ↔ (∀ (s : Set α), Set.Nonempty s → ∃ m ∈ s, ∀ x ∈ s, ¬(r m x)) := by
  simp [ConverseWellFounded, WellFounded.wellFounded_iff_has_min, flip]

variable [Finite α]

lemma Finite.converseWellFounded_of_trans_irrefl [IsTrans α rel] [IsIrrefl α rel] : ConverseWellFounded rel := by
  apply @Finite.wellFounded_of_trans_of_irrefl _ _ _
    ⟨by intro a b c rba rcb; exact IsTrans.trans c b a rcb rba⟩
    ⟨by simp [flip, IsIrrefl.irrefl]⟩

end ConverseWellFounded

end
