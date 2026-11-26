module

public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# Cobham's order and weak representability in $\mathsf{R}_0$

Every computable function is weakly representable in $\mathsf{R}_0$ through Cobham's order.

## References

- [Sve08]
-/

@[expose] public section

open scoped FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open ORingStructure

section order

variable {M : Type*} [ORingStructure M] {x y : M}

@[mk_iff]
structure IsRegular (y : M) : Prop where
  zero_le : 0 = y ∨ 0 < y
  add_one_le : ∀ v < y, v + 1 = y ∨ v + 1 < y

def isRegularDef : 𝚺ᴬ₀.Semisentence 1 := .mkSigma “y. 0 ≤ y ∧ ∀ v < y, v + 1 ≤ y”

instance isRegular_defined : 𝚺ᴬ₀-Predicate (IsRegular : M → Prop) via isRegularDef := .mk fun v ↦ by
  simp [isRegularDef, isRegular_iff, Semiformula.Operator.LE.sentence_eq,
    Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq]

def CobhamLE (x y : M) : Prop := (x = y ∨ x < y) ∨ ¬IsRegular y

scoped infix:50 " ≤ᶜ " => CobhamLE

def cobhamLEDef : 𝚺ᴬ₀.Semisentence 2 := .mkSigma “x y. x ≤ y ∨ ¬!isRegularDef y”

instance cobhamLE_defined : 𝚺ᴬ₀-Relation (CobhamLE : M → M → Prop) via cobhamLEDef := .mk fun v ↦ by
  simp [cobhamLEDef, CobhamLE, Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.val,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq]

@[simp, grind .]
lemma cobhamLE_refl (x : M) : x ≤ᶜ x := Or.inl <| Or.inl rfl

def CobhamLT (x y : M) : Prop := x ≤ᶜ y ∧ x ≠ y

scoped infix:50 " <ᶜ " => CobhamLT

def cobhamLTDef : 𝚺ᴬ₀.Semisentence 2 := .mkSigma “x y. !cobhamLEDef x y ∧ x ≠ y”

instance cobhamLT_defined : 𝚺ᴬ₀-Relation (CobhamLT : M → M → Prop) via cobhamLTDef := .mk fun v ↦ by
  simp [cobhamLTDef, CobhamLT]

variable [M↓[ℒₒᵣ] ⊧* 𝗥₀]

@[simp, grind =]
lemma numeral_add_one_of_R0 (n : ℕ) : (numeral n : M) + 1 = numeral (n + 1) := by
  simpa using numeral_add_numeral (M := M) n 1

@[grind .]
lemma isRegular_numeral (n : ℕ) : IsRegular (numeral n : M) := by
  constructor
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · right
      simpa using (numeral_lt_numeral_iff (M := M)).mpr hn
  · intro v hv
    rcases lt_numeral_iff.mp hv with ⟨i, rfl⟩
    simp
    omega

@[grind =]
lemma cobhamLE_numeral_iff {n : ℕ} : x ≤ᶜ numeral n ↔ x = numeral n ∨ x < numeral n := by
  simp [CobhamLE, isRegular_numeral]

lemma exists_eq_numeral_or_numeral_le_of_isRegular (hx : IsRegular x) (k : ℕ) :
    (∃ i < k, x = numeral i) ∨ numeral k = x ∨ numeral k < x := by
  induction k with
  | zero => simpa using hx.zero_le
  | succ k ih =>
    have := hx.add_one_le (numeral k)
    grind

lemma cobhamLE_numeral_or (n : ℕ) : x ≤ᶜ numeral n ∨ numeral n ≤ᶜ x := by
  by_cases hx : IsRegular x
  · rcases exists_eq_numeral_or_numeral_le_of_isRegular hx n with ⟨i, hi, rfl⟩ | h
    · simp [cobhamLE_numeral_iff, hi]
    · exact .inr <| .inl h
  · exact .inr <| .inr hx

lemma eq_numeral_of_cobhamLE_numeral {n : ℕ} (h : x ≤ᶜ numeral n) :
    ∃ i ≤ n, x = numeral i := by
  rcases cobhamLE_numeral_iff.mp h with rfl | h
  · use n
  · rcases lt_numeral_iff.mp h with ⟨i, rfl⟩
    use i, i.isLt.le

lemma cobhamLE_numeral_of_le {k q : ℕ} {w : M} (hkq : k ≤ q) (h : numeral q ≤ᶜ w) :
    numeral k ≤ᶜ w := by
  by_cases hw : IsRegular w
  · rcases exists_eq_numeral_or_numeral_le_of_isRegular hw k with ⟨i, hi, rfl⟩ | h'
    · simp [CobhamLE, hw] at h
      omega
    · exact Or.inl h'
  · exact Or.inr hw

@[simp, grind =]
lemma numeral_cobhamLE_numeral_iff {k n : ℕ} : (numeral k : M) ≤ᶜ numeral n ↔ k ≤ n := by
  simp [cobhamLE_numeral_iff]
  omega

@[grind =]
lemma cobhamLT_numeral_iff {n : ℕ} : x <ᶜ numeral n ↔ x < numeral n := by
  have := not_numeral_lt_self (M := M) n
  grind [CobhamLT]

lemma cobhamLT_numeral_iff_exists {n : ℕ} : x <ᶜ numeral n ↔ ∃ i < n, x = numeral i := by
  simp [cobhamLT_numeral_iff, lt_numeral_iff, Fin.exists_iff]

end order

section representation

def cobhamComparison (φ : ArithmeticSemisentence 3) : ArithmeticSemisentence 2 :=
  “x y. ∃ w, !cobhamLEDef y w ∧ (∃ v, !cobhamLEDef v w ∧ !φ x y v) ∧
    ∀ z u, !cobhamLEDef z w → !cobhamLEDef u w → !φ x z u → y = z”

variable {M : Type*} [ORingStructure M] {φ : ArithmeticSemisentence 3}

@[simp]
lemma eval_cobhamComparison {x y : M} :
    M ⊧/![x, y] (cobhamComparison φ) ↔ ∃ w, y ≤ᶜ w ∧
      (∃ v, v ≤ᶜ w ∧ M ⊧/![x, y, v] φ) ∧
      ∀ z u, z ≤ᶜ w → u ≤ᶜ w → M ⊧/![x, z, u] φ → y = z := by
  simp [cobhamComparison]

variable [M↓[ℒₒᵣ] ⊧* 𝗥₀]

lemma eval_numeral_iff_of_deltaZero (hφ₀ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ) (n i j : ℕ) :
    M ⊧/![numeral n, numeral i, numeral j] φ ↔ ℕ ⊧/![n, i, j] φ := by
  have e : (numeral ∘ ![n, i, j] : Fin 3 → M) = ![numeral n, numeral i, numeral j] := by
    funext x
    match x with | 0 | 1 | 2 => rfl
  constructor
  · intro h
    by_contra h'
    have := bold_sigma_one_completeness' (M := M) (σ := ∼φ) (by simpa using hφ₀.of_zero)
      (bv := ![n, i, j]) (by simpa using h')
    exact absurd h (by simpa [e] using this)
  · intro h
    simpa [e] using bold_sigma_one_completeness' (M := M) hφ₀.of_zero h

variable {f : ℕ → ℕ}

section

variable (hφ₀ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ) (hφ : ∀ n m, m = f n ↔ ∃ k, ℕ ⊧/![n, m, k] φ)
include hφ₀ hφ

lemma eval_cobhamComparison_numeral_iff (n : ℕ) (y : M) :
    M ⊧/![numeral n, y] (cobhamComparison φ) ↔ y = numeral (f n) := by
  obtain ⟨k, hk⟩ := (hφ n (f n)).mp rfl
  have key : ∀ i j, M ⊧/![numeral n, numeral i, numeral j] φ → i = f n := fun i j h ↦
    (hφ n i).mpr ⟨j, (eval_numeral_iff_of_deltaZero hφ₀ n i j).mp h⟩
  have hkM : M ⊧/![numeral n, numeral (f n), numeral k] φ :=
    (eval_numeral_iff_of_deltaZero hφ₀ n (f n) k).mpr hk
  rw [eval_cobhamComparison]
  constructor
  · rintro ⟨w, hyw, ⟨v, hvw, hv⟩, huniq⟩
    rcases cobhamLE_numeral_or (x := w) (max (f n) k) with hw | hw
    · grind [eq_numeral_of_cobhamLE_numeral]
    · exact huniq _ _ (cobhamLE_numeral_of_le (le_max_left _ _) hw)
        (cobhamLE_numeral_of_le (le_max_right _ _) hw) hkM
  · rintro rfl
    use numeral (max (f n) k)
    and_intros
    · simp
    · use numeral k, by simp
    · grind [eq_numeral_of_cobhamLE_numeral]

end

lemma hierarchy_codeOfPartrec'_graph (f : ℕ → ℕ) : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1
    (codeOfPartrec' fun v : List.Vector ℕ 1 ↦ Part.some (f (v.get 0))) := by
  simp [codeOfPartrec']

noncomputable def deltaZeroGraph (f : ℕ → ℕ) : ArithmeticSemisentence 3 :=
  “x y v. !(hierarchy_codeOfPartrec'_graph f).prenex.sigmaInv.val v y x”

@[simp]
lemma deltaZeroGraph_hierarchy (f : ℕ → ℕ) : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 (deltaZeroGraph f) := by
  simp [deltaZeroGraph]

lemma deltaZeroGraph_spec (hf : Computable f) (n m : ℕ) :
    m = f n ↔ ∃ k, ℕ ⊧/![n, m, k] (deltaZeroGraph f) := by
  have hF : Nat.Partrec' fun v : List.Vector ℕ 1 ↦ Part.some (f (v.get 0)) :=
    Nat.Partrec'.of_part <| hf.comp (Primrec.to_comp (by primrec))
  have h := hierarchy_codeOfPartrec'_graph f
  have := (codeOfPartrec'_spec hF (y := m) (v := ![n])).symm.trans
    (((Bounding.Prenex.models_exists_prenex.{_, 0} (Γ' := 𝚺) h).choose_spec ℕ (m :> ![n])
      Empty.elim).trans (h.prenex.models_sigmaInv _))
  simpa [deltaZeroGraph] using this

noncomputable def cobhamRepresentation (f : ℕ → ℕ) : ArithmeticSemisentence 2 :=
  cobhamComparison (deltaZeroGraph f)

theorem cobhamRepresentation_spec (hf : Computable f) (n : ℕ) :
    𝗥₀ ⊢ “∀ y, !(cobhamRepresentation f) ↑n y ↔ y = ↑(f n)” := by
  apply complete.{0}
  intro M _ _
  simpa [models_iff, cobhamRepresentation, -eval_cobhamComparison]
    using eval_cobhamComparison_numeral_iff (M := M) (deltaZeroGraph_hierarchy f)
      (deltaZeroGraph_spec hf) n

end representation

end FFL.FirstOrder.Arithmetic
