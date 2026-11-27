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

variable {V : Type*} [ORingStructure V] {x y : V}

@[mk_iff]
structure IsRegular (y : V) : Prop where
  zero_le : 0 = y ∨ 0 < y
  add_one_le : ∀ v < y, v + 1 = y ∨ v + 1 < y

def isRegularDef : 𝚺ᴬ₀.Semisentence 1 := .mkSigma “y. 0 ≤ y ∧ ∀ v < y, v + 1 ≤ y”

instance isRegular_defined : 𝚺ᴬ₀-Predicate[V] IsRegular via isRegularDef := .mk fun v ↦ by
  simp [isRegularDef, isRegular_iff, Semiformula.Operator.LE.sentence_eq,
    Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq]

def CobhamLE (x y : V) : Prop := (x = y ∨ x < y) ∨ ¬IsRegular y

scoped infix:50 " ≤ᶜ " => CobhamLE

def cobhamLEDef : 𝚺ᴬ₀.Semisentence 2 := .mkSigma “x y. x ≤ y ∨ ¬!isRegularDef y”

instance cobhamLE_defined : 𝚺ᴬ₀-Relation[V] CobhamLE via cobhamLEDef := .mk fun v ↦ by
  simp [cobhamLEDef, CobhamLE, Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.val,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq]

@[simp, grind .]
lemma cobhamLE_refl (x : V) : x ≤ᶜ x := Or.inl <| Or.inl rfl

def CobhamLT (x y : V) : Prop := x ≤ᶜ y ∧ x ≠ y

scoped infix:50 " <ᶜ " => CobhamLT

def cobhamLTDef : 𝚺ᴬ₀.Semisentence 2 := .mkSigma “x y. !cobhamLEDef x y ∧ x ≠ y”

instance cobhamLT_defined : 𝚺ᴬ₀-Relation[V] CobhamLT via cobhamLTDef := .mk fun v ↦ by
  simp [cobhamLTDef, CobhamLT]

variable [V↓[ℒₒᵣ] ⊧* 𝗥₀]

@[simp, grind =]
lemma numeral_add_one_of_R0 (n : ℕ) : (numeral n : V) + 1 = numeral (n + 1) := by
  simpa using numeral_add_numeral (M := V) n 1

@[grind .]
lemma isRegular_numeral (n : ℕ) : IsRegular (numeral n : V) := by
  constructor
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · right
      simpa using (numeral_lt_numeral_iff (M := V)).mpr hn
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

lemma cobhamLE_numeral_of_le {k q : ℕ} {w : V} (hkq : k ≤ q) (h : numeral q ≤ᶜ w) :
    numeral k ≤ᶜ w := by
  by_cases hw : IsRegular w
  · rcases exists_eq_numeral_or_numeral_le_of_isRegular hw k with ⟨i, hi, rfl⟩ | h'
    · simp [CobhamLE, hw] at h
      omega
    · exact Or.inl h'
  · exact Or.inr hw

@[simp, grind =]
lemma numeral_cobhamLE_numeral_iff {k n : ℕ} : (numeral k : V) ≤ᶜ numeral n ↔ k ≤ n := by
  simp [cobhamLE_numeral_iff]
  omega

@[grind =]
lemma cobhamLT_numeral_iff {n : ℕ} : x <ᶜ numeral n ↔ x < numeral n := by
  have := not_numeral_lt_self (M := V) n
  grind [CobhamLT]

lemma cobhamLT_numeral_iff_exists {n : ℕ} : x <ᶜ numeral n ↔ ∃ i < n, x = numeral i := by
  simp [cobhamLT_numeral_iff, lt_numeral_iff, Fin.exists_iff]

end order

section representation

def cobhamComparison (φ : 𝚺ᴬ₀.Semisentence 3) : ArithmeticSemisentence 2 :=
  “x y. ∃ w, !cobhamLEDef y w ∧ (∃ v, !cobhamLEDef v w ∧ !φ x y v) ∧
    ∀ z u, !cobhamLEDef z w → !cobhamLEDef u w → !φ x z u → y = z”

variable {f : ℕ → ℕ}

noncomputable def cobhamRepresentation (f : ℕ → ℕ) : ArithmeticSemisentence 2 :=
  cobhamComparison (deltaZeroGraph f)

theorem cobhamRepresentation_spec (hf : Computable f) (n : ℕ) :
    𝗥₀ ⊢ “∀ y, !(cobhamRepresentation f) ↑n y ↔ y = ↑(f n)” := by
  apply complete.{0}
  intro V _ _
  have hφ := deltaZeroGraph_spec hf
  obtain ⟨k, hk⟩ := (hφ n (f n)).mp rfl
  have key : ∀ i j, V ⊧/![numeral n, numeral i, numeral j] (deltaZeroGraph f).val → i = f n :=
    fun i j h ↦ (hφ n i).mpr ⟨j, by
      simpa using (R0.models_iff_of_Sigma0 (M := V) (by simp) (bv := ![n, i, j])).mp
        (by simpa [Matrix.comp_vecCons''] using h)⟩
  have hkM : V ⊧/![numeral n, numeral (f n), numeral k] (deltaZeroGraph f).val := by
    simpa [Matrix.comp_vecCons''] using
      (R0.models_iff_of_Sigma0 (M := V) (by simp) (bv := ![n, f n, k])).mpr hk
  suffices ∀ y : V, V ⊧/![numeral n, y] (cobhamRepresentation f) ↔ y = numeral (f n) by
    simpa [models_iff] using this
  intro y
  suffices (∃ w, y ≤ᶜ w ∧ (∃ v, v ≤ᶜ w ∧ V ⊧/![numeral n, y, v] (deltaZeroGraph f).val) ∧
      ∀ z u, z ≤ᶜ w → u ≤ᶜ w → V ⊧/![numeral n, z, u] (deltaZeroGraph f).val → y = z) ↔
        y = numeral (f n) by
    simpa [cobhamRepresentation, cobhamComparison] using this
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

end representation

end FFL.FirstOrder.Arithmetic
