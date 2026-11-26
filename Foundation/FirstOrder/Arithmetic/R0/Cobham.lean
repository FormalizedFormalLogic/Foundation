module

public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# Cobham's order and weak representability in $\mathsf{R}_0$

Cobham's order `x ≤ᶜ y` holds if $x \le y$ or `y` is not regular, i.e. fails
$0 \le y \wedge \forall v < y,\ v + 1 \le y$. In every model of $\mathsf{R}_0$ it compares every
element with every numeral, and below a numeral it coincides with $\le$. Bounding the search for
a witness by Cobham's order, every computable function `f` is weakly represented in
$\mathsf{R}_0$ by `cobhamRepresentation f`: $\mathsf{R}_0 \vdash \forall y\,(\gamma(\bar n, y)
\leftrightarrow y = \overline{f(n)})$ for every `n` (`cobhamRepresentation_spec`).

## References

- [Sve08]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open ORingStructure

section order

variable {M : Type*} [ORingStructure M] {x y : M}

@[mk_iff]
structure IsRegular (y : M) : Prop where
  zero_le : 0 = y ∨ 0 < y
  add_one_le : ∀ v < y, v + 1 = y ∨ v + 1 < y

def isRegular : ArithmeticSemisentence 1 := “y. 0 ≤ y ∧ ∀ v < y, v + 1 ≤ y”

@[simp]
lemma eval_isRegular : M ⊧/![y] isRegular ↔ IsRegular y := by
  simp [isRegular, isRegular_iff, Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.val,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq]

def CobhamLE (x y : M) : Prop := (x = y ∨ x < y) ∨ ¬IsRegular y

scoped infix:50 " ≤ᶜ " => CobhamLE

def cobhamLE : ArithmeticSemisentence 2 := “x y. x ≤ y ∨ ¬!isRegular y”

@[simp]
lemma eval_cobhamLE : M ⊧/![x, y] cobhamLE ↔ x ≤ᶜ y := by
  simp [cobhamLE, CobhamLE, Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.val,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq]

@[simp, grind .]
lemma cobhamLE_refl (x : M) : x ≤ᶜ x := Or.inl <| Or.inl rfl

def CobhamLT (x y : M) : Prop := x ≤ᶜ y ∧ x ≠ y

scoped infix:50 " <ᶜ " => CobhamLT

def cobhamLT : ArithmeticSemisentence 2 := “x y. !cobhamLE x y ∧ x ≠ y”

@[simp]
lemma eval_cobhamLT : M ⊧/![x, y] cobhamLT ↔ x <ᶜ y := by
  simp [cobhamLT, CobhamLT]

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
  “x y. ∃ w, !cobhamLE y w ∧ (∃ v, !cobhamLE v w ∧ !φ x y v) ∧
    ∀ z u, !cobhamLE z w → !cobhamLE u w → !φ x z u → y = z”

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

lemma exists_deltaZero_graph (hf : Computable f) : ∃ φ : ArithmeticSemisentence 3,
    ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ ∧ ∀ n m, m = f n ↔ ∃ k, ℕ ⊧/![n, m, k] φ := by
  let F : List.Vector ℕ 1 →. ℕ := fun v ↦ Part.some (f (v.get 0))
  have hF : Nat.Partrec' F := Nat.Partrec'.of_part <| hf.comp (Primrec.to_comp (by primrec))
  have hσ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 (codeOfPartrec' F) := by simp [codeOfPartrec']
  obtain ⟨ψ, hψ⟩ := Bounding.Prenex.models_exists_prenex.{_, 0} (Γ' := 𝚺) hσ
  use “x y v. !ψ.sigmaInv.val v y x”
  and_intros
  · simp
  · intro n m
    have := (codeOfPartrec'_spec hF (y := m) (v := ![n])).symm.trans
      ((hψ ℕ (m :> ![n]) Empty.elim).trans (ψ.models_sigmaInv _))
    simpa [F] using this

noncomputable def cobhamRepresentation (f : ℕ → ℕ) : ArithmeticSemisentence 2 :=
  cobhamComparison <| Classical.epsilon fun φ ↦
    ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ ∧ ∀ n m, m = f n ↔ ∃ k, ℕ ⊧/![n, m, k] φ

theorem cobhamRepresentation_spec (hf : Computable f) (n : ℕ) :
    𝗥₀ ⊢ “∀ y, !(cobhamRepresentation f) ↑n y ↔ y = ↑(f n)” := by
  obtain ⟨hφ₀, hφ⟩ := Classical.epsilon_spec (exists_deltaZero_graph hf)
  apply complete.{0}
  intro M _ _
  simpa [models_iff, cobhamRepresentation, -eval_cobhamComparison]
    using eval_cobhamComparison_numeral_iff (M := M) hφ₀ hφ n

end representation

end FFL.FirstOrder.Arithmetic
