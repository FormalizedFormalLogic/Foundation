module

public import Foundation.ProvabilityLogic.Formula

/-!
# Letterless formulas, their spectra and traces

## References

- [Art86]
- [Boo94]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

namespace Formula

variable {α : Type*}

def alpha (n : ℕ) : Formula α := □^[n + 1]⊥ 🡒 □^[n]⊥

end Formula

open Formula

abbrev LetterlessFormula := Formula Empty

abbrev LetterlessFormulaSet := Set LetterlessFormula

namespace LetterlessFormula

variable {α : Type*} {A B : LetterlessFormula} {n : ℕ}

def lift : LetterlessFormula → Formula α
  | #a    => a.elim
  | ⊥     => ⊥
  | A 🡒 B => A.lift 🡒 B.lift
  | □A    => □A.lift

attribute [coe] lift

instance : Coe LetterlessFormula (Formula α) := ⟨lift⟩

@[simp, grind =] lemma lift_bot : lift ⊥ = (⊥ : Formula α) := rfl
@[simp, grind =] lemma lift_imp : lift (A 🡒 B) = (↑A 🡒 ↑B : Formula α) := rfl
@[simp, grind =] lemma lift_box : lift (□A) = (□↑A : Formula α) := rfl
lemma lift_neg : lift (∼A) = (∼↑A : Formula α) := rfl

@[simp, grind =]
lemma lift_boxItr : lift (□^[n]A) = (□^[n]↑A : Formula α) := by
  induction n <;> simp_all;

@[simp, grind =] lemma lift_alpha : lift (alpha n) = (alpha n : Formula α) := by
  simp [alpha];

lemma lift_conj₂ : ∀ {l : List LetterlessFormula}, lift (⋀l) = (⋀l.map lift : Formula α)
  | []  => rfl
  | [_] => rfl
  | A :: B :: l => congrArg (lift A ⋏ ·) (lift_conj₂ (l := B :: l))

lemma lift_conj' {ι : Type*} {s : Finset ι} {f : ι → LetterlessFormula} :
    lift (s.conj' f) = (s.conj' fun i ↦ ↑(f i) : Formula α) := by
  simp [Finset.conj', List.conj', lift_conj₂, Function.comp_def];

@[simp] lemma lift_eq_self : ∀ A : LetterlessFormula, A.lift = A
  | #a    => a.elim
  | ⊥     => rfl
  | A 🡒 B => by simp [lift_eq_self A, lift_eq_self B]
  | □A    => by simp [lift_eq_self A]

/-- The set of ranks of worlds forcing a letterless formula. -/
def spectrum : LetterlessFormula → Set ℕ
  | #a    => a.elim
  | ⊥     => ∅
  | A 🡒 B => A.spectrumᶜ ∪ B.spectrum
  | □A    => { n | ∀ i < n, i ∈ A.spectrum }

def trace (A : LetterlessFormula) : Set ℕ := A.spectrumᶜ

@[simp, grind =] lemma spectrum_bot : spectrum ⊥ = ∅ := rfl
@[simp, grind =] lemma spectrum_imp : spectrum (A 🡒 B) = A.spectrumᶜ ∪ B.spectrum := rfl
@[simp, grind =] lemma spectrum_box : spectrum (□A) = { n | ∀ i < n, i ∈ A.spectrum } := rfl
@[simp, grind =] lemma spectrum_top : spectrum ⊤ = Set.univ := by
  change (∅ : Set ℕ)ᶜ ∪ ∅ = _;
  simp;
@[simp, grind =] lemma spectrum_neg : spectrum (∼A) = A.spectrumᶜ := by
  change A.spectrumᶜ ∪ ∅ = _;
  simp;
@[simp, grind =] lemma spectrum_and : spectrum (A ⋏ B) = A.spectrum ∩ B.spectrum := by
  change (A.spectrumᶜ ∪ (B.spectrumᶜ ∪ ∅))ᶜ ∪ ∅ = _;
  simp;

@[simp, grind =]
lemma spectrum_boxItr_bot : spectrum (□^[n]⊥) = Set.Iio n := by
  induction n with
  | zero => simp;
  | succ n ih =>
    ext k;
    suffices (∀ i < k, i < n) ↔ k ≤ n by simpa [ih, Nat.lt_succ_iff];
    exact ⟨fun h ↦ by by_contra! hk; exact lt_irrefl n (h n hk), fun h i hi ↦ by omega⟩;

@[simp, grind =]
lemma spectrum_alpha : spectrum (alpha n) = {n}ᶜ := by
  ext i;
  suffices (∃ k < i, n ≤ k) ∨ i < n ↔ i ≠ n by simpa [alpha];
  constructor;
  · rintro (⟨k, hk, hn⟩ | h) <;> omega;
  · exact fun h ↦ (Nat.lt_or_gt_of_ne h).symm.imp (⟨n, ·, le_rfl⟩) id;

lemma spectrum_conj₂ : ∀ {l : List LetterlessFormula}, spectrum (⋀l) = ⋂ A ∈ l, A.spectrum
  | []  => by simp
  | [A] => by simp
  | A :: B :: l => by simp [spectrum_conj₂ (l := B :: l)]

@[simp, grind =]
lemma spectrum_conj' {ι : Type*} {s : Finset ι} {f : ι → LetterlessFormula} :
    spectrum (s.conj' f) = ⋂ i ∈ s, (f i).spectrum := by
  simp [Finset.conj', List.conj', spectrum_conj₂];

@[simp, grind =] lemma mem_trace : n ∈ trace A ↔ n ∉ spectrum A := Iff.rfl

@[simp, grind =] lemma trace_alpha : trace (alpha n) = {n} := by simp [trace]

@[grind .]
lemma spectrum_finite_or_cofinite : A.spectrum.Finite ∨ A.spectrumᶜ.Finite := by
  induction A using Formula.rec' with
  | atom a => exact a.elim;
  | falsum => simp;
  | imp A B ihA ihB =>
    rcases ihA with hA | hA <;> rcases ihB with hB | hB <;>
    simp_all [Set.compl_union, Set.Finite.inter_of_left, Set.Finite.inter_of_right];
  | box A ih =>
    by_cases h : ∀ i, i ∈ spectrum A;
    · simp [h];
    · obtain ⟨k, hk⟩ := not_forall.mp h;
      left;
      apply (Set.finite_Iic k).subset;
      intro n hn;
      by_contra! hkn;
      exact hk (hn k (not_le.mp hkn));

end LetterlessFormula

namespace LetterlessFormulaSet

variable {α : Type*}

abbrev lift (X : LetterlessFormulaSet) : Set (Formula α) := LetterlessFormula.lift '' X

attribute [coe] lift

instance : Coe LetterlessFormulaSet (Set (Formula α)) := ⟨lift⟩

def spectrum (X : LetterlessFormulaSet) : Set ℕ := ⋂ A ∈ X, LetterlessFormula.spectrum A

def trace (X : LetterlessFormulaSet) : Set ℕ := X.spectrumᶜ

variable {X : LetterlessFormulaSet} {n : ℕ}

@[simp, grind =]
lemma mem_spectrum : n ∈ X.spectrum ↔ ∀ A ∈ X, n ∈ LetterlessFormula.spectrum A := by
  simp [spectrum];

variable {A : LetterlessFormula}

@[simp] lemma spectrum_singleton : spectrum {A} = LetterlessFormula.spectrum A := by simp [spectrum]

end LetterlessFormulaSet

namespace LetterlessFormula

variable {X : LetterlessFormulaSet} {A : LetterlessFormula}

lemma exists_finset_of_spectrum_subset (hXA : X.spectrum ⊆ spectrum A)
    (h : (∃ B ∈ X, (spectrum B).Finite) ∨ (trace A).Finite) :
    ∃ Y : Finset LetterlessFormula, ↑Y ⊆ X ∧
      ∀ n, (∀ C ∈ Y, n ∈ spectrum C) → n ∈ spectrum A := by
  obtain ⟨Y₀, hY₀, hfin⟩ : ∃ Y₀ : Finset LetterlessFormula, ↑Y₀ ⊆ X ∧
      {n | (∀ C ∈ Y₀, n ∈ spectrum C) ∧ n ∉ spectrum A}.Finite := by
    rcases h with ⟨B, hB, hfin⟩ | hfin;
    · exact ⟨{B}, by simpa, hfin.subset fun n hn ↦ by simpa using hn.1⟩;
    · exact ⟨∅, by simp, by simpa [trace, Set.compl_def] using hfin⟩;
  have hC : ∀ n, (∀ C ∈ Y₀, n ∈ spectrum C) ∧ n ∉ spectrum A → ∃ C ∈ X, n ∉ spectrum C := by
    intro n hn;
    by_contra! hc;
    exact hn.2 (hXA (LetterlessFormulaSet.mem_spectrum.mpr hc));
  choose f hfX hf using hC;
  use Y₀ ∪ hfin.toFinset.attach.image fun n ↦ f n.1 (hfin.mem_toFinset.mp n.2);
  and_intros;
  · intro C hC;
    rcases Finset.mem_union.mp hC with hC | hC;
    · exact hY₀ hC;
    · obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hC;
      exact hfX _ _;
  · intro n hn;
    by_contra hA;
    have hn' : (∀ C ∈ Y₀, n ∈ spectrum C) ∧ n ∉ spectrum A := ⟨fun C hC ↦ hn C (by simp [hC]), hA⟩;
    exact hf n hn' <| hn _ <| Finset.mem_union_right _ <|
      Finset.mem_image.mpr ⟨⟨n, hfin.mem_toFinset.mpr hn'⟩, by simp, rfl⟩;

end LetterlessFormula

end FFL.ProvabilityLogic

end
