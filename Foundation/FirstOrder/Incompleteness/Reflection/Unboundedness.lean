module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.HierarchicalSatisfaction
public import Foundation.FirstOrder.Incompleteness.Reflection.Local

/-!
# Unboundedness of local reflection

Let `X` be a $\Delta_1$-definable set of prenex `Γ (n + 1)` sentences and `Y` a
$\Delta_1$-definable set of sentences none of which is provable in `T + X`. Then a single
`Γ (n + 1)` sentence `truncatedTruthSentence` implies `X` over `T` without making any member of
`Y` provable. With `Y = {⊥}`, the local reflection schema of `T` on `Γ.alt (n + 1)` sentences is
not provable in any consistent extension of `T` by `X`.

## References

- [Lin97, Theorem 4.3, Corollary 4.2]
- [AB05, Theorem 23, Remark 24]
-/

@[expose] public section

open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment Bootstrapping

section truncatedTruth

variable (T U Y : ArithmeticTheory) [T.Δ₁] [U.Δ₁] [Y.Δ₁] (n : ℕ)

noncomputable def truncatedTruthFormula : Polarity → ArithmeticSemisentence 1
  | 𝚷 => “v. ∀ y, ((!U.Δ₁ch.sigma.val y ∧ !(isSemiformula ℒₒᵣ).sigma.val 0 y ∧
        ∀ z < y, ∀ u < y, (!Y.Δ₁ch.pi.val z →
          ∃ w, !(impGraph ℒₒᵣ).val w v z ∧ ¬!(proof T).pi.val u w))
      → !(partialTruth 𝚷 (n + 1)).val y)”
  | 𝚺 => “v. ∃ y, ((∃ z < y, ∃ u < y, !Y.Δ₁ch.sigma.val z ∧
        ∃ w, !(impGraph ℒₒᵣ).val w v z ∧ !(proof T).sigma.val u w) ∧
      ∀ z < y, ((!U.Δ₁ch.pi.val z ∧ !(isSemiformula ℒₒᵣ).pi.val 0 z)
        → !(partialTruth 𝚺 (n + 1)).val z))”

noncomputable def truncatedTruthSentence (Γ : Polarity) : ArithmeticSentence :=
  (truncatedTruthFormula T U Y n Γ)/[⌜fixedpoint (truncatedTruthFormula T U Y n Γ)⌝]

lemma hierarchy_truncatedTruthSentence (Γ : Polarity) :
    ℬ[<, ℒₒᵣ].Hierarchy Γ (n + 1) (truncatedTruthSentence T U Y n Γ) := by
  have h : 1 ≤ n + 1 := Nat.le_add_left 1 n;
  suffices ℬ[<, ℒₒᵣ].Hierarchy Γ (n + 1) (truncatedTruthFormula T U Y n Γ) by
    simpa [truncatedTruthSentence];
  cases Γ with
  | sigma =>
    simpa [truncatedTruthFormula, Y.Δ₁ch.sigma.sigma_prop.mono h,
      (impGraph ℒₒᵣ).sigma_prop.mono h, (proof T).sigma.sigma_prop.mono h,
      U.Δ₁ch.pi.pi_prop.mono h, (isSemiformula ℒₒᵣ).pi.pi_prop.mono h]
      using (partialTruth 𝚺 (n + 1)).sigma_prop;
  | pi =>
    simpa [truncatedTruthFormula, U.Δ₁ch.sigma.sigma_prop.mono h,
      (isSemiformula ℒₒᵣ).sigma.sigma_prop.mono h, Y.Δ₁ch.pi.pi_prop.mono h,
      (impGraph ℒₒᵣ).sigma_prop.mono h, (proof T).pi.pi_prop.mono h]
      using (partialTruth 𝚷 (n + 1)).pi_prop;

end truncatedTruth

variable {T : ArithmeticTheory} [T.Δ₁] {n : ℕ} {Γ : Polarity}

section
variable {U Y : ArithmeticTheory} [U.Δ₁] [Y.Δ₁]

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma mem_Δ₁Class_natCast_iff {m : ℕ} : m ∈ U.Δ₁Class ↔ (m : V) ∈ U.Δ₁Class := by
  simpa using Defined.shigmaOne_absolute V (φ := U.Δ₁ch)
    (R := fun v ↦ v 0 ∈ U.Δ₁Class) (R' := fun v ↦ v 0 ∈ U.Δ₁Class)
    Δ₁Class.defined Δ₁Class.defined ![m];

lemma isSemiformula_natCast_iff {m : ℕ} :
    IsSemiformula ℒₒᵣ 0 m ↔ IsSemiformula ℒₒᵣ (0 : V) (m : V) := by
  simpa using Defined.shigmaOne_absolute V (φ := isSemiformula ℒₒᵣ)
    (R := fun v ↦ IsSemiformula ℒₒᵣ (v 0) (v 1)) (R' := fun v ↦ IsSemiformula ℒₒᵣ (v 0) (v 1))
    IsSemiformula.defined IsSemiformula.defined ![0, m];

lemma exists_mem_eq_quote {m : ℕ} (hmem : (m : V) ∈ U.Δ₁Class)
    (hsemi : IsSemiformula ℒₒᵣ (0 : V) (m : V)) : ∃ σ ∈ U, (m : V) = (⌜σ⌝ : V) := by
  obtain ⟨F, hF⟩ :=
    IsSemiformula.sound (L := ℒₒᵣ) (isSemiformula_natCast_iff (V := V) |>.mpr hsemi);
  have : (⌜F⌝ : ℕ) ∈ U.Δ₁Class := hF ▸ mem_Δ₁Class_natCast_iff.mpr hmem;
  obtain ⟨σ, hσ, rfl⟩ := Δ₁Class.mem_iff_s.mp this;
  exact ⟨σ, hσ, by rw [← hF]; simp [Sentence.quote_def, Semiformula.coe_quote_eq_quote]⟩;

lemma models_truncatedTruthSentence_pi_iff :
    V↓[ℒₒᵣ] ⊧ truncatedTruthSentence T U Y n 𝚷 ↔
      ∀ y ∈ U.Δ₁Class, IsSemiformula ℒₒᵣ (0 : V) y →
        (∀ z < y, ∀ u < y, z ∈ Y.Δ₁Class →
          ¬Proof T u (imp ℒₒᵣ ⌜fixedpoint (truncatedTruthFormula T U Y n 𝚷)⌝ z)) →
          PartialTruth 𝚷 (n + 1) y := by
  have h : V↓[ℒₒᵣ] ⊧ truncatedTruthSentence T U Y n 𝚷 ↔
      V ⊧/![(⌜fixedpoint (truncatedTruthFormula T U Y n 𝚷)⌝ : V)]
        (truncatedTruthFormula T U Y n 𝚷) := by
    simp [truncatedTruthSentence, models_iff];
  rw [h];
  simp [truncatedTruthFormula, HierarchySymbol.Semiformula.val_sigma,
    (Δ₁Class.defined (T := U) (V := V)).df,
    (Δ₁Class.defined (T := Y) (V := V)).proper.iff',
    (Δ₁Class.defined (T := Y) (V := V)).df,
    (IsSemiformula.defined (L := ℒₒᵣ) (V := V)).df,
    (imp.defined (L := ℒₒᵣ) (V := V)).df,
    (Proof.defined (T := T) (V := V)).proper.iff',
    (Proof.defined (T := T) (V := V)).df,
    (PartialTruth.pi_defined (V := V) (n + 1)).df];

lemma models_truncatedTruthSentence_sigma_iff :
    V↓[ℒₒᵣ] ⊧ truncatedTruthSentence T U Y n 𝚺 ↔
      ∃ y : V, (∃ z < y, ∃ u < y, z ∈ Y.Δ₁Class ∧
          Proof T u (imp ℒₒᵣ ⌜fixedpoint (truncatedTruthFormula T U Y n 𝚺)⌝ z)) ∧
        ∀ z < y, z ∈ U.Δ₁Class → IsSemiformula ℒₒᵣ (0 : V) z → PartialTruth 𝚺 (n + 1) z := by
  have h : V↓[ℒₒᵣ] ⊧ truncatedTruthSentence T U Y n 𝚺 ↔
      V ⊧/![(⌜fixedpoint (truncatedTruthFormula T U Y n 𝚺)⌝ : V)]
        (truncatedTruthFormula T U Y n 𝚺) := by
    simp [truncatedTruthSentence, models_iff];
  rw [h];
  simp [truncatedTruthFormula, HierarchySymbol.Semiformula.val_sigma,
    (Δ₁Class.defined (T := U) (V := V)).proper.iff',
    (Δ₁Class.defined (T := U) (V := V)).df,
    (Δ₁Class.defined (T := Y) (V := V)).df,
    (IsSemiformula.defined (L := ℒₒᵣ) (V := V)).proper.iff',
    (IsSemiformula.defined (L := ℒₒᵣ) (V := V)).df,
    (imp.defined (L := ℒₒᵣ) (V := V)).df,
    (Proof.defined (T := T) (V := V)).df,
    (PartialTruth.sigma_defined (V := V) (n + 1)).df];

end

variable [𝗜𝚺₁ ⪯ T]

private lemma provable_imp_truncatedTruthSentence_iff {ψ : ArithmeticSentence} :
    T ⊢ truncatedTruthSentence T U Y n Γ 🡒 ψ ↔
      T ⊢ fixedpoint (truncatedTruthFormula T U Y n Γ) 🡒 ψ := by
  have e : T ⊢ fixedpoint (truncatedTruthFormula T U Y n Γ) 🡘 truncatedTruthSentence T U Y n Γ :=
    WeakerThan.pbl (𝓢 := 𝗜𝚺₁) (diagonal _);
  exact ⟨C_trans (K_left e), C_trans (K_right e)⟩;

private lemma provable_of_provable_imp_pi
    (hΓ : ∀ σ ∈ U, ∃ φ : Prenex 𝚷 (n + 1) Empty 0, φ.val = σ) {ψ : ArithmeticSentence}
    (hψ : ψ ∈ Y) (h : T ⊢ truncatedTruthSentence T U Y n 𝚷 🡒 ψ) : T ∪ U ⊢ ψ := by
  obtain ⟨d⟩ := provable_imp_truncatedTruthSentence_iff.mp h;
  have hθ : T ∪ U ⊢ truncatedTruthSentence T U Y n 𝚷 := by
    apply Arithmetic.complete.{0};
    intro M _ _;
    have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ (T ∪ U) inferInstance;
    apply models_truncatedTruthSentence_pi_iff.mpr;
    intro y hmem hsemi hlt;
    have hp : Proof T ((⌜d⌝ : ℕ) : M)
        (imp ℒₒᵣ ⌜fixedpoint (truncatedTruthFormula T U Y n 𝚷)⌝ (⌜ψ⌝ : M)) := by
      have : Proof T ((⌜d⌝ : ℕ) : M) ⌜fixedpoint (truncatedTruthFormula T U Y n 𝚷) 🡒 ψ⌝ := by
        simp [coe_quote_proof_eq];
      simpa [Sentence.quote_eq] using this;
    have hle : y ≤ ((max ⌜d⌝ ⌜ψ⌝ : ℕ) : M) := not_lt.mp fun hy ↦
      hlt _ (lt_of_le_of_lt (by rw [← Sentence.coe_quote_eq_quote]; simp) hy) _
        (lt_of_le_of_lt (by simp) hy) (by simpa using hψ) hp;
    obtain ⟨m, rfl⟩ := eq_nat_of_le_nat hle;
    obtain ⟨σ, hσ, hmσ⟩ := exists_mem_eq_quote hmem hsemi;
    obtain ⟨φ, rfl⟩ := hΓ σ hσ;
    rw [hmσ];
    exact (partialTruth_quote_iff φ).mpr (models_of_mem (Set.mem_union_right T hσ));
  exact (WeakerThan.ofSubset Set.subset_union_left).pbl h ⨀ hθ;

private lemma provable_of_provable_imp_sigma
    (hΓ : ∀ σ ∈ U, ∃ φ : Prenex 𝚺 (n + 1) Empty 0, φ.val = σ) {ψ : ArithmeticSentence}
    (hψ : ψ ∈ Y) (h : T ⊢ truncatedTruthSentence T U Y n 𝚺 🡒 ψ) : T ∪ U ⊢ ψ := by
  sorry

private lemma provable_of_provable_imp
    (hΓ : ∀ σ ∈ U, ∃ φ : Prenex Γ (n + 1) Empty 0, φ.val = σ) {ψ : ArithmeticSentence}
    (hψ : ψ ∈ Y) (h : T ⊢ truncatedTruthSentence T U Y n Γ 🡒 ψ) : T ∪ U ⊢ ψ := by
  cases Γ with
  | sigma => exact provable_of_provable_imp_sigma hΓ hψ h;
  | pi => exact provable_of_provable_imp_pi hΓ hψ h;

private lemma provable_of_mem_pi (hΓ : ∀ σ ∈ U, ∃ φ : Prenex 𝚷 (n + 1) Empty 0, φ.val = σ)
    (hY : ∀ ψ ∈ Y, T ⊬ truncatedTruthSentence T U Y n 𝚷 🡒 ψ) {σ : ArithmeticSentence}
    (hσ : σ ∈ U) : 𝗜𝚺₁ ⊢ truncatedTruthSentence T U Y n 𝚷 🡒 σ := by
  sorry

private lemma provable_of_mem_sigma (hΓ : ∀ σ ∈ U, ∃ φ : Prenex 𝚺 (n + 1) Empty 0, φ.val = σ)
    (hY : ∀ ψ ∈ Y, T ⊬ truncatedTruthSentence T U Y n 𝚺 🡒 ψ) {σ : ArithmeticSentence}
    (hσ : σ ∈ U) : 𝗜𝚺₁ ⊢ truncatedTruthSentence T U Y n 𝚺 🡒 σ := by
  sorry

private lemma provable_of_mem (hΓ : ∀ σ ∈ U, ∃ φ : Prenex Γ (n + 1) Empty 0, φ.val = σ)
    (hY : ∀ ψ ∈ Y, T ⊬ truncatedTruthSentence T U Y n Γ 🡒 ψ) {σ : ArithmeticSentence}
    (hσ : σ ∈ U) : 𝗜𝚺₁ ⊢ truncatedTruthSentence T U Y n Γ 🡒 σ := by
  cases Γ with
  | sigma => exact provable_of_mem_sigma hΓ hY hσ;
  | pi => exact provable_of_mem_pi hΓ hY hσ;

end

variable {U U' Y : ArithmeticTheory} [U'.Δ₁] [Y.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- - [Lin97, Theorem 4.3] -/
theorem exists_sentence_weakerThan_of_unprovable
    (hΓ : ∀ σ ∈ U', ∃ φ : Prenex Γ (n + 1) Empty 0, φ.val = σ) (e : T ∪ U ≊ T ∪ U')
    (hY : ∀ ψ ∈ Y, T ∪ U ⊬ ψ) :
    ∃ θ : ArithmeticSentence, ℬ[<, ℒₒᵣ].Hierarchy Γ (n + 1) θ ∧
      T ∪ U ⪯ insert θ T ∧ ∀ ψ ∈ Y, insert θ T ⊬ ψ := by
  have hY' : ∀ ψ ∈ Y, T ⊬ truncatedTruthSentence T U' Y n Γ 🡒 ψ := fun ψ hψ h ↦
    hY ψ hψ (e.symm.le.pbl (provable_of_provable_imp hΓ hψ h));
  have hT : T ⪯ insert (truncatedTruthSentence T U' Y n Γ) T :=
    WeakerThan.ofSubset (Set.subset_insert _ _);
  use truncatedTruthSentence T U' Y n Γ;
  and_intros;
  · exact hierarchy_truncatedTruthSentence T U' Y n Γ;
  · apply e.le.trans;
    apply WeakerThan.ofAxm!;
    rintro φ (hφ | hφ);
    · exact by_axm (Set.mem_insert_of_mem _ hφ);
    · exact hT.pbl (WeakerThan.pbl (provable_of_mem hΓ hY' hφ)) ⨀ by_axm (Set.mem_insert _ _);
  · intro ψ hψ;
    simpa [Set.cons_eq] using deduction_iff.not.mpr (hY' ψ hψ);

theorem inconsistent_of_provable_localReflectionOn_union
    (hΓ : ∀ σ ∈ U', ∃ φ : Prenex Γ (n + 1) Empty 0, φ.val = σ) (e : T ∪ U ≊ T ∪ U')
    (h : T ∪ U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy Γ.alt (n + 1)] T) : Inconsistent (T ∪ U) := by
  by_contra hC;
  obtain ⟨θ, hθ, hle, hcon⟩ := exists_sentence_weakerThan_of_unprovable (Y := {⊥}) hΓ e
    (by simpa [consistent_iff_unprovable_bot] using hC);
  apply hcon ⊥ rfl;
  exact inconsistent_iff_provable_bot.mp <|
    T.standardProvability.inconsistent_of_provable_localReflectionOn_insert
      (fun _ hσ ↦ by simpa using hσ) hθ fun hσ ↦ hle.pbl (h hσ);

theorem not_provable_localReflectionOn_union
    (hΓ : ∀ σ ∈ U', ∃ φ : Prenex Γ (n + 1) Empty 0, φ.val = σ) (e : T ∪ U ≊ T ∪ U')
    (hC : Consistent (T ∪ U)) :
    ¬T ∪ U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy Γ.alt (n + 1)] T :=
  fun h ↦ (inconsistent_of_provable_localReflectionOn_union hΓ e h).not_con hC

end FFL.FirstOrder.Arithmetic
