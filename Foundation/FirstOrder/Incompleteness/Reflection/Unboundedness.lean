module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.HierarchicalSatisfaction
public import Foundation.FirstOrder.Incompleteness.Reflection.Local

/-!
# Unboundedness of local reflection

The local reflection schema of `T` on `Γ.alt (n + 1)` sentences is not provable in any consistent
extension of `T` by a $\Delta_1$-presented set of prenex `Γ (n + 1)` sentences. Such an extension
is contained in a consistent extension of `T` by the single `Γ (n + 1)` sentence
`collapseSentence`.

## References

- [Lin97, Theorem 4.3, Corollary 4.2]
- [AB05, Theorem 23, Remark 24]
-/

@[expose] public section

open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment Bootstrapping

section collapse

variable (T U : ArithmeticTheory) [T.Δ₁] [U.Δ₁] (n : ℕ)

noncomputable def collapseFormula : Polarity → ArithmeticSemisentence 1
  | 𝚷 => “v. ∀ y, ((!U.Δ₁ch.sigma.val y ∧ !(isSemiformula ℒₒᵣ).sigma.val 0 y ∧
        ∀ u < y, ∃ w, !(negGraph ℒₒᵣ).val w v ∧ ¬!(proof T).pi.val u w)
      → !(partialTruth 𝚷 (n + 1)).val y)”
  | 𝚺 => “v. ∃ y, ((∃ u < y, ∃ w, !(negGraph ℒₒᵣ).val w v ∧ !(proof T).sigma.val u w) ∧
      ∀ z < y, ((!U.Δ₁ch.pi.val z ∧ !(isSemiformula ℒₒᵣ).pi.val 0 z)
        → !(partialTruth 𝚺 (n + 1)).val z))”

noncomputable def collapseSentence (Γ : Polarity) : ArithmeticSentence :=
  (collapseFormula T U n Γ)/[⌜fixedpoint (collapseFormula T U n Γ)⌝]

lemma hierarchy_collapseSentence (Γ : Polarity) :
    ℬ[<, ℒₒᵣ].Hierarchy Γ (n + 1) (collapseSentence T U n Γ) := by
  have h : 1 ≤ n + 1 := Nat.le_add_left 1 n;
  suffices ℬ[<, ℒₒᵣ].Hierarchy Γ (n + 1) (collapseFormula T U n Γ) by
    simpa [collapseSentence];
  cases Γ with
  | sigma =>
    simpa [collapseFormula, (negGraph ℒₒᵣ).sigma_prop.mono h, (proof T).sigma.sigma_prop.mono h,
      U.Δ₁ch.pi.pi_prop.mono h, (isSemiformula ℒₒᵣ).pi.pi_prop.mono h]
      using (partialTruth 𝚺 (n + 1)).sigma_prop;
  | pi =>
    simpa [collapseFormula, U.Δ₁ch.sigma.sigma_prop.mono h,
      (isSemiformula ℒₒᵣ).sigma.sigma_prop.mono h, (negGraph ℒₒᵣ).sigma_prop.mono h,
      (proof T).pi.pi_prop.mono h]
      using (partialTruth 𝚷 (n + 1)).pi_prop;

end collapse

variable {T : ArithmeticTheory} [T.Δ₁] {n : ℕ} {Γ : Polarity}

section
variable {U : ArithmeticTheory} [U.Δ₁]

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

lemma eval_collapseFormula_pi (c : V) :
    V ⊧/![c] (collapseFormula T U n 𝚷) ↔
      ∀ y ∈ U.Δ₁Class, IsSemiformula ℒₒᵣ (0 : V) y →
        (∀ u < y, ¬Proof T u (neg ℒₒᵣ c)) → PartialTruth 𝚷 (n + 1) y := by
  simp [collapseFormula, HierarchySymbol.Semiformula.val_sigma,
    (Δ₁Class.defined (T := U) (V := V)).df,
    (IsSemiformula.defined (L := ℒₒᵣ) (V := V)).df,
    (neg.defined (L := ℒₒᵣ) (V := V)).df,
    (Proof.defined (T := T) (V := V)).proper.iff',
    (Proof.defined (T := T) (V := V)).df,
    (PartialTruth.pi_defined (V := V) (n + 1)).df];

lemma eval_collapseFormula_sigma (c : V) :
    V ⊧/![c] (collapseFormula T U n 𝚺) ↔
      ∃ y : V, (∃ u < y, Proof T u (neg ℒₒᵣ c)) ∧
        ∀ z < y, z ∈ U.Δ₁Class → IsSemiformula ℒₒᵣ (0 : V) z → PartialTruth 𝚺 (n + 1) z := by
  simp [collapseFormula, HierarchySymbol.Semiformula.val_sigma,
    (Δ₁Class.defined (T := U) (V := V)).proper.iff',
    (Δ₁Class.defined (T := U) (V := V)).df,
    (IsSemiformula.defined (L := ℒₒᵣ) (V := V)).proper.iff',
    (IsSemiformula.defined (L := ℒₒᵣ) (V := V)).df,
    (neg.defined (L := ℒₒᵣ) (V := V)).df,
    (Proof.defined (T := T) (V := V)).df,
    (PartialTruth.sigma_defined (V := V) (n + 1)).df];

lemma models_collapseSentence_pi_iff :
    V↓[ℒₒᵣ] ⊧ collapseSentence T U n 𝚷 ↔
      ∀ y ∈ U.Δ₁Class, IsSemiformula ℒₒᵣ (0 : V) y →
        (∀ u < y, ¬Proof T u (⌜∼fixedpoint (collapseFormula T U n 𝚷)⌝ : V)) →
          PartialTruth 𝚷 (n + 1) y := by
  have h : V↓[ℒₒᵣ] ⊧ collapseSentence T U n 𝚷 ↔
      V ⊧/![(⌜fixedpoint (collapseFormula T U n 𝚷)⌝ : V)] (collapseFormula T U n 𝚷) := by
    simp [collapseSentence, models_iff];
  rw [h, eval_collapseFormula_pi];
  simp [Sentence.quote_eq];

lemma models_collapseSentence_sigma_iff :
    V↓[ℒₒᵣ] ⊧ collapseSentence T U n 𝚺 ↔
      ∃ y : V, (∃ u < y, Proof T u (⌜∼fixedpoint (collapseFormula T U n 𝚺)⌝ : V)) ∧
        ∀ z < y, z ∈ U.Δ₁Class → IsSemiformula ℒₒᵣ (0 : V) z → PartialTruth 𝚺 (n + 1) z := by
  have h : V↓[ℒₒᵣ] ⊧ collapseSentence T U n 𝚺 ↔
      V ⊧/![(⌜fixedpoint (collapseFormula T U n 𝚺)⌝ : V)] (collapseFormula T U n 𝚺) := by
    simp [collapseSentence, models_iff];
  rw [h, eval_collapseFormula_sigma];
  simp [Sentence.quote_eq];

end

variable [𝗜𝚺₁ ⪯ T]

private lemma provable_neg_collapseSentence_iff :
    T ⊢ ∼collapseSentence T U n Γ ↔ T ⊢ ∼fixedpoint (collapseFormula T U n Γ) := by
  have e : T ⊢ fixedpoint (collapseFormula T U n Γ) 🡘 collapseSentence T U n Γ :=
    WeakerThan.pbl (𝓢 := 𝗜𝚺₁) (diagonal _);
  constructor <;> intro h <;> cl_prover [e, h];

private lemma inconsistent_union_of_provable_neg_pi
    (hΓ : ∀ σ ∈ U, ∃ φ : Prenex 𝚷 (n + 1) Empty 0, φ.val = σ)
    (hneg : T ⊢ ∼collapseSentence T U n 𝚷) : Inconsistent (T ∪ U) := by
  obtain ⟨d⟩ : T ⊢ ∼fixedpoint (collapseFormula T U n 𝚷) :=
    provable_neg_collapseSentence_iff.mp hneg;
  have hprov : T ∪ U ⊢ collapseSentence T U n 𝚷 := by
    apply Arithmetic.complete.{0};
    intro M _ _;
    have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ (T ∪ U) inferInstance;
    apply models_collapseSentence_pi_iff.mpr;
    intro y hmem hsemi hlt;
    have hp : Proof T ((⌜d⌝ : ℕ) : M) ⌜∼fixedpoint (collapseFormula T U n 𝚷)⌝ := by
      simp [coe_quote_proof_eq];
    have hle : y ≤ ((⌜d⌝ : ℕ) : M) := not_lt.mp fun h ↦ hlt _ h hp;
    obtain ⟨m, rfl⟩ := eq_nat_of_le_nat hle;
    obtain ⟨σ, hσ, hmσ⟩ := exists_mem_eq_quote hmem hsemi;
    obtain ⟨φ, rfl⟩ := hΓ σ hσ;
    rw [hmσ];
    exact (partialTruth_quote_iff φ).mpr (models_of_mem (Set.mem_union_right T hσ));
  exact inconsistent_of_provable_of_unprovable hprov (WeakerThan.pbl hneg);

private lemma inconsistent_union_of_provable_neg_sigma
    (hΓ : ∀ σ ∈ U, ∃ φ : Prenex 𝚺 (n + 1) Empty 0, φ.val = σ)
    (hneg : T ⊢ ∼collapseSentence T U n 𝚺) : Inconsistent (T ∪ U) := by
  obtain ⟨d⟩ : T ⊢ ∼fixedpoint (collapseFormula T U n 𝚺) :=
    provable_neg_collapseSentence_iff.mp hneg;
  have hprov : T ∪ U ⊢ collapseSentence T U n 𝚺 := by
    apply Arithmetic.complete.{0};
    intro M _ _;
    have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ (T ∪ U) inferInstance;
    have hp : Proof T ((⌜d⌝ : ℕ) : M) ⌜∼fixedpoint (collapseFormula T U n 𝚺)⌝ := by
      simp [coe_quote_proof_eq];
    apply models_collapseSentence_sigma_iff.mpr;
    use ((⌜d⌝ : ℕ) + 1 : ℕ);
    and_intros;
    · exact ⟨_, by push_cast; simp, hp⟩;
    · intro z hz hmem hsemi;
      obtain ⟨m, rfl⟩ := eq_nat_of_lt_nat hz;
      obtain ⟨σ, hσ, hmσ⟩ := exists_mem_eq_quote hmem hsemi;
      obtain ⟨φ, rfl⟩ := hΓ σ hσ;
      rw [hmσ];
      exact (partialTruth_quote_iff φ).mpr (models_of_mem (Set.mem_union_right T hσ));
  exact inconsistent_of_provable_of_unprovable hprov (WeakerThan.pbl hneg);

private lemma inconsistent_union_of_provable_neg
    (hΓ : ∀ σ ∈ U, ∃ φ : Prenex Γ (n + 1) Empty 0, φ.val = σ)
    (hneg : T ⊢ ∼collapseSentence T U n Γ) : Inconsistent (T ∪ U) := by
  cases Γ with
  | sigma => exact inconsistent_union_of_provable_neg_sigma hΓ hneg;
  | pi => exact inconsistent_union_of_provable_neg_pi hΓ hneg;

private lemma provable_of_mem_pi (hΓ : ∀ σ ∈ U, ∃ φ : Prenex 𝚷 (n + 1) Empty 0, φ.val = σ)
    (hneg : T ⊬ ∼collapseSentence T U n 𝚷) {σ : ArithmeticSentence} (hσ : σ ∈ U) :
    𝗜𝚺₁ ⊢ collapseSentence T U n 𝚷 🡒 σ := by
  have h₁ : T ⊬ ∼fixedpoint (collapseFormula T U n 𝚷) := fun h ↦
    hneg (provable_neg_collapseSentence_iff.mpr h);
  obtain ⟨φ, rfl⟩ := hΓ σ hσ;
  apply Arithmetic.complete.{0};
  intro M _ _;
  apply Semantics.Imp.models_imply.mpr;
  intro hθ;
  apply (partialTruth_quote_iff φ).mp;
  apply models_collapseSentence_pi_iff.mp hθ _ (Δ₁Class.mem_iff.mpr hσ) (by simp);
  intro u hu hpu;
  rw [← Sentence.coe_quote_eq_quote] at hu;
  obtain ⟨j, rfl⟩ := eq_nat_of_lt_nat hu;
  exact h₁ (provable_of_standard_proof (V := M) hpu);

private lemma provable_of_mem_sigma (hΓ : ∀ σ ∈ U, ∃ φ : Prenex 𝚺 (n + 1) Empty 0, φ.val = σ)
    (hneg : T ⊬ ∼collapseSentence T U n 𝚺) {σ : ArithmeticSentence} (hσ : σ ∈ U) :
    𝗜𝚺₁ ⊢ collapseSentence T U n 𝚺 🡒 σ := by
  have h₁ : T ⊬ ∼fixedpoint (collapseFormula T U n 𝚺) := fun h ↦
    hneg (provable_neg_collapseSentence_iff.mpr h);
  obtain ⟨φ, rfl⟩ := hΓ σ hσ;
  apply Arithmetic.complete.{0};
  intro M _ _;
  apply Semantics.Imp.models_imply.mpr;
  intro hθ;
  obtain ⟨y, ⟨u, huy, hpu⟩, hall⟩ := models_collapseSentence_sigma_iff.mp hθ;
  have h₂ : ¬u ≤ (⌜φ.val⌝ : M) := by
    intro hle;
    rw [← Sentence.coe_quote_eq_quote] at hle;
    obtain ⟨j, rfl⟩ := eq_nat_of_le_nat hle;
    exact h₁ (provable_of_standard_proof (V := M) hpu);
  have hlt : (⌜φ.val⌝ : M) < y := lt_trans (not_le.mp h₂) huy;
  exact (partialTruth_quote_iff φ).mp (hall (⌜φ.val⌝ : M) hlt (Δ₁Class.mem_iff.mpr hσ) (by simp));

private lemma provable_of_mem (hΓ : ∀ σ ∈ U, ∃ φ : Prenex Γ (n + 1) Empty 0, φ.val = σ)
    (hneg : T ⊬ ∼collapseSentence T U n Γ) {σ : ArithmeticSentence} (hσ : σ ∈ U) :
    𝗜𝚺₁ ⊢ collapseSentence T U n Γ 🡒 σ := by
  cases Γ with
  | sigma => exact provable_of_mem_sigma hΓ hneg hσ;
  | pi => exact provable_of_mem_pi hΓ hneg hσ;

end

variable {U U' : ArithmeticTheory} [U'.Δ₁] [𝗜𝚺₁ ⪯ T]

theorem exists_sentence_weakerThan_of_consistent
    (hΓ : ∀ σ ∈ U', ∃ φ : Prenex Γ (n + 1) Empty 0, φ.val = σ) (e : T ∪ U ≊ T ∪ U')
    (hC : Consistent (T ∪ U)) :
    ∃ θ : ArithmeticSentence, ℬ[<, ℒₒᵣ].Hierarchy Γ (n + 1) θ ∧
      T ∪ U ⪯ insert θ T ∧ Consistent (insert θ T) := by
  have hneg : T ⊬ ∼collapseSentence T U' n Γ := fun h ↦
    (inconsistent_union_of_provable_neg hΓ h).not_con (hC.of_le e.symm.le);
  have hT : T ⪯ insert (collapseSentence T U' n Γ) T := WeakerThan.ofSubset (Set.subset_insert _ _);
  use collapseSentence T U' n Γ;
  and_intros;
  · exact hierarchy_collapseSentence T U' n Γ;
  · apply e.le.trans;
    apply WeakerThan.ofAxm!;
    rintro φ (hφ | hφ);
    · exact by_axm (Set.mem_insert_of_mem _ hφ);
    · exact hT.pbl (WeakerThan.pbl (provable_of_mem hΓ hneg hφ)) ⨀ by_axm (Set.mem_insert _ _);
  · simpa [Set.cons_eq] using unprovable_iff_consistent_adjoin.mp hneg;

theorem inconsistent_of_provable_localReflectionOn_union
    (hΓ : ∀ σ ∈ U', ∃ φ : Prenex Γ (n + 1) Empty 0, φ.val = σ) (e : T ∪ U ≊ T ∪ U')
    (h : T ∪ U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy Γ.alt (n + 1)] T) : Inconsistent (T ∪ U) := by
  by_contra hC
  obtain ⟨θ, hθ, hle, hcon⟩ :=
    exists_sentence_weakerThan_of_consistent hΓ e (not_inconsistent_iff_consistent.mp hC);
  exact hcon.not_inc <| T.standardProvability.inconsistent_of_provable_localReflectionOn_insert
    (fun _ hσ ↦ by simpa using hσ) hθ fun hσ ↦ hle.pbl (h hσ);

theorem not_provable_localReflectionOn_union
    (hΓ : ∀ σ ∈ U', ∃ φ : Prenex Γ (n + 1) Empty 0, φ.val = σ) (e : T ∪ U ≊ T ∪ U')
    (hC : Consistent (T ∪ U)) :
    ¬T ∪ U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy Γ.alt (n + 1)] T :=
  fun h ↦ (inconsistent_of_provable_localReflectionOn_union hΓ e h).not_con hC

end FFL.FirstOrder.Arithmetic
