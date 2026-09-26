module

public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Reflection
public import Foundation.FirstOrder.Incompleteness.Second

@[expose] public section
/-!
# Local reflection principles for arithmetic theories

Local reflection schemas `Rfn_Γ(T)` for arithmetic theories via the standard provability predicate:
their relation to consistency, their soundness, and their unboundedness over finite extensions.

## References

- [Lin97]
- [AB05]
-/

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment ProvabilityAbstraction

abbrev _root_.FFL.FirstOrder.Theory.localReflectionOn
    (T : ArithmeticTheory) [T.Δ₁] (Γ : ArithmeticSentence → Prop) : Set ArithmeticSentence :=
  T.standardProvability.reflOn Γ

notation "𝗥𝗳𝗻[" Γ "] " T:max => Theory.localReflectionOn T Γ

variable {T : ArithmeticTheory} [T.Δ₁]

@[instance]
lemma strictlyWeakerThan_localReflection [𝗜𝚺₁ ⪯ T] [Consistent T] :
    T ⪱ T ∪ 𝗥𝗳𝗻[Set.univ] T :=
  StrictlyWeakerThan.of_unprovable_provable (φ := T.consistent)
    (consistent_unprovable T)
    (Provability.con_of_localReflection _ trivial)

theorem localReflection_Pi1_equiv_con [𝗜𝚺₁ ⪯ T] : T ∪ 𝗥𝗳𝗻[Hierarchy 𝚷 1] T ≊ T ∪ T.Con := by
  apply Equiv.antisymm;
  constructor;
  · apply WeakerThan.ofAxm!;
    rintro φ (hφ | ⟨σ, hσ, rfl⟩);
    · exact by_axm (Set.mem_union_left _ hφ);
    · have : T.standardProvability.FormalizedCompleteOn (∼σ) :=
        ⟨provable_sigma_one_complete (by simpa using hσ.neg)⟩;
      have h₁ : T ∪ T.Con ⊢ T.standardProvability.con 🡒 T.standardProvability.refl σ :=
        WeakerThan.pbl (Provability.localReflection_of_con T.standardProvability);
      have h₂ : T ∪ T.Con ⊢ T.standardProvability.con :=
        by_axm (Set.mem_union_right _ rfl);
      cl_prover [h₁, h₂];
  · apply WeakerThan.ofAxm!;
    rintro φ (hφ | rfl);
    · exact by_axm (Set.mem_union_left _ hφ);
    · exact Provability.con_of_localReflection _ (by simp);

instance models_localReflectionOn {Γ : ArithmeticSentence → Prop} [ℕ↓[ℒₒᵣ] ⊧* T] :
    ℕ↓[ℒₒᵣ] ⊧* (T ∪ 𝗥𝗳𝗻[Γ] T) := by
  apply Semantics.modelsSet_iff.mpr;
  rintro φ (hφ | ⟨σ, _, rfl⟩);
  · exact Semantics.modelsSet_iff.mp inferInstance hφ;
  · have : ℕ↓[ℒₒᵣ] ⊧ T.standardProvability σ → ℕ↓[ℒₒᵣ] ⊧ σ := fun h ↦
      models_of_provable inferInstance (T.standardProvability.sound_on h);
    simpa using this;

@[instance]
lemma consistent_localReflection_of_sound [ℕ↓[ℒₒᵣ] ⊧* T] :
    Consistent (T ∪ 𝗥𝗳𝗻[Set.univ] T) :=
  Theory.consistent_of_satisfiable ⟨ℕ↓[ℒₒᵣ], models_localReflectionOn (Γ := Set.univ)⟩

section Sigma1Sound

variable [T.SoundOnHierarchy 𝚺 1]

@[instance] theorem consistent_localReflection_of_Sigma1_sound :
    Consistent (T ∪ 𝗥𝗳𝗻[Set.univ] T) := by
  classical
  apply consistent_compact.mpr;
  intro F hF hFfin;
  -- The instances of `Rfn(T)` in the finite part `F` come from a finite set `t` of sentences.
  obtain ⟨t, -, htfin, ht⟩ :=
    Set.Finite.exists_subset_finite_image_eq (s := Set.univ) (u := F \ T)
      (f := T.standardProvability.refl) ((by simpa using hFfin : F.Finite).sdiff)
      fun ψ hψ ↦ (AdjunctiveSet.subset_iff.mp hF ψ hψ.1).resolve_left hψ.2;
  -- Adjoining `∼Pr(σ)` for those `σ ∈ t` that `T` does not prove proves every instance in `F`.
  set s : Finset ArithmeticSentence := htfin.toFinset.filter fun σ ↦ T ⊬ σ;
  have hD : T ⊬ (⩖ σ ∈ s, T.standardProvability σ) := by
    intro h;
    obtain ⟨σ, hσ, hmod⟩ : ∃ σ ∈ s, ℕ↓[ℒₒᵣ] ⊧ T.standardProvability σ := by
      simpa using T.soundOnHierarchy 𝚺 1 h (by simp [standardProvability_def]);
    exact (Finset.mem_filter.mp hσ).2 (T.standardProvability.sound_on hmod);
  set D : ArithmeticSentence := ⩖ σ ∈ s, T.standardProvability σ;
  have hcon : Consistent (adjoin (∼D) T) := unprovable_iff_consistent_adjoin.mp hD;
  apply hcon.of_le;
  apply WeakerThan.ofAxm!;
  intro ψ hψ;
  by_cases hψT : ψ ∈ T;
  · exact by_axm (by simp [hψT]);
  obtain ⟨σ, hσt, rfl⟩ : ψ ∈ T.standardProvability.refl '' t := ht ▸ ⟨hψ, hψT⟩;
  by_cases hσ : T ⊢ σ;
  · have h₁ : adjoin (∼D) T ⊢ σ := Axiomatized.to_adjoin hσ;
    cl_prover [h₁];
  · have h₁ : adjoin (∼D) T ⊢ T.standardProvability σ 🡒 D :=
      right_Fdisj'_intro _ _ (Finset.mem_filter.mpr ⟨htfin.mem_toFinset.mpr hσt, hσ⟩);
    have h₂ : adjoin (∼D) T ⊢ ∼D := Axiomatized.adjoin _ _;
    cl_prover [h₁, h₂];

end Sigma1Sound

section
variable [𝗜𝚺₁ ⪯ T] {Γ : Polarity} {n : ℕ} {π : ArithmeticSentence}

lemma provable_localReflectionOn_hierarchy_of_strictHierarchy [𝗜𝚺n ⪯ T]
    {S : ArithmeticTheory} (hTS : T ⪯ S) (h : S ⊢* 𝗥𝗳𝗻[StrictHierarchy Γ n] T) :
    S ⊢* 𝗥𝗳𝗻[Hierarchy Γ n] T := by
  have : 𝗜𝚺₁ ⪯ S := (inferInstance : 𝗜𝚺₁ ⪯ T).trans hTS;
  have : 𝗕𝚺 n ⪯ T := by
    rcases n with _ | m;
    · exact (CollectionOnHierarchy_weakerThan_of_le (Nat.zero_le 1)).trans
        (BSigma_weakerThan_ISigma.trans (inferInstance : 𝗜𝚺₁ ⪯ T));
    · exact BSigma_weakerThan_ISigma.trans (inferInstance : 𝗜𝚺 (m + 1) ⪯ T);
  rintro φ ⟨σ, hσ, rfl⟩;
  obtain ⟨σ', hσ', e⟩ := exists_strictHierarchy_of_hierarchy (Γ := Γ) T hσ;
  have he : T ⊢ σ 🡘 σ' := by simpa using e;
  have hinst : S ⊢ T.standardProvability.refl σ' :=
    h ((Provability.mem_localReflectionOn_iff _).mpr ⟨σ', hσ', rfl⟩);
  have hext : S ⊢ T.standardProvability σ 🡘 T.standardProvability σ' :=
    WeakerThan.pbl (Provability.ext (𝔅 := T.standardProvability) he);
  have he' : S ⊢ σ 🡘 σ' := hTS.pbl he;
  cl_prover [hinst, hext, he'];

theorem inconsistent_of_provable_localReflectionOn_insert [𝗜𝚺n ⪯ T]
    (hπ : Hierarchy Γ n π) (h : insert π T ⊢* 𝗥𝗳𝗻[StrictHierarchy Γ.alt n] T) :
    Inconsistent (insert π T) :=
  T.standardProvability.inconsistent_of_provable_localReflectionOn_insert
    (fun _ hσ ↦ by simpa using hσ) hπ
    (provable_localReflectionOn_hierarchy_of_strictHierarchy
      (WeakerThan.ofSubset (Set.subset_insert _ _)) h)

theorem not_provable_localReflectionOn_insert [𝗜𝚺n ⪯ T]
    (hπ : Hierarchy Γ n π) [Consistent (insert π T)] :
    ¬insert π T ⊢* 𝗥𝗳𝗻[StrictHierarchy Γ.alt n] T :=
  fun h ↦ (inconsistent_of_provable_localReflectionOn_insert hπ h).not_con
    inferInstance

theorem inconsistent_of_provable_localReflectionOn_union_of_finite [𝗜𝚺n ⪯ T]
    {U U' : ArithmeticTheory} (e : U ≊ U') (hU' : U'.Finite) (hΓ : ∀ σ ∈ U', Hierarchy Γ n σ)
    (h : T ∪ U ⊢* 𝗥𝗳𝗻[StrictHierarchy Γ.alt n] T) : Inconsistent (T ∪ U) := by
  classical
  have e : T ∪ U ≊ T ∪ U' := Theory.equiv_union_right e T;
  have hmem : ∀ σ, σ ∈ hU'.toFinset.toList ↔ σ ∈ U' := by simp;
  have hconj : Hierarchy Γ n (⋀hU'.toFinset.toList) :=
    Hierarchy.list_conj₂_iff.mpr fun σ hσ ↦ hΓ σ ((hmem σ).mp hσ);
  have hle : T ∪ U' ⪯ insert (⋀hU'.toFinset.toList) T := WeakerThan.ofAxm! <| by
    rintro φ (hφ | hφ);
    · exact by_axm (Set.mem_insert_of_mem _ hφ);
    · exact mdp (left_Conj₂_intro ((hmem φ).mpr hφ)) (by_axm (Set.mem_insert _ _));
  have hge : insert (⋀hU'.toFinset.toList) T ⪯ T ∪ U' := WeakerThan.ofAxm! <| by
    rintro φ (rfl | hφ);
    · exact Conj₂_iff_forall_provable.mpr fun ψ hψ ↦
        by_axm (Set.mem_union_right _ ((hmem ψ).mp hψ));
    · exact by_axm (Set.mem_union_left _ hφ);
  exact (inconsistent_of_provable_localReflectionOn_insert hconj
    fun hσ ↦ (e.le.trans hle).pbl (h hσ)).of_ge (hge.trans e.symm.le);

end

end FFL.FirstOrder.Arithmetic
