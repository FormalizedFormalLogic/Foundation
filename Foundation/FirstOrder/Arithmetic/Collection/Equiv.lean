module

public import Foundation.FirstOrder.Arithmetic.Prenex

/-!
# Equivalences between the collection schemata

Collection for the definable relations of a model of `𝗕 Γ s`, the collapse `𝗕⁺ Γ s ≊ 𝗕 Γ s`, the
equivalence `𝗕𝚺 (s + 1) ≊ 𝗕𝚷 s`, and `𝗜𝚺⁺ s` from `𝗕𝚺 (s + 1)`.

## References

- [HP98]
- [Bus98]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

variable {V : Type*} [ORingStructure V] {s : ℕ} {k : ℕ}

section BroadHierarchy

/-! ### Collection for the broad hierarchy -/

lemma CollectionOnHierarchy.collection_of_definable {Γ : Polarity} [V↓[ℒₒᵣ] ⊧* 𝗕 Γ s]
    {R : V → V → Prop} (hR : Γ-[s].DefinableRel R) (a : V) (h : ∀ x < a, ∃ y, R x y) :
    ∃ b, ∀ x < a, ∃ y < b, R x y :=
  CollectionOnHierarchy.collection Γ s (StrictDefinable.of_definable (Γ' := Γ) hR) a h

instance CollectionOnHierarchy.models_CollectionOnBroadHierarchy {Γ : Polarity}
    [V↓[ℒₒᵣ] ⊧* 𝗕 Γ s] : V↓[ℒₒᵣ] ⊧* 𝗕⁺ Γ s := by
  apply Semantics.ModelsSet.union_iff.mpr;
  and_intros;
  · exact models_of_ss (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕 Γ s) Set.subset_union_left;
  · exact CollectionScheme.models_of_collection CollectionOnHierarchy.collection_of_definable;

/-- - [Bus98, pp. 84-85] -/
theorem CollectionOnBroadHierarchy_equiv_CollectionOnHierarchy {Γ : Polarity} {s : ℕ}
  : 𝗕⁺ Γ s ≊ 𝗕 Γ s := Equiv.antisymm ⟨
    weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance,
    CollectionOnHierarchy_weakerThan_CollectionOnBroadHierarchy Γ s
  ⟩

end BroadHierarchy

section BSigma_succ_BPi

/-! ### `𝗕𝚺 (s + 1)` and `𝗕𝚷 s` -/

private lemma definable_swap {ℌ : HierarchySymbol} {Q : (Fin (k + 2) → V) → Prop}
    (hQ : ℌ.Definable Q) :
    ℌ.Definable fun u : Fin (k + 2) → V ↦
      Q (u (0 : Fin (k + 1)).succ :> u 0 :> fun i : Fin k ↦ u i.succ.succ) :=
  (hQ.retraction ((0 : Fin (k + 1)).succ :> 0 :> fun i : Fin k ↦ i.succ.succ)).of_iff fun u ↦
    Iff.of_eq <| congrArg Q <| funext fun i ↦ by
      cases i using Fin.cases with
      | zero => simp;
      | succ i => cases i using Fin.cases <;> simp;

private structure MonotoneWitness (P : (Fin k → V) → Prop)
    (Q : (Fin (k + 1) → V) → Prop) : Prop where
  monotone : ∀ e v v', v ≤ v' → Q (v :> e) → Q (v' :> e)
  iff : ∀ e, P e ↔ ∃ v, Q (v :> e)

variable [V↓[ℒₒᵣ] ⊧* 𝗕𝚷s]

private lemma exists_monotoneWitness {P : (Fin k → V) → Prop} (hP : 𝚺-[s + 1].Definable P) :
  ∃ Q : (Fin (k + 1) → V) → Prop, 𝚷-[s].Definable Q ∧ MonotoneWitness P Q := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕 𝚷 s);
  induction k, P, hP using HierarchySymbol.Definable.sigma_succ_induction with
  | @pi k P hP =>
    use fun w ↦ P (w ·.succ);
    and_intros;
    · exact hP.retraction Fin.succ;
    · constructor <;> simp;
  | @and k P₁ P₂ _ _ ih₁ ih₂ =>
    obtain ⟨Q₁, hQ₁, hM₁⟩ := ih₁;
    obtain ⟨Q₂, hQ₂, hM₂⟩ := ih₂;
    use fun w ↦ Q₁ w ∧ Q₂ w;
    and_intros;
    · exact .and hQ₁ hQ₂;
    · constructor;
      · intro e v v' hv h;
        exact ⟨hM₁.monotone e v v' hv h.1, hM₂.monotone e v v' hv h.2⟩;
      · intro e;
        constructor;
        · rintro ⟨h₁, h₂⟩;
          obtain ⟨v₁, hv₁⟩ := (hM₁.iff e).mp h₁;
          obtain ⟨v₂, hv₂⟩ := (hM₂.iff e).mp h₂;
          use max v₁ v₂;
          and_intros;
          · exact hM₁.monotone _ _ _ (by grind) hv₁;
          · exact hM₂.monotone _ _ _ (by grind) hv₂;
        · rintro ⟨v, h₁, h₂⟩;
          exact ⟨(hM₁.iff e).mpr ⟨v, h₁⟩, (hM₂.iff e).mpr ⟨v, h₂⟩⟩;
  | @or k P₁ P₂ _ _ ih₁ ih₂ =>
    obtain ⟨Q₁, hQ₁, hM₁⟩ := ih₁;
    obtain ⟨Q₂, hQ₂, hM₂⟩ := ih₂;
    use fun w ↦ Q₁ w ∨ Q₂ w;
    and_intros;
    · exact .or hQ₁ hQ₂;
    · constructor;
      · intro e v v' hv h;
        exact h.imp (hM₁.monotone e v v' hv) (hM₂.monotone e v v' hv);
      · intro e;
        simp only [hM₁.iff, hM₂.iff, exists_or];
  | @ball k P t _ ih =>
    obtain ⟨Q, hQ, hM⟩ := ih;
    use fun w : Fin (k + 1) → V ↦ ∀ x < t.val (w ·.succ) id, Q (w 0 :> x :> (w ·.succ));
    and_intros;
    . apply Bounding.HierarchySymbol.Definable.of_iff $ HierarchySymbol.Definable.ball
        (P := fun (v : Fin (k + 1) → V) (x : V) ↦ Q (v 0 :> x :> (v ·.succ)))
        (definable_swap hQ) (Rew.bShift t);
      simp [Semiterm.val_bShift'];
    · constructor;
      · intro e v v' hv h x hx;
        exact hM.monotone (x :> e) v v' hv (h x hx);
      · intro e;
        constructor;
        · intro h;
          have hQe : 𝚷-[s].DefinableRel fun x v : V ↦ Q (v :> x :> e) :=
            (Bounding.HierarchySymbol.Definable.retractiont (n := 2) hQ
              (#1 :> #0 :> fun i : Fin k ↦ (&(e i) : ArithmeticSemiterm V 2))).of_iff fun w ↦
              Iff.of_eq <| congrArg Q <| funext fun i ↦ by
                cases i using Fin.cases with
                | zero => simp;
                | succ i => cases i using Fin.cases <;> simp;
          obtain ⟨b, hb⟩ := CollectionOnHierarchy.collection_of_definable (Γ := 𝚷) hQe
            (t.val e id) fun x hx ↦ (hM.iff (x :> e)).mp (h x hx);
          use b;
          intro x hx;
          obtain ⟨v, hvb, hv⟩ := hb x hx;
          exact hM.monotone (x :> e) v b hvb.le hv;
        · rintro ⟨v, hv⟩ x hx;
          exact (hM.iff (x :> e)).mpr ⟨v, hv x hx⟩;
  | @bexs k P t _ ih =>
    obtain ⟨Q, hQ, hM⟩ := ih;
    use fun w : Fin (k + 1) → V ↦ ∃ x < t.val (w ·.succ) id, Q (w 0 :> x :> (w ·.succ));
    and_intros;
    . apply Bounding.HierarchySymbol.Definable.of_iff
        (HierarchySymbol.Definable.bexs
          (P := fun (v : Fin (k + 1) → V) (x : V) ↦ Q (v 0 :> x :> (v ·.succ)))
          (definable_swap hQ) (Rew.bShift t));
      intro w;
      simp [Semiterm.val_bShift'];
    · constructor;
      · intro e v v' hv h;
        obtain ⟨x, hx, hxv⟩ := h;
        exact ⟨x, hx, hM.monotone (x :> e) v v' hv hxv⟩;
      · intro e;
        constructor;
        · rintro ⟨x, hx, hxe⟩;
          obtain ⟨v, hv⟩ := (hM.iff (x :> e)).mp hxe;
          exact ⟨v, x, hx, hv⟩;
        · rintro ⟨v, x, hx, hxv⟩;
          exact ⟨x, hx, (hM.iff (x :> e)).mpr ⟨v, hxv⟩⟩;
  | @exs k P _ ih =>
    obtain ⟨Q, hQ, hM⟩ := ih;
    use fun w : Fin (k + 1) → V ↦ ∃ x < w 0, Q (w 0 :> x :> (w ·.succ));
    and_intros;
    . apply Bounding.HierarchySymbol.Definable.of_iff
        (HierarchySymbol.Definable.bexs
          (P := fun (v : Fin (k + 1) → V) (x : V) ↦ Q (v 0 :> x :> (v ·.succ)))
          (definable_swap hQ) #0);
      simp;
    · constructor;
      · intro e v v' hv h;
        obtain ⟨x, hx, hxv⟩ := h;
        use x;
        and_intros;
        · exact lt_of_lt_of_le hx hv;
        · exact hM.monotone (x :> e) v v' hv hxv;
      · intro e;
        constructor;
        · rintro ⟨x, hxe⟩;
          obtain ⟨v, hv⟩ := (hM.iff (x :> e)).mp hxe;
          use max (x + 1) v, x;
          and_intros;
          · exact lt_of_lt_of_le (lt_add_one x) (le_max_left _ _);
          · exact hM.monotone (x :> e) v _ (le_max_right _ _) hv;
        · rintro ⟨v, x, -, hxv⟩;
          exact ⟨x, (hM.iff (x :> e)).mpr ⟨v, hxv⟩⟩;

lemma BPi.collection_sigma_succ {R : V → V → Prop}
    (hR : 𝚺-[s + 1].DefinableRel R) (a : V) (h : ∀ x < a, ∃ y, R x y) :
    ∃ b, ∀ x < a, ∃ y < b, R x y := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕 𝚷 s);
  obtain ⟨Q, hQ, hM⟩ := exists_monotoneWitness hR;
  have hS : 𝚷-[s].DefinableRel fun x v : V ↦ ∃ y < v, Q ![v, x, y] := Bounding.HierarchySymbol.Definable.of_iff
    (HierarchySymbol.Definable.bexs
      (P := fun (w : Fin 2 → V) (y : V) ↦ Q ![w 1, w 0, y])
      ((hQ.retraction ![2, 1, 0]).of_iff fun u ↦
        Iff.of_eq <| congrArg Q <| funext fun i ↦ by match i with | 0 | 1 | 2 => simp) #1)
    (by simp);
  obtain ⟨b, hb⟩ := CollectionOnHierarchy.collection_of_definable (Γ := 𝚷) hS a <| by
    intro x hx;
    obtain ⟨y, hy⟩ := h x hx;
    obtain ⟨v, hv⟩ := (hM.iff ![x, y]).mp (by simpa using hy);
    use max v (y + 1), y;
    and_intros;
    · exact lt_of_lt_of_le (lt_add_one y) (le_max_right v (y + 1));
    · exact hM.monotone ![x, y] v _ (le_max_left v (y + 1)) hv;
  use b;
  intro x hx;
  obtain ⟨v, hvb, y, hyv, hy⟩ := hb x hx;
  exact ⟨y, lt_trans hyv hvb, by simpa using (hM.iff ![x, y]).mpr ⟨v, hy⟩⟩;

instance BPi.models_BSigma_succ : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (s + 1) := by
  apply Semantics.ModelsSet.union_iff.mpr;
  and_intros;
  · exact models_of_ss (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 s) Set.subset_union_left;
  · exact models_of_ss (CollectionScheme.models_of_collection (Γ := 𝚺) BPi.collection_sigma_succ)
      (CollectionScheme_subset (·.hierarchy));

lemma exists_pi_definableRel_iff {P : V → Prop} (hP : 𝚺-[s + 1].DefinablePred P) :
  ∃ Q, 𝚷-[s].DefinableRel Q ∧ ∀ x, P x ↔ ∃ w, Q x w := by
  obtain ⟨Q, hQ, hM⟩ := exists_monotoneWitness hP;
  use (fun x w ↦ Q ![w, x]);
  and_intros;
  · apply (hQ.retraction ![1, 0]).of_iff;
    intro;
    apply Iff.of_eq;
    apply congrArg Q;
    funext i;
    match i with | 0 | 1 => simp;
  · intro x;
    simpa using hM.iff ![x];

@[instance]
theorem BSigma_succ_weakerThan_BPi : 𝗕𝚺 (s + 1) ⪯ 𝗕𝚷 s :=
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance

@[instance]
theorem BSigma_succ_equiv_BPi : 𝗕𝚺 (s + 1) ≊ 𝗕𝚷 s :=
  Equiv.antisymm ⟨inferInstance, CollectionOnHierarchy_weakerThan_BSigma_succ 𝚷 s⟩

end BSigma_succ_BPi

section ISigma_BSigma_succ

/-! ### `𝗜𝚺⁺ s` from `𝗕𝚺 (s + 1)` -/

variable {P : V → Prop} {Q : V → V → Prop}

lemma succ_induction_of_exists_pi [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺s] [V↓[ℒₒᵣ] ⊧* 𝗕𝚷(s + 1)]
    (hQ : 𝚷-[s].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∃ w, Q x w)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺ s);
  intro a;
  have hstep : 𝚷-[s + 1].DefinableRel fun x w ↦ (¬∃ z, Q x z) ∨ Q (x + 1) w := by
    have hex : 𝚺-[s + 1].DefinablePred fun x ↦ ∃ z, Q x z :=
      Bounding.HierarchySymbol.Definable.exs <|
        .of_iff ((hQ.of_lt (s := s + 1) (Γ := 𝚺) (by simp)).retraction ![1, 0]) (by intro w; simp);
    apply Bounding.HierarchySymbol.Definable.or
    . exact .of_iff (hex.notSigma.retraction ![0]) (by intro v; simp);
    . exact .of_iff (Bounding.HierarchySymbol.Definable.retractiont (n := 2)
        (hQ.of_lt (s := s + 1) (Γ := 𝚷) (by simp)) ![‘#0 + 1’, #1]) (by intro v; simp);
  obtain ⟨v, hv⟩ := CollectionOnHierarchy.collection_of_definable (Γ := 𝚷) hstep a <| by
      intro x _;
      by_cases hx : ∃ z, Q x z;
      · exact ((hPQ (x + 1)).mp (succ x ((hPQ x).mpr hx))).imp fun w hw ↦ by tauto;
      · exact ⟨0, by tauto⟩;
  obtain ⟨w₀, hw₀⟩ := (hPQ 0).mp zero;
  obtain ⟨b, hvb, hw₀b⟩ : ∃ b : V, v ≤ b ∧ w₀ < b :=
    ⟨max v (w₀ + 1), le_max_left _ _, lt_of_lt_of_le (lt_add_one w₀) (le_max_right _ _)⟩;
  have hbdd : 𝚷-[s].DefinablePred fun x ↦ a < x ∨ ∃ y < b, Q x y := by
    have hlt : 𝚷-[s].Definable fun v : Fin 1 → V ↦ a < v 0 := .of_iff
      (Bounding.HierarchySymbol.Definable.retractiont (n := 1)
        (inferInstance : 𝚷-[s].DefinableRel (LT.lt : V → V → Prop)) ![&a, #0]) (by intro v; simp);
    have hbexs : 𝚷-[s].Definable
        fun v : Fin 1 → V ↦ ∃ y < (&b : ArithmeticSemiterm V 1).val v id, Q (v 0) y := by
      apply HierarchySymbol.Definable.bexs;
      exact .of_iff (hQ.retraction ![1, 0]) (by intro w; simp);
    exact (hlt.or hbexs).of_iff (by intro v; simp);
  have key : ∀ x, a < x ∨ ∃ y < b, Q x y := by
    apply InductionOnBroadHierarchy.succ_induction 𝚷 s hbdd;
    · right;
      exact ⟨w₀, hw₀b, hw₀⟩;
    · rintro x (hx | ⟨y, -, hy⟩);
      · left;
        exact lt_trans hx (lt_add_one x);
      · rcases lt_or_ge x a with hxa | hxa;
        · obtain ⟨z, hzv, hz | hz⟩ := hv x hxa;
          · exact absurd ⟨y, hy⟩ hz;
          · right;
            exact ⟨z, lt_of_lt_of_le hzv hvb, hz⟩;
        · left;
          exact lt_of_le_of_lt hxa (lt_add_one x);
  obtain hy | ⟨y, -, hy⟩ := key a;
  · exact absurd hy (lt_irrefl a);
  · exact (hPQ a).mpr ⟨y, hy⟩;

lemma models_IBroadSigma_of_models_BSigma_succ [V↓[ℒₒᵣ] ⊧* 𝗕𝚺(s + 1)] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺ s := by
  rename_i hn;
  induction s generalizing hn with
  | zero =>
    exact models_of_ss (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 1)
      (IBroadSigmaZero_subset_ISigmaZero.trans Set.subset_union_left);
  | succ s ih =>
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory hn;
    have : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (s + 1) := models_of_ss hn
      (CollectionOnHierarchy_subset_mono (by omega));
    have : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 s := models_of_ss hn
      ((CollectionOnHierarchy_subset_BSigma_succ 𝚷 s).trans
      (CollectionOnHierarchy_subset_mono (by omega)));
    have : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 (s + 1) := models_of_ss hn
      (CollectionOnHierarchy_subset_BSigma_succ 𝚷 (s + 1));
    suffices V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Hierarchy 𝚺 (s + 1)) by
      apply Semantics.ModelsSet.union_iff.mpr;
      simp_all;
    apply Semantics.ModelsSet.setOf_iff.mpr;
    rintro _ ⟨φ, hφ, rfl⟩;
    suffices ∀ f : ℕ → V, φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) →
        ∀ x, φ.Eval ![x] f by
      simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
        Matrix.constant_eq_singleton];
    intro f;
    obtain ⟨Q, hQ, hiff⟩ := exists_pi_definableRel_iff (definablePred_of_hierarchy hφ f);
    exact succ_induction_of_exists_pi hQ hiff;

@[instance]
theorem IBroadSigma_weakerThan_BSigma_succ : 𝗜𝚺⁺ s ⪯ 𝗕𝚺 (s + 1) :=
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ models_IBroadSigma_of_models_BSigma_succ

end ISigma_BSigma_succ

end FFL.FirstOrder.Arithmetic
