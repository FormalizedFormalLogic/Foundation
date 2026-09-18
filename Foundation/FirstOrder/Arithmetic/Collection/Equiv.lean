module

public import Foundation.FirstOrder.Arithmetic.Prenex

/-!
# Equivalences between the collection schemata

Collection for the definable relations of a model of `𝗕 Γ s`, the collapse `𝗕⁺ Γ s ≊ 𝗕 Γ s`, the
equivalence `𝗕𝚺 (s + 1) ≊ 𝗕𝚷 s`, and `𝗜𝚺 s` from `𝗕𝚺 (s + 1)`.

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
  . exact models_of_ss (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕 Γ s) Set.subset_union_left;
  . exact CollectionScheme.models_of_collection CollectionOnHierarchy.collection_of_definable;

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

private lemma definable_pair {ℌ : HierarchySymbol} {Q : (Fin (k + 2) → V) → Prop}
    (hQ : ℌ.Definable Q) (e : Fin k → V) : ℌ.DefinableRel fun x v : V ↦ Q (v :> x :> e) :=
  (HierarchySymbol.Definable.retractiont 2 hQ
    (#1 :> #0 :> fun i : Fin k ↦ (&(e i) : ArithmeticSemiterm V 2))).of_iff fun w ↦
    Iff.of_eq <| congrArg Q <| funext fun i ↦ by
      cases i using Fin.cases with
      | zero => simp;
      | succ i => cases i using Fin.cases <;> simp;

private structure MonotoneWitness (P : (Fin k → V) → Prop) (Q : (Fin (k + 1) → V) → Prop) : Prop where
  monotone : ∀ e v v', v ≤ v' → Q (v :> e) → Q (v' :> e)
  sound : ∀ e v, Q (v :> e) → P e
  complete : ∀ e, P e → ∃ v, Q (v :> e)

private lemma MonotoneWitness.and [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {P₁ P₂ : (Fin k → V) → Prop}
    {Q₁ Q₂ : (Fin (k + 1) → V) → Prop} (hM₁ : MonotoneWitness P₁ Q₁) (hM₂ : MonotoneWitness P₂ Q₂) :
    MonotoneWitness (fun e ↦ P₁ e ∧ P₂ e) (fun w ↦ Q₁ w ∧ Q₂ w) where
  monotone e v v' hv h := ⟨hM₁.monotone e v v' hv h.1, hM₂.monotone e v v' hv h.2⟩;
  sound e v h := ⟨hM₁.sound e v h.1, hM₂.sound e v h.2⟩;
  complete e h := by
    obtain ⟨v₁, hv₁⟩ := hM₁.complete e h.1;
    obtain ⟨v₂, hv₂⟩ := hM₂.complete e h.2;
    exact ⟨max v₁ v₂, hM₁.monotone e v₁ _ (le_max_left _ _) hv₁, hM₂.monotone e v₂ _ (le_max_right _ _) hv₂⟩;

private lemma MonotoneWitness.or {P₁ P₂ : (Fin k → V) → Prop} {Q₁ Q₂ : (Fin (k + 1) → V) → Prop}
    (hM₁ : MonotoneWitness P₁ Q₁) (hM₂ : MonotoneWitness P₂ Q₂) :
    MonotoneWitness (fun e ↦ P₁ e ∨ P₂ e) (fun w ↦ Q₁ w ∨ Q₂ w) where
  monotone e v v' hv h := h.imp (hM₁.monotone e v v' hv) (hM₂.monotone e v v' hv);
  sound e v h := h.imp (hM₁.sound e v) (hM₂.sound e v);
  complete e h := by
    rcases h with h | h;
    . exact (hM₁.complete e h).imp fun v hv ↦ by tauto;
    . exact (hM₂.complete e h).imp fun v hv ↦ by tauto;

private lemma MonotoneWitness.bexs {k : ℕ} {P : (Fin (k + 1) → V) → Prop} {Q : (Fin (k + 2) → V) → Prop}
    (hM : MonotoneWitness P Q) (bound : (Fin k → V) → V) :
    MonotoneWitness (fun e ↦ ∃ x < bound e, P (x :> e))
      (fun w : Fin (k + 1) → V ↦ ∃ x < bound (w ·.succ), Q (w 0 :> x :> (w ·.succ))) where
  monotone e v v' hv h := by
    obtain ⟨x, hx, hxv⟩ := h;
    exact ⟨x, hx, hM.monotone (x :> e) v v' hv hxv⟩;
  sound e v h := by
    obtain ⟨x, hx, hxv⟩ := h;
    exact ⟨x, hx, hM.sound (x :> e) v hxv⟩;
  complete e h := by
    obtain ⟨x, hx, hxe⟩ := h;
    obtain ⟨v, hv⟩ := hM.complete (x :> e) hxe;
    exact ⟨v, x, hx, hv⟩;

private lemma MonotoneWitness.exs [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {k : ℕ} {P : (Fin (k + 1) → V) → Prop}
    {Q : (Fin (k + 2) → V) → Prop} (hM : MonotoneWitness P Q) :
    MonotoneWitness (fun e ↦ ∃ x, P (x :> e))
      (fun w : Fin (k + 1) → V ↦ ∃ x < w 0, Q (w 0 :> x :> (w ·.succ))) where
  monotone e v v' hv h := by
    obtain ⟨x, hx, hxv⟩ := h;
    exact ⟨x, lt_of_lt_of_le hx hv, hM.monotone (x :> e) v v' hv hxv⟩;
  sound e v h := by
    obtain ⟨x, -, hxv⟩ := h;
    exact ⟨x, hM.sound (x :> e) v hxv⟩;
  complete e h := by
    obtain ⟨x, hxe⟩ := h;
    obtain ⟨v, hv⟩ := hM.complete (x :> e) hxe;
    exact ⟨max (x + 1) v, x, lt_of_lt_of_le (lt_add_one x) (le_max_left _ _),
      hM.monotone (x :> e) v _ (le_max_right _ _) hv⟩;

variable [V↓[ℒₒᵣ] ⊧* 𝗕𝚷 s]

private lemma MonotoneWitness.ball [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {k : ℕ} {P : (Fin (k + 1) → V) → Prop}
    {Q : (Fin (k + 2) → V) → Prop} (hQ : 𝚷-[s].Definable Q) (hM : MonotoneWitness P Q)
    (bound : (Fin k → V) → V) :
    MonotoneWitness (fun e ↦ ∀ x < bound e, P (x :> e))
      (fun w : Fin (k + 1) → V ↦ ∀ x < bound (w ·.succ), Q (w 0 :> x :> (w ·.succ))) where
  monotone e v v' hv h x hx := hM.monotone (x :> e) v v' hv (h x hx);
  sound e v h x hx := hM.sound (x :> e) v (h x hx);
  complete e h := by
    obtain ⟨b, hb⟩ := CollectionOnHierarchy.collection_of_definable (Γ := 𝚷) (definable_pair hQ e) (bound e)
      fun x hx ↦ hM.complete (x :> e) (h x hx);
    exact ⟨b, fun x hx ↦ by
      obtain ⟨v, hvb, hv⟩ := hb x hx;
      exact hM.monotone (x :> e) v b hvb.le hv⟩;

private lemma exists_monotoneWitness {k : ℕ} {P : (Fin k → V) → Prop} (hP : 𝚺-[s + 1].Definable P) :
    ∃ Q : (Fin (k + 1) → V) → Prop, 𝚷-[s].Definable Q ∧ MonotoneWitness P Q := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy 𝚷 s;
  induction k, P, hP using HierarchySymbol.Definable.sigma_succ_induction with
  | @pi k P hP =>
    use fun w ↦ P (w ·.succ);
    and_intros;
    . exact hP.retraction Fin.succ;
    . constructor;
      . intro e v v' _ h;
        simpa using h;
      . intro e v h;
        simpa using h;
      . intro e h;
        use 0;
        simpa using h;
  | @and k P₁ P₂ _ _ ih₁ ih₂ =>
    obtain ⟨Q₁, hQ₁, hM₁⟩ := ih₁;
    obtain ⟨Q₂, hQ₂, hM₂⟩ := ih₂;
    exact ⟨fun w ↦ Q₁ w ∧ Q₂ w, hQ₁.and hQ₂, hM₁.and hM₂⟩;
  | @or k P₁ P₂ _ _ ih₁ ih₂ =>
    obtain ⟨Q₁, hQ₁, hM₁⟩ := ih₁;
    obtain ⟨Q₂, hQ₂, hM₂⟩ := ih₂;
    exact ⟨fun w ↦ Q₁ w ∨ Q₂ w, hQ₁.or hQ₂, hM₁.or hM₂⟩;
  | @ball k P t _ ih =>
    obtain ⟨Q, hQ, hM⟩ := ih;
    use fun w : Fin (k + 1) → V ↦ ∀ x < t.val (w ·.succ) id, Q (w 0 :> x :> (w ·.succ));
    and_intros;
    . apply HierarchySymbol.Definable.of_iff
        (HierarchySymbol.Definable.ball
          (P := fun (v : Fin (k + 1) → V) (x : V) ↦ Q (v 0 :> x :> (v ·.succ)))
          (definable_swap hQ) (Rew.bShift t));
      simp [Semiterm.val_bShift'];
    . exact hM.ball hQ (t.val · id);
  | @bexs k P t _ ih =>
    obtain ⟨Q, hQ, hM⟩ := ih;
    use fun w : Fin (k + 1) → V ↦ ∃ x < t.val (w ·.succ) id, Q (w 0 :> x :> (w ·.succ));
    and_intros;
    . apply HierarchySymbol.Definable.of_iff
        (HierarchySymbol.Definable.bexs
          (P := fun (v : Fin (k + 1) → V) (x : V) ↦ Q (v 0 :> x :> (v ·.succ)))
          (definable_swap hQ) (Rew.bShift t));
      intro w;
      simp [Semiterm.val_bShift'];
    . exact hM.bexs (t.val · id);
  | @exs k P _ ih =>
    obtain ⟨Q, hQ, hM⟩ := ih;
    use fun w : Fin (k + 1) → V ↦ ∃ x < w 0, Q (w 0 :> x :> (w ·.succ));
    and_intros;
    . apply HierarchySymbol.Definable.of_iff
        (HierarchySymbol.Definable.bexs
          (P := fun (v : Fin (k + 1) → V) (x : V) ↦ Q (v 0 :> x :> (v ·.succ)))
          (definable_swap hQ) #0);
      simp;
    . exact hM.exs;

lemma BPi.collection_sigma_succ {R : V → V → Prop}
    (hR : 𝚺-[s + 1].DefinableRel R) (a : V) (h : ∀ x < a, ∃ y, R x y) :
    ∃ b, ∀ x < a, ∃ y < b, R x y := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy 𝚷 s;
  obtain ⟨Q, hQ, hM⟩ := exists_monotoneWitness hR;
  have hS : 𝚷-[s].DefinableRel fun x v : V ↦ ∃ y < v, Q ![v, x, y] :=
    HierarchySymbol.Definable.of_iff
      (HierarchySymbol.Definable.bexs
        (P := fun (w : Fin 2 → V) (y : V) ↦ Q ![w 1, w 0, y])
        ((hQ.retraction ![2, 1, 0]).of_iff fun u ↦
          Iff.of_eq <| congrArg Q <| funext fun i ↦ by match i with | 0 | 1 | 2 => simp) #1)
      (by simp);
  obtain ⟨b, hb⟩ := CollectionOnHierarchy.collection_of_definable (Γ := 𝚷) hS a <| by
    intro x hx;
    obtain ⟨y, hy⟩ := h x hx;
    obtain ⟨v, hv⟩ := hM.complete ![x, y] (by simpa using hy);
    use max v (y + 1), y;
    and_intros;
    . exact lt_of_lt_of_le (lt_add_one y) (le_max_right v (y + 1));
    . exact hM.monotone ![x, y] v _ (le_max_left v (y + 1)) hv;
  use b;
  intro x hx;
  obtain ⟨v, hvb, y, hyv, hy⟩ := hb x hx;
  exact ⟨y, lt_trans hyv hvb, by simpa using hM.sound ![x, y] v hy⟩;

instance BPi.models_BSigma_succ : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (s + 1) := by
  apply Semantics.ModelsSet.union_iff.mpr;
  and_intros;
  . exact models_of_ss (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 s) Set.subset_union_left;
  . exact models_of_ss (CollectionScheme.models_of_collection (Γ := 𝚺) BPi.collection_sigma_succ)
      (CollectionScheme_subset (·.hierarchy));

lemma exists_pi_definableRel_iff {P : V → Prop} (hP : 𝚺-[s + 1].DefinablePred P) :
    ∃ Q : V → V → Prop, 𝚷-[s].DefinableRel Q ∧ ∀ x, P x ↔ ∃ w, Q x w := by
  obtain ⟨Q, hQ, hM⟩ := exists_monotoneWitness hP;
  use fun x w ↦ Q ![w, x];
  and_intros;
  . exact (hQ.retraction ![1, 0]).of_iff fun u ↦
      Iff.of_eq <| congrArg Q <| funext fun i ↦ by match i with | 0 | 1 => simp;
  . intro x;
    constructor;
    . intro h;
      exact hM.complete ![x] (by simpa using h);
    . rintro ⟨w, hw⟩;
      simpa using hM.sound ![x] w hw;

@[instance]
theorem BSigma_succ_weakerThan_BPi : 𝗕𝚺 (s + 1) ⪯ 𝗕𝚷 s :=
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance

@[instance]
theorem BSigma_succ_equiv_BPi : 𝗕𝚺 (s + 1) ≊ 𝗕𝚷 s :=
  Equiv.antisymm_iff.mpr ⟨BSigma_succ_weakerThan_BPi, CollectionOnHierarchy_weakerThan_BSigma_succ 𝚷 s⟩

end BSigma_succ_BPi

section ISigma_BSigma_succ

/-! ### `𝗜𝚺 s` from `𝗕𝚺 (s + 1)` -/

variable {P : V → Prop} {Q : V → V → Prop}

private lemma definable_step (hQ : 𝚷-[s].DefinableRel Q) :
    𝚷-[s + 1].DefinableRel fun x w ↦ (¬∃ z, Q x z) ∨ Q (x + 1) w := by
  have hex : 𝚺-[s + 1].DefinablePred fun x ↦ ∃ z, Q x z :=
    HierarchySymbol.Definable.exs <|
      .of_iff ((hQ.of_lt (s := s + 1) (Γ := 𝚺) (by simp)).retraction ![1, 0]) (by intro w; simp);
  apply HierarchySymbol.Definable.or;
  . exact .of_iff (hex.notSigma.retraction ![0]) (by intro v; simp);
  . exact .of_iff (HierarchySymbol.Definable.retractiont 2
      (hQ.of_lt (s := s + 1) (Γ := 𝚷) (by simp)) ![‘#0 + 1’, #1]) (by intro v; simp);

private lemma definable_bounded (hQ : 𝚷-[s].DefinableRel Q) (a u : V) :
    𝚷-[s].DefinablePred fun x ↦ ∃ y < u, Q x y ∨ a < x := by
  have hlt : 𝚷-[s].Definable fun w : Fin 2 → V ↦ a < w 1 := .of_iff
    (HierarchySymbol.Definable.retractiont 2
    (inferInstance : 𝚷-[s].DefinableRel (LT.lt : V → V → Prop)) ![&a, #1]) (by intro w; simp);
  have h : 𝚷-[s].Definable
      fun v : Fin 1 → V ↦ ∃ y < (&u : ArithmeticSemiterm V 1).val v id, Q (v 0) y ∨ a < v 0 := by
    apply HierarchySymbol.Definable.bexs;
    exact .of_iff ((hQ.retraction ![1, 0]).or hlt) (by intro w; simp);
  exact h.of_iff (by intro v; simp);

lemma succ_induction_of_exists_pi [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s] [V↓[ℒₒᵣ] ⊧* 𝗕𝚷 (s + 1)]
    (hQ : 𝚷-[s].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∃ w, Q x w)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := by
  intro a;
  obtain ⟨v, hv⟩ := CollectionOnHierarchy.collection_of_definable (Γ := 𝚷)
    (definable_step hQ) a <| by
      intro x _;
      by_cases hx : ∃ z, Q x z;
      . exact ((hPQ (x + 1)).mp (succ x ((hPQ x).mpr hx))).imp fun w hw ↦ .inr hw;
      . exact ⟨0, .inl hx⟩;
  obtain ⟨w₀, hw₀⟩ := (hPQ 0).mp zero;
  have hw₀' : w₀ < max v (w₀ + 1) := lt_of_lt_of_le (lt_add_one w₀) (le_max_right v (w₀ + 1));
  have hpos : (0 : V) < max v (w₀ + 1) := lt_of_le_of_lt (by simp) hw₀';
  have key : ∀ x, ∃ y < max v (w₀ + 1), Q x y ∨ a < x := by
    apply InductionOnHierarchy.succ_induction 𝚷 s (definable_bounded hQ a _) ⟨w₀, hw₀', .inl hw₀⟩;
    rintro x ⟨y, -, hy | hy⟩;
    . by_cases hxa : x < a;
      . obtain ⟨z, hzv, hz | hz⟩ := hv x hxa;
        . exact absurd ⟨y, hy⟩ hz;
        . exact ⟨z, lt_of_lt_of_le hzv (le_max_left v (w₀ + 1)), .inl hz⟩;
      . exact ⟨0, hpos, .inr (lt_of_le_of_lt (not_lt.mp hxa) (lt_add_one x))⟩;
    . exact ⟨0, hpos, .inr (lt_trans hy (lt_add_one x))⟩;
  obtain ⟨y, -, hy | hy⟩ := key a;
  . exact (hPQ a).mpr ⟨y, hy⟩;
  . exact absurd hy (lt_irrefl a);

private lemma models_ISigma_succ [V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (s + 2)] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (s + 2));
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 s := models_of_ss inferInstance
    ((CollectionOnHierarchy_subset_BSigma_succ 𝚷 s).trans
    (CollectionOnHierarchy_subset_mono (Nat.le_succ (s + 1))));
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 (s + 1) :=
    models_of_ss inferInstance (CollectionOnHierarchy_subset_BSigma_succ 𝚷 (s + 1));

  suffices V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Hierarchy 𝚺 (s + 1)) by
    apply Semantics.ModelsSet.union_iff.mpr;
    simp_all;
  apply Semantics.ModelsSet.setOf_iff.mpr;
  rintro _ ⟨φ, hφ, rfl⟩;
  suffices ∀ f : ℕ → V, φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) → ∀ x, φ.Eval ![x] f by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs, Matrix.constant_eq_singleton];
  intro f;
  obtain ⟨Q, hQ, hiff⟩ := exists_pi_definableRel_iff (definablePred_of_hierarchy hφ f);
  exact succ_induction_of_exists_pi hQ hiff;

lemma models_ISigma_of_models_BSigma_succ [V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (s + 1)] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := by
  rename_i hn;
  induction s generalizing hn with
  | zero =>
    exact models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 1);
  | succ s ih =>
    have : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (s + 1) :=
      models_of_ss inferInstance <| CollectionOnHierarchy_subset_mono <| Nat.le_succ (s + 1);
    exact models_ISigma_succ;

@[instance]
theorem ISigma_weakerThan_BSigma_succ : 𝗜𝚺 s ⪯ 𝗕𝚺 (s + 1) :=
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ models_ISigma_of_models_BSigma_succ

end ISigma_BSigma_succ

end FFL.FirstOrder.Arithmetic
