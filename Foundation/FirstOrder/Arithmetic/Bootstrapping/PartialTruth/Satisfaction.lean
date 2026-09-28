module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Hierarchy
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.BoundedSatisfaction

/-!
# Satisfaction for strict prenex $\Sigma_n$ and $\Pi_n$ formulas

Satisfaction predicates `SigmaSatisfaction n` and `PiSatisfaction n` for the internally coded
strict prenex hierarchy: they are definable at level $\Sigma_{n + 1}$ and $\Pi_{n + 1}$, satisfy
the Tarski conditions, and are dual to each other, monotone in the level, and commute with
substitution of coded terms.

## References

- [HP98, 1.64, Lemma I.1.68(2), Lemma I.1.69, Theorem I.1.70, Definition I.1.74,
  Theorem I.1.75, Remark I.1.77, Definition I.1.78]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Vector append -/

section vecAppend

namespace VecAppend

def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y w. y = w”
  adjoin := .mkSigma “y x xs ih w. !adjoinDef y x ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil param := param 0
  adjoin (_ x _ ih) := x ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end VecAppend

noncomputable def vecAppend (v w : V) : V := VecAppend.construction.result ![w] v

@[simp] lemma vecAppend_nil (w : V) : vecAppend 0 w = w := by
  simp [vecAppend, VecAppend.construction];

@[simp] lemma vecAppend_adjoin (x v w : V) : vecAppend (x ∷ v) w = x ∷ vecAppend v w := by
  simp [vecAppend, VecAppend.construction];

def _root_.FFL.FirstOrder.Arithmetic.vecAppendDef : 𝚺ᴬ₁.Semisentence 3 :=
  VecAppend.blueprint.resultDef

instance vecAppend_defined : 𝚺ᴬ₁-Function₂ (vecAppend : V → V → V) via vecAppendDef :=
  VecAppend.construction.result_defined

instance vecAppend_definable : 𝚺ᴬ₁-Function₂ (vecAppend : V → V → V) :=
  vecAppend_defined.to_definable

instance vecAppend_definable' (Γ m) : Γᴬ-[m + 1]-Function₂ (vecAppend : V → V → V) :=
  vecAppend_definable.of_sigmaOne

@[simp] lemma len_vecAppend (v w : V) : len (vecAppend v w) = len v + len w := by
  induction v using adjoin_ISigma1.sigma1_succ_induction
  · definability;
  case nil => simp;
  case adjoin x v ih => simp [vecAppend_adjoin, ih, add_right_comm];

lemma vecAppend_assoc (u v e : V) :
    vecAppend (vecAppend u v) e = vecAppend u (vecAppend v e) := by
  induction u using adjoin_ISigma1.sigma1_succ_induction
  · definability;
  case nil => simp;
  case adjoin x u ih => simp [ih];

lemma exists_vecAppend_singleton {k w : V} (h : len w = k + 1) :
    ∃ u x, len u = k ∧ w = vecAppend u ?[x] := by
  have H : ∀ w : V, w ≠ 0 → ∃ u ≤ w, ∃ x ≤ w, len u + 1 = len w ∧ w = vecAppend u ?[x] := by
    intro w;
    induction w using adjoin_ISigma1.sigma1_succ_induction
    · definability;
    case nil => simp;
    case adjoin y w ih =>
      intro _;
      rcases eq_or_ne w 0 with rfl | hw;
      · exact ⟨0, by simp, y, le_of_lt (lt_adjoin y 0), by simp⟩;
      · obtain ⟨u, hu, x, hx, hlen, heq⟩ := ih hw;
        exact ⟨y ∷ u, adjoin_le_adjoin (le_refl y) hu, x,
          le_trans hx (le_of_lt (lt_adjoin' y w)), by simp [hlen], by simp [← heq]⟩;
  obtain ⟨u, -, x, -, hlen, heq⟩ := H w (by rintro rfl; simp at h);
  exact ⟨u, x, add_right_cancel (hlen.trans h), heq⟩;

end vecAppend

/-! ## Satisfaction predicates -/

mutual

def SigmaSatisfaction : ℕ → V → V → Prop
  | 0 => BoundedSatisfaction
  | n + 1 => fun z e ↦
      ∃ k q, z = qqQuants 𝚺 q k ∧ IsStrictPi n q ∧
        ∃ w, len w = k ∧ PiSatisfaction n q (vecAppend w e)

def PiSatisfaction : ℕ → V → V → Prop
  | 0 => BoundedSatisfaction
  | n + 1 => fun z e ↦
      IsStrictPi (n + 1) z ∧ IsUFormula ℒₒᵣ z ∧ ¬SigmaSatisfaction (n + 1) (neg ℒₒᵣ z) e

end

noncomputable def piOfSigma (m : ℕ) (σ : 𝚺ᴬ-[m + 1].Semisentence 2) :
    𝚷ᴬ-[m + 1].Semisentence 2 := .mkPi
  “z e. !(isStrictHierarchy 𝚷 (m + 1)).pi z ∧ !(isUFormula ℒₒᵣ).pi z ∧
    ∀ nz, !(negGraph ℒₒᵣ).val nz z → ¬!σ.val nz e”
  (by
    have h1 : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (m + 1) (isStrictHierarchy 𝚷 (m + 1)).pi.val :=
      (isStrictHierarchy 𝚷 (m + 1)).pi.pi_prop.mono (Nat.le_add_left 1 m);
    have h2 : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (m + 1) (isUFormula ℒₒᵣ).pi.val :=
      (isUFormula ℒₒᵣ).pi.pi_prop.mono (Nat.le_add_left 1 m);
    have h3 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (m + 1) (negGraph ℒₒᵣ).val :=
      (negGraph ℒₒᵣ).sigma_prop.mono (Nat.le_add_left 1 m);
    have h4 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (m + 1) σ.val := σ.sigma_prop;
    simp [h1, h2, h3, h4])

noncomputable def sigmaOfPi (m : ℕ) (π : 𝚷ᴬ-[m + 1].Semisentence 2) :
    𝚺ᴬ-[m + 2].Semisentence 2 := .mkSigma
  “z e. ∃ k q w e', !(qqQuantsDef 𝚺) z q k ∧ !(isStrictHierarchy 𝚷 (m + 1)).val q ∧
    !lenDef k w ∧ !vecAppendDef e' w e ∧ !π.val q e'”
  (by
    have h1 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (m + 2) (qqQuantsDef 𝚺).val :=
      (qqQuantsDef 𝚺).sigma_prop.mono (show 1 ≤ m + 2 by omega);
    have h2 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (m + 2) (isStrictHierarchy 𝚷 (m + 1)).val :=
      (isStrictHierarchy 𝚷 (m + 1)).sigma.sigma_prop.mono (show 1 ≤ m + 2 by omega);
    have h3 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (m + 2) lenDef.val :=
      lenDef.sigma_prop.mono (show 1 ≤ m + 2 by omega);
    have h4 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (m + 2) vecAppendDef.val :=
      vecAppendDef.sigma_prop.mono (show 1 ≤ m + 2 by omega);
    have h5 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (m + 2) π.val := π.pi_prop.accum 𝚺;
    simp [h1, h2, h3, h4, h5])

noncomputable def sigmaZero : 𝚺ᴬ-[1].Semisentence 2 := .mkSigma
  “z e. ∃ k q w e', !(qqQuantsDef 𝚺) z q k ∧ !(isStrictHierarchy 𝚷 0).val q ∧ !lenDef k w ∧
    !vecAppendDef e' w e ∧ !boundedSatisfaction.val q e'”
  (by
    have h1 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 (qqQuantsDef 𝚺).val := (qqQuantsDef 𝚺).sigma_prop;
    have h2 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 (isStrictHierarchy 𝚷 0).val :=
      (isStrictHierarchy 𝚷 0).sigma.sigma_prop;
    have h3 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 lenDef.val := lenDef.sigma_prop;
    have h4 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 vecAppendDef.val := vecAppendDef.sigma_prop;
    have h5 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 boundedSatisfaction.val :=
      HierarchySymbol.Semiformula.val_sigma boundedSatisfaction ▸
        boundedSatisfaction.sigma.sigma_prop;
    simp [h1, h2, h3, h4, h5])

noncomputable def sigmaSatisfaction : (n : ℕ) → 𝚺ᴬ-[n + 1].Semisentence 2
  | 0 => sigmaZero
  | n + 1 => sigmaOfPi n (piOfSigma n (sigmaSatisfaction n))

noncomputable def piSatisfaction (n : ℕ) :
    𝚷ᴬ-[n + 1].Semisentence 2 := piOfSigma n (sigmaSatisfaction n)

private lemma piDefined_of_sigmaDefined {m : ℕ} {σ : 𝚺ᴬ-[m + 1].Semisentence 2}
    (hσ : 𝚺ᴬ-[m + 1]-Relation (SigmaSatisfaction (m + 1) : V → V → Prop) via σ) :
    𝚷ᴬ-[m + 1]-Relation (PiSatisfaction (m + 1) : V → V → Prop) via piOfSigma m σ := .mk fun v ↦ by
  have := hσ;
  simp [piOfSigma, PiSatisfaction];

instance SigmaSatisfaction.defined : (n : ℕ) →
    𝚺ᴬ-[n + 1]-Relation (SigmaSatisfaction (n + 1) : V → V → Prop) via sigmaSatisfaction n
  | 0 => .mk fun v ↦ by simp [sigmaSatisfaction, sigmaZero, SigmaSatisfaction, PiSatisfaction]
  | n + 1 =>
    have : 𝚷ᴬ-[n + 1]-Relation (PiSatisfaction (n + 1) : V → V → Prop)
        via piOfSigma n (sigmaSatisfaction n) :=
      piDefined_of_sigmaDefined (SigmaSatisfaction.defined n);
    .mk fun v ↦ by simp [sigmaSatisfaction, sigmaOfPi, SigmaSatisfaction]

instance PiSatisfaction.defined (n : ℕ) :
    𝚷ᴬ-[n + 1]-Relation (PiSatisfaction (n + 1) : V → V → Prop) via piSatisfaction n :=
  piDefined_of_sigmaDefined (SigmaSatisfaction.defined n)

instance SigmaSatisfaction.definable (n : ℕ) :
    𝚺ᴬ-[n + 1]-Relation (SigmaSatisfaction (n + 1) : V → V → Prop) :=
  (SigmaSatisfaction.defined n).to_definable

instance PiSatisfaction.definable (n : ℕ) :
    𝚷ᴬ-[n + 1]-Relation (PiSatisfaction (n + 1) : V → V → Prop) :=
  (PiSatisfaction.defined n).to_definable

@[simp] lemma SigmaSatisfaction.zero :
    SigmaSatisfaction 0 = (BoundedSatisfaction : V → V → Prop) := by
  simp [SigmaSatisfaction];

@[simp] lemma PiSatisfaction.zero : PiSatisfaction 0 = (BoundedSatisfaction : V → V → Prop) := by
  simp [PiSatisfaction];

/-! ## Tarski conditions -/

section
variable {n : ℕ} {z e : V}

private lemma sigmaSatisfaction_succ_iff :
    SigmaSatisfaction (n + 1) z e ↔ ∃ k q, z = qqQuants 𝚺 q k ∧ IsStrictPi n q ∧
      ∃ w, len w = k ∧ PiSatisfaction n q (vecAppend w e) := by rw [SigmaSatisfaction]

private lemma piSatisfaction_succ_iff :
    PiSatisfaction (n + 1) z e ↔ IsStrictPi (n + 1) z ∧ IsUFormula ℒₒᵣ z ∧
      ¬SigmaSatisfaction (n + 1) (neg ℒₒᵣ z) e := by rw [PiSatisfaction]

theorem PiSatisfaction.dom (h : PiSatisfaction n z e) :
    IsStrictPi n z ∧ IsUFormula ℒₒᵣ z := by
  match n with
  | 0 => exact BoundedSatisfaction.dom (by simpa using h);
  | _ + 1 => exact ⟨(piSatisfaction_succ_iff.mp h).1, (piSatisfaction_succ_iff.mp h).2.1⟩;

theorem SigmaSatisfaction.dom (h : SigmaSatisfaction n z e) :
    IsStrictSigma n z ∧ IsUFormula ℒₒᵣ z := by
  match n with
  | 0 => exact BoundedSatisfaction.dom (by simpa using h);
  | _ + 1 =>
    obtain ⟨k, q, rfl, hq, w, -, hsat⟩ := sigmaSatisfaction_succ_iff.mp h;
    exact ⟨⟨k, q, rfl, hq⟩, isUFormula_qqQuants.mpr (PiSatisfaction.dom hsat).2⟩;

theorem PiSatisfaction.neg_iff (hz : IsStrictSigma n z)
    (hz' : IsUFormula ℒₒᵣ z) : PiSatisfaction n (neg ℒₒᵣ z) e ↔ ¬SigmaSatisfaction n z e := by
  match n with
  | 0 => simpa using BoundedSatisfaction.neg_iff hz hz';
  | _ + 1 =>
    rw [piSatisfaction_succ_iff, IsUFormula.neg_neg hz'];
    simp [show IsStrictPi _ (neg ℒₒᵣ z) from IsStrictHierarchy.neg hz' hz, hz'];

theorem SigmaSatisfaction.neg_iff (hz : IsStrictPi n z)
    (hz' : IsUFormula ℒₒᵣ z) : SigmaSatisfaction n (neg ℒₒᵣ z) e ↔ ¬PiSatisfaction n z e := by
  match n with
  | 0 => simpa using BoundedSatisfaction.neg_iff hz hz';
  | _ + 1 =>
    rw [piSatisfaction_succ_iff (z := z)];
    simp [hz, hz'];

end

/-! ### Maximal existential blocks -/

lemma qqQuants_cancel {Γ : Polarity} (k : V) :
    ∀ p p' j : V, qqQuants Γ p k = qqQuants Γ p' (k + j) → p = qqQuants Γ p' j := by
  induction k using ISigma1.pi1_succ_induction
  · definability;
  case zero => intro p p' j h; simpa using h;
  case succ k ih =>
    intro p p' j h;
    rw [qqQuants_succ, add_right_comm k 1 j, qqQuants_succ, qqQuant_inj] at h;
    exact ih p p' j h.2;

private lemma exists_ex_block (z : V) : ∃ K M, z = qqQuants 𝚺 M K ∧ ∀ p : V, M ≠ ^∃ p := by
  have H : ∀ z : V, ∃ K ≤ z, ∃ M ≤ z, z = qqQuants 𝚺 M K ∧ ∀ p < M, M ≠ ^∃ p := by
    intro z;
    induction z using ISigma1.sigma1_order_induction
    · definability;
    case ind z ih =>
      by_cases hz : ∃ p < z, z = ^∃ p;
      · obtain ⟨p, hp, rfl⟩ := hz;
        obtain ⟨K, hK, M, hM, rfl, hM'⟩ := ih p hp;
        exact ⟨K + 1, lt_iff_succ_le.mp (lt_of_le_of_lt hK (lt_exists _)),
          M, le_trans hM (le_of_lt hp), by rw [qqQuants_succ, qqQuant_sigma], hM'⟩;
      · exact ⟨0, by simp, z, by simp, by simp, fun p hp h ↦ hz ⟨p, hp, h⟩⟩;
  obtain ⟨K, -, M, -, h, hM⟩ := H z;
  exact ⟨K, M, h, fun p hp ↦ hM p (hp ▸ lt_exists p) hp⟩;

private lemma ex_block_dominates {z M K q k : V} (hMK : z = qqQuants 𝚺 M K)
    (hM : ∀ p : V, M ≠ ^∃ p) (hqk : z = qqQuants 𝚺 q k) :
    ∃ j, K = k + j ∧ q = qqQuants 𝚺 M j := by
  rcases le_total k K with h | h;
  · obtain ⟨j, rfl⟩ := exists_add_of_le h;
    exact ⟨j, rfl, qqQuants_cancel k q M j (by rw [← hqk, hMK])⟩;
  · obtain ⟨j, rfl⟩ := exists_add_of_le h;
    have hMq : M = qqQuants 𝚺 q j := qqQuants_cancel K M q j (by rw [← hMK, hqk]);
    rcases zero_or_succ j with rfl | ⟨j, rfl⟩;
    · exact ⟨0, by simp, by simpa using hMq.symm⟩;
    · exact absurd hMq (by rw [qqQuants_succ]; exact hM _);

private lemma isStrictSigma_of_isStrictPi_ex {n : ℕ} {p : V} (h : IsStrictPi (n + 1) (^∃ p)) :
    IsStrictSigma n (^∃ p) := by
  obtain ⟨k, q, heq, hq⟩ := h;
  rcases zero_or_succ k with rfl | ⟨k, rfl⟩;
  · rw [qqQuants_zero] at heq; exact heq ▸ hq;
  · rw [qqQuants_succ] at heq; simp [qqExs, qqAll, pair_ext_iff] at heq;

private lemma isBounded_ex_block {z M K : V} (hz : IsBounded z) (hMK : z = qqQuants 𝚺 M K)
    (hM : ∀ p : V, M ≠ ^∃ p) : IsBounded M ∧ K ≤ 1 := by
  rcases zero_or_succ K with rfl | ⟨K, rfl⟩;
  · rw [qqQuants_zero] at hMK; exact ⟨hMK ▸ hz, by simp⟩;
  · rw [qqQuants_succ] at hMK;
    subst hMK;
    obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, heq⟩ := IsBounded.of_ex hz;
    rcases zero_or_succ K with rfl | ⟨K, rfl⟩;
    · rw [qqQuants_zero] at heq;
      subst heq;
      exact ⟨IsBounded.and_iff.mpr ⟨by rw [Arithmetic.qqLT]; exact IsBounded.rel, hq⟩, by simp⟩;
    · rw [qqQuants_succ] at heq;
      simp [qqExs, qqAnd, pair_ext_iff] at heq;

private lemma isStrictPi_ex_block : ∀ (n : ℕ) (z M K : V), IsStrictSigma (n + 1) z →
    z = qqQuants 𝚺 M K → (∀ p : V, M ≠ ^∃ p) → IsStrictPi n M
  | 0, _, M, _, hz, hMK, hM => by
    obtain ⟨k, q, hqk, hq⟩ := hz;
    obtain ⟨j, -, rfl⟩ := ex_block_dominates hMK hM hqk;
    exact (isBounded_ex_block hq rfl hM).1;
  | n + 1, _, M, _, hz, hMK, hM => by
    obtain ⟨k, q, hqk, hq⟩ := hz;
    obtain ⟨j, -, rfl⟩ := ex_block_dominates hMK hM hqk;
    rcases zero_or_succ j with rfl | ⟨j, rfl⟩;
    · simpa using hq;
    · have hs : IsStrictSigma n (qqQuants 𝚺 M (j + 1)) := by
        rw [qqQuants_succ] at hq ⊢;
        exact isStrictSigma_of_isStrictPi_ex hq;
      match n with
      | 0 => exact IsStrictHierarchy.of_bounded (isBounded_ex_block hs rfl hM).1;
      | n + 1 =>
        exact IsStrictHierarchy.mono (by omega)
          (isStrictPi_ex_block n (qqQuants 𝚺 M (j + 1)) M (j + 1) hs rfl hM);

/-! ### The $\Delta_0$ existential condition -/

private lemma boundedSatisfaction_ex_iff {p e : V} (h : IsBounded (^∃ p)) :
    BoundedSatisfaction (^∃ p) e ↔ ∃ x, BoundedSatisfaction p (x ∷ e) := by
  obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ := IsBounded.of_ex h;
  have hlt : ∀ x : V,
      BoundedSatisfaction (Arithmetic.qqLT (qqBvar 0) (termBShift ℒₒᵣ t)) (x ∷ e) ↔
        x < termVal e t := fun x ↦ by
    rw [BoundedSatisfaction.lt_iff (by simp) ht.termBShift];
    simp [termVal_termBShift ht x e];
  rw [show (^∃ ((Arithmetic.qqLT (qqBvar 0) (termBShift ℒₒᵣ t)) ^⋏ q) : V)
      = qqBex (termBShift ℒₒᵣ t) q from rfl, BoundedSatisfaction.bex_iff ht];
  constructor;
  · rintro ⟨x, hx, hsat⟩;
    exact ⟨x, BoundedSatisfaction.and_iff.mpr ⟨(hlt x).mpr hx, hsat⟩⟩;
  · rintro ⟨x, hsat⟩;
    obtain ⟨h₁, h₂⟩ := BoundedSatisfaction.and_iff.mp hsat;
    exact ⟨x, (hlt x).mp h₁, h₂⟩;

/-! ### The block characterization -/

private def BlockSatisfaction (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (n : ℕ) : Prop :=
  ∀ z M K e : V, IsStrictSigma (n + 1) z → IsUFormula ℒₒᵣ z → z = qqQuants 𝚺 M K →
    (∀ p : V, M ≠ ^∃ p) →
      (SigmaSatisfaction (n + 1) z e ↔ ∃ w, len w = K ∧ PiSatisfaction n M (vecAppend w e))

private lemma of_Pi0 (hB : BlockSatisfaction V 0) {z e : V} (hz : IsBounded z)
    (hz' : IsUFormula ℒₒᵣ z) : SigmaSatisfaction 1 z e ↔ PiSatisfaction 0 z e := by
  constructor;
  · intro h;
    obtain ⟨K, M, hMK, hM⟩ := exists_ex_block z;
    obtain ⟨w, hw, hsat⟩ := (hB z M K e (IsStrictHierarchy.of_alt hz) hz' hMK hM).mp h;
    obtain ⟨hMd, hK1⟩ := isBounded_ex_block hz hMK hM;
    rcases zero_or_succ K with rfl | ⟨K, rfl⟩;
    · rw [qqQuants_zero] at hMK;
      rw [len_zero_iff_eq_nil.mp hw] at hsat;
      simpa [hMK] using hsat;
    · have hK : K = 0 := by simpa using hK1;
      subst hK;
      rw [qqQuants_succ, qqQuants_zero, qqQuant_sigma] at hMK;
      obtain ⟨x, rfl⟩ := eq_singleton_iff_len_eq_one.mp (by simpa using hw);
      have h0 : BoundedSatisfaction M (x ∷ e) := by simpa using hsat;
      simpa [hMK] using (boundedSatisfaction_ex_iff (hMK ▸ hz)).mpr ⟨x, h0⟩;
  · intro h;
    exact sigmaSatisfaction_succ_iff.mpr ⟨0, z, by simp, hz, 0, by simp, by simpa using h⟩;

private lemma mono_step : ∀ (n : ℕ), (∀ m ≤ n, BlockSatisfaction V m) →
    (∀ z e : V, IsStrictSigma n z → IsUFormula ℒₒᵣ z →
      (SigmaSatisfaction n z e ↔ SigmaSatisfaction (n + 1) z e)) ∧
    (∀ z e : V, IsStrictPi n z → IsUFormula ℒₒᵣ z →
      (PiSatisfaction n z e ↔ PiSatisfaction (n + 1) z e)) := by
  intro n;
  induction n with
  | zero =>
    intro hB;
    have hsig : ∀ z e : V, IsStrictSigma 0 z → IsUFormula ℒₒᵣ z →
        (SigmaSatisfaction 0 z e ↔ SigmaSatisfaction 1 z e) := fun z e hz hz' ↦ by
      simpa using (of_Pi0 (hB 0 le_rfl) hz hz').symm;
    exact ⟨hsig, fun z e hz hz' ↦ by
      rw [show (PiSatisfaction 0 z e ↔ ¬SigmaSatisfaction 0 (neg ℒₒᵣ z) e) by
          rw [SigmaSatisfaction.neg_iff hz hz']; simp,
        show (PiSatisfaction 1 z e ↔ ¬SigmaSatisfaction 1 (neg ℒₒᵣ z) e) by
          rw [SigmaSatisfaction.neg_iff (IsStrictHierarchy.mono (Nat.le_succ 0) hz) hz']; simp,
        hsig (neg ℒₒᵣ z) e (IsStrictHierarchy.neg hz' hz) hz'.neg]⟩;
  | succ n ih =>
    intro hB;
    have hpin := (ih fun i hi ↦ hB i (by omega)).2;
    have hsig : ∀ z e : V, IsStrictSigma (n + 1) z → IsUFormula ℒₒᵣ z →
        (SigmaSatisfaction (n + 1) z e ↔ SigmaSatisfaction (n + 2) z e) := fun z e hz hz' ↦ by
      obtain ⟨K, M, hMK, hM⟩ := exists_ex_block z;
      have hMu : IsUFormula ℒₒᵣ M := isUFormula_qqQuants.mp (hMK ▸ hz');
      have hMpi : IsStrictPi n M := isStrictPi_ex_block n z M K hz hMK hM;
      rw [hB n (by omega) z M K e hz hz' hMK hM,
        hB (n + 1) le_rfl z M K e (IsStrictHierarchy.mono (by omega) hz) hz' hMK hM];
      exact exists_congr fun w ↦ and_congr_right fun _ ↦ hpin M _ hMpi hMu;
    exact ⟨hsig, fun z e hz hz' ↦ by
      rw [show (PiSatisfaction (n + 1) z e ↔ ¬SigmaSatisfaction (n + 1) (neg ℒₒᵣ z) e) by
          rw [SigmaSatisfaction.neg_iff hz hz']; simp,
        show (PiSatisfaction (n + 2) z e ↔ ¬SigmaSatisfaction (n + 2) (neg ℒₒᵣ z) e) by
          rw [SigmaSatisfaction.neg_iff (IsStrictHierarchy.mono (Nat.le_succ _) hz) hz']; simp,
        hsig (neg ℒₒᵣ z) e (IsStrictHierarchy.neg hz' hz) hz'.neg]⟩;

private lemma of_pi_step : ∀ (n : ℕ), (∀ m ≤ n, BlockSatisfaction V m) →
    (∀ z e : V, IsStrictPi n z → IsUFormula ℒₒᵣ z →
      (SigmaSatisfaction (n + 1) z e ↔ PiSatisfaction n z e)) ∧
    (∀ z e : V, IsStrictSigma n z → IsUFormula ℒₒᵣ z →
      (PiSatisfaction (n + 1) z e ↔ SigmaSatisfaction n z e)) := by
  intro n;
  induction n with
  | zero =>
    intro hB;
    exact ⟨fun z e hz hz' ↦ of_Pi0 (hB 0 le_rfl) hz hz', fun z e hz hz' ↦ by
        rw [show (PiSatisfaction 1 z e ↔ ¬SigmaSatisfaction 1 (neg ℒₒᵣ z) e) by
            rw [SigmaSatisfaction.neg_iff (IsStrictHierarchy.of_alt hz) hz']; simp,
          of_Pi0 (hB 0 le_rfl) (IsStrictHierarchy.neg hz' hz) hz'.neg,
          PiSatisfaction.neg_iff hz hz'];
        simp⟩;
  | succ n ih =>
    intro hB;
    have hsig : ∀ z e : V, IsStrictPi (n + 1) z → IsUFormula ℒₒᵣ z →
        (SigmaSatisfaction (n + 2) z e ↔ PiSatisfaction (n + 1) z e) := by
      intro z e hz hz';
      constructor;
      · intro h;
        obtain ⟨K, M, hMK, hM⟩ := exists_ex_block z;
        have hMu : IsUFormula ℒₒᵣ M := isUFormula_qqQuants.mp (hMK ▸ hz');
        obtain ⟨w, hw, hsat⟩ :=
          (hB (n + 1) le_rfl z M K e (IsStrictHierarchy.of_alt hz) hz' hMK hM).mp h;
        rcases zero_or_succ K with rfl | ⟨K, rfl⟩;
        · rw [qqQuants_zero] at hMK;
          rw [len_zero_iff_eq_nil.mp hw] at hsat;
          simpa [hMK] using hsat;
        · have hzex : z = ^∃ (qqQuants 𝚺 M K) := by rw [hMK, qqQuants_succ, qqQuant_sigma];
          have hzs : IsStrictSigma n z := by
            rw [hzex] at hz ⊢;
            exact isStrictSigma_of_isStrictPi_ex hz;
          apply ((ih fun i hi ↦ hB i (by omega)).2 z e hzs hz').mpr;
          match n with
          | 0 =>
            obtain ⟨hMd, hK1⟩ := isBounded_ex_block hzs hMK hM;
            have hK : K = 0 := by simpa using hK1;
            subst hK;
            rw [qqQuants_zero] at hzex;
            obtain ⟨x, rfl⟩ := eq_singleton_iff_len_eq_one.mp (by simpa using hw);
            have h0 : BoundedSatisfaction M (x ∷ e) := by
              simpa using ((ih fun i hi ↦ hB i (by omega)).2 M (x ∷ e) hMd hMu).mp
                (by simpa using hsat);
            simpa [hzex] using (boundedSatisfaction_ex_iff (hzex ▸ hzs)).mpr ⟨x, h0⟩;
          | n + 1 =>
            have hMpi : IsStrictPi n M := isStrictPi_ex_block n z M (K + 1) hzs hMK hM;
            have h1 := (mono_step n fun i hi ↦ hB i (by omega)).2;
            have h2 := (mono_step (n + 1) fun i hi ↦ hB i (by omega)).2;
            exact (hB n (by omega) z M (K + 1) e hzs hz' hMK hM).mpr
              ⟨w, hw, by
                rw [h1 M _ hMpi hMu, h2 M _ (IsStrictHierarchy.mono (by omega) hMpi) hMu];
                exact hsat⟩;
      · intro h;
        exact sigmaSatisfaction_succ_iff.mpr ⟨0, z, by simp, hz, 0, by simp, by simpa using h⟩;
    exact ⟨hsig, fun z e hz hz' ↦ by
      rw [show (PiSatisfaction (n + 2) z e ↔ ¬SigmaSatisfaction (n + 2) (neg ℒₒᵣ z) e) by
          rw [SigmaSatisfaction.neg_iff (IsStrictHierarchy.of_alt hz) hz']; simp,
        hsig (neg ℒₒᵣ z) e (IsStrictHierarchy.neg hz' hz) hz'.neg, PiSatisfaction.neg_iff hz hz'];
      simp⟩;

private lemma blockSatisfaction : ∀ n : ℕ, BlockSatisfaction V n := fun n ↦ by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z M K e hz hz' hMK hM;
    have hMu : IsUFormula ℒₒᵣ M := isUFormula_qqQuants.mp (hMK ▸ hz');
    have hMpi : IsStrictPi n M := isStrictPi_ex_block n z M K hz hMK hM;
    constructor;
    · intro h;
      obtain ⟨k, q, hqk, hq, w, hw, hsat⟩ := sigmaSatisfaction_succ_iff.mp h;
      obtain ⟨j, rfl, rfl⟩ := ex_block_dominates hMK hM hqk;
      rcases zero_or_succ j with rfl | ⟨j, rfl⟩;
      · exact ⟨w, by simpa using hw, by simpa using hsat⟩;
      · have hqex : (^∃ (qqQuants 𝚺 M j) : V) = qqQuants 𝚺 M (j + 1) :=
          (qqQuants_succ (Γ := 𝚺) (p := M) (k := j)).symm;
        rw [qqQuants_succ] at hq hsat;
        match n with
        | 0 =>
          obtain ⟨-, hj⟩ := isBounded_ex_block hq hqex hM;
          have hj0 : j = 0 := by simpa using hj;
          subst hj0;
          rw [qqQuants_zero] at hq hsat;
          obtain ⟨x, hx⟩ := (boundedSatisfaction_ex_iff hq).mp (by simpa using hsat);
          exact ⟨x ∷ w, by simp [hw], by simpa using hx⟩;
        | m + 1 =>
          have hqU : IsUFormula ℒₒᵣ (^∃ (qqQuants 𝚺 M j) : V) := by
            rw [hqex]; exact isUFormula_qqQuants.mpr hMu;
          have hqs : IsStrictSigma m (^∃ (qqQuants 𝚺 M j) : V) :=
            isStrictSigma_of_isStrictPi_ex hq;
          have hsat' : SigmaSatisfaction m (^∃ (qqQuants 𝚺 M j) : V) (vecAppend w e) :=
            ((of_pi_step m fun i hi ↦ ih i (by omega)).2 _ _ hqs hqU).mp hsat;
          match m with
          | 0 =>
            obtain ⟨hMd, hj'⟩ := isBounded_ex_block hqs hqex hM;
            have hj0 : j = 0 := by simpa using hj';
            subst hj0;
            rw [qqQuants_zero] at hqs hsat';
            obtain ⟨x, hx⟩ := (boundedSatisfaction_ex_iff hqs).mp (by simpa using hsat');
            exact ⟨x ∷ w, by simp [hw],
              ((of_pi_step 0 fun i hi ↦ ih i (by omega)).2 M _ hMd hMu).mpr (by simpa using hx)⟩;
          | m + 1 =>
            have hMpi' : IsStrictPi m M := isStrictPi_ex_block m _ M (j + 1) hqs hqex hM;
            obtain ⟨u, hu, husat⟩ :=
              (ih m (by omega) _ M (j + 1) (vecAppend w e) hqs hqU hqex hM).mp hsat';
            use vecAppend u w;
            constructor;
            · rw [len_vecAppend, hu, hw, add_comm];
            · rw [vecAppend_assoc];
              have h1 := (mono_step m fun i hi ↦ ih i (by omega)).2 M
                (vecAppend u (vecAppend w e)) hMpi' hMu;
              have h2 := (mono_step (m + 1) fun i hi ↦ ih i (by omega)).2 M
                (vecAppend u (vecAppend w e)) (IsStrictHierarchy.mono (by omega) hMpi') hMu;
              exact h2.mp (h1.mp husat);
    · rintro ⟨w, hw, hsat⟩;
      exact sigmaSatisfaction_succ_iff.mpr ⟨K, M, hMK, hMpi, w, hw, hsat⟩;

section
variable {n : ℕ} {z e : V}

theorem SigmaSatisfaction.of_pi (hz : IsStrictPi n z) (hz' : IsUFormula ℒₒᵣ z) :
    SigmaSatisfaction (n + 1) z e ↔ PiSatisfaction n z e :=
  (of_pi_step n fun m _ ↦ blockSatisfaction m).1 z e hz hz'

theorem PiSatisfaction.of_sigma (hz : IsStrictSigma n z) (hz' : IsUFormula ℒₒᵣ z) :
    PiSatisfaction (n + 1) z e ↔ SigmaSatisfaction n z e :=
  (of_pi_step n fun m _ ↦ blockSatisfaction m).2 z e hz hz'

end

section
variable {n : ℕ} {p e : V}

theorem SigmaSatisfaction.exs_iff : SigmaSatisfaction (n + 1) (^∃ p) e ↔
    ∃ x, SigmaSatisfaction (n + 1) p (x ∷ e) := by
  by_cases hp : IsStrictSigma (n + 1) p ∧ IsUFormula ℒₒᵣ p;
  · obtain ⟨K, M, hMK, hM⟩ := exists_ex_block p;
    have h1 : SigmaSatisfaction (n + 1) (^∃ p) e ↔
      ∃ w, len w = K + 1 ∧ PiSatisfaction n M (vecAppend w e) :=
      blockSatisfaction n (^∃ p) M (K + 1) e (IsStrictHierarchy.quant hp.1) (by simp [hp.2])
        (by rw [qqQuants_succ, qqQuant_sigma, ← hMK]) hM;
    have h2 : ∀ x : V, SigmaSatisfaction (n + 1) p (x ∷ e) ↔
      ∃ u, len u = K ∧ PiSatisfaction n M (vecAppend u (x ∷ e)) :=
      fun x ↦ blockSatisfaction n p M K (x ∷ e) hp.1 hp.2 hMK hM;
    rw [h1];
    constructor;
    · rintro ⟨w, hw, hsat⟩;
      obtain ⟨u, x, hu, rfl⟩ := exists_vecAppend_singleton hw;
      exact ⟨x, (h2 x).mpr ⟨u, hu, by rw [vecAppend_assoc] at hsat; simpa using hsat⟩⟩;
    · rintro ⟨x, hx⟩;
      obtain ⟨u, hu, hsat⟩ := (h2 x).mp hx;
      exact ⟨vecAppend u ?[x], by simp [hu], by rw [vecAppend_assoc]; simpa using hsat⟩;
  · constructor;
    · intro h;
      obtain ⟨hs, hu⟩ := h.dom;
      exact absurd ⟨IsStrictHierarchy.of_quant (Γ := 𝚺) hs, by simpa using hu⟩ hp;
    · rintro ⟨_, hx⟩;
      exact absurd hx.dom hp;

theorem PiSatisfaction.all_iff : PiSatisfaction (n + 1) (^∀ p) e ↔
    ∀ x, PiSatisfaction (n + 1) p (x ∷ e) := by
  constructor;
  · intro h;
    obtain ⟨hs, hu, hns⟩ := piSatisfaction_succ_iff.mp h;
    have hup : IsUFormula ℒₒᵣ p := by simpa using hu;
    rw [neg_all hup, SigmaSatisfaction.exs_iff] at hns;
    exact fun x ↦ piSatisfaction_succ_iff.mpr
      ⟨IsStrictHierarchy.of_quant (Γ := 𝚷) hs, hup, fun hc ↦ hns ⟨x, hc⟩⟩;
  · intro h;
    obtain ⟨hsp, hup, -⟩ := piSatisfaction_succ_iff.mp (h 0);
    apply piSatisfaction_succ_iff.mpr;
    and_intros;
    · exact IsStrictHierarchy.quant hsp;
    · simp [hup];
    · rw [neg_all hup, SigmaSatisfaction.exs_iff];
      rintro ⟨x, hx⟩;
      exact (piSatisfaction_succ_iff.mp (h x)).2.2 hx;

end

section
variable {m n : ℕ} (h : m ≤ n) {z e : V}
include h

theorem SigmaSatisfaction.mono (hz : IsStrictSigma m z) (hz' : IsUFormula ℒₒᵣ z) :
    SigmaSatisfaction m z e ↔ SigmaSatisfaction n z e := by
  induction n, h using Nat.le_induction with
  | base => rfl;
  | succ n hn ih =>
    exact ih.trans
      ((mono_step n fun i _ ↦ blockSatisfaction i).1 z e (IsStrictHierarchy.mono hn hz) hz');

theorem PiSatisfaction.mono (hz : IsStrictPi m z) (hz' : IsUFormula ℒₒᵣ z) :
    PiSatisfaction m z e ↔ PiSatisfaction n z e := by
  induction n, h using Nat.le_induction with
  | base => rfl;
  | succ n hn ih =>
    exact ih.trans
      ((mono_step n fun i _ ↦ blockSatisfaction i).2 z e (IsStrictHierarchy.mono hn hz) hz');

end

/-! ### Substitution under a quantifier block -/

namespace QVecIter

noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. !(qVecGraph ℒₒᵣ) y ih”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun x ↦ x 0
  succ := fun _ _ ih ↦ qVec ℒₒᵣ ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  -- Letting `simp` apply `Semiformula.eval_substs` here overflows memory on Lean v4.33.1.
  succ_defined := .mk fun v ↦ by
    simp only [blueprint, HierarchySymbol.Semiformula.val_mkSigma];
    rw [Semiformula.eval_substs];
    simp [(qVec.defined (L := ℒₒᵣ) (V := V)).df];

end QVecIter

noncomputable def qVecIter (w k : V) : V := QVecIter.construction.result ![w] k

@[simp] lemma qVecIter_zero (w : V) : qVecIter w 0 = w := by
  simp [qVecIter, QVecIter.construction];

@[simp] lemma qVecIter_succ (w k : V) : qVecIter w (k + 1) = qVec ℒₒᵣ (qVecIter w k) := by
  simp [qVecIter, QVecIter.construction];

noncomputable def _root_.FFL.FirstOrder.Arithmetic.qVecIterDef : 𝚺ᴬ₁.Semisentence 3 :=
  QVecIter.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance qVecIter_defined : 𝚺ᴬ₁-Function₂ (qVecIter : V → V → V) via qVecIterDef := .mk
  fun v ↦ by simp [QVecIter.construction.result_defined_iff, qVecIterDef]; rfl

instance qVecIter_definable : 𝚺ᴬ₁-Function₂ (qVecIter : V → V → V) :=
  qVecIter_defined.to_definable

instance qVecIter_definable' (Γ m) : Γᴬ-[m + 1]-Function₂ (qVecIter : V → V → V) :=
  qVecIter_definable.of_sigmaOne

lemma isSemitermVec_qVecIter {m l w : V} (hw : IsSemitermVec ℒₒᵣ m l w) (k : V) :
    IsSemitermVec ℒₒᵣ (m + k) (l + k) (qVecIter w k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability;
  case zero => simpa using hw;
  case succ k ih =>
    rw [qVecIter_succ, ← add_assoc, ← add_assoc];
    exact ih.qVec;

lemma qVecIter_qVec (w k : V) :
    qVecIter (qVec ℒₒᵣ w) k = qVec ℒₒᵣ (qVecIter w k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability;
  case zero => simp;
  case succ k ih => rw [qVecIter_succ, ih, qVecIter_succ];

section
variable {Γ : Polarity}

@[simp] lemma substs_qqQuant {p : V} (hp : IsUFormula ℒₒᵣ p) (w : V) :
    Bootstrapping.subst ℒₒᵣ w (qqQuant Γ p)
      = qqQuant Γ (Bootstrapping.subst ℒₒᵣ (qVec ℒₒᵣ w) p) := by
  cases Γ <;> simp [hp];

@[simp] lemma isSemiformula_qqQuant {n p : V} :
    IsSemiformula ℒₒᵣ n (qqQuant Γ p) ↔ IsSemiformula ℒₒᵣ (n + 1) p := by
  cases Γ <;> simp;

lemma substs_qqQuants {p : V} (hp : IsUFormula ℒₒᵣ p) (k : V) :
    ∀ w : V, Bootstrapping.subst ℒₒᵣ w (qqQuants Γ p k)
      = qqQuants Γ (Bootstrapping.subst ℒₒᵣ (qVecIter w k) p) k := by
  induction k using ISigma1.pi1_succ_induction
  · definability;
  case zero => intro w; simp;
  case succ k ih =>
    intro w;
    rw [qqQuants_succ, substs_qqQuant (isUFormula_qqQuants.mpr hp), ih (qVec ℒₒᵣ w),
      qVecIter_qVec, qVecIter_succ, qqQuants_succ];

lemma isSemiformula_qqQuants {p : V} (k : V) :
    ∀ n : V, (IsSemiformula ℒₒᵣ n (qqQuants Γ p k) ↔ IsSemiformula ℒₒᵣ (n + k) p) := by
  induction k using ISigma1.pi1_succ_induction
  · definability;
  case zero => intro n; simp;
  case succ k ih =>
    intro n;
    rw [qqQuants_succ, isSemiformula_qqQuant, ih, add_assoc, add_comm 1 k];

end

lemma termValVec_qVecIter {m l w e : V} (hw : IsSemitermVec ℒₒᵣ m l w) (k : V) :
    ∀ v : V, len v = k → termValVec (vecAppend v e) (m + k) (qVecIter w k) =
      vecAppend v (termValVec e m w) := by
  induction k using ISigma1.pi1_succ_induction
  · definability;
  case zero => intro v hv; rw [len_zero_iff_eq_nil.mp hv]; simp;
  case succ k ih =>
    intro v hv;
    rcases nil_or_adjoin v with rfl | ⟨x, v, rfl⟩;
    · simp at hv;
    · rw [vecAppend_adjoin, qVecIter_succ, ← add_assoc,
        termValVec_qVec (isSemitermVec_qVecIter hw k), ih v (by simpa using hv),
        vecAppend_adjoin];

lemma IsStrictHierarchy.subst {Γ : Polarity} {n : ℕ} {m l w p : V}
    (hw : IsSemitermVec ℒₒᵣ m l w) (hp : IsSemiformula ℒₒᵣ m p) (h : IsStrictHierarchy Γ n p) :
    IsStrictHierarchy Γ n (Bootstrapping.subst ℒₒᵣ w p) := by
  induction n generalizing Γ m l w p with
  | zero => exact IsBounded.subst hw hp h;
  | succ n ih =>
    obtain ⟨k, q, rfl, hq⟩ := h;
    have hqp : IsSemiformula ℒₒᵣ (m + k) q := (isSemiformula_qqQuants k m).mp hp;
    exact ⟨k, Bootstrapping.subst ℒₒᵣ (qVecIter w k) q, substs_qqQuants hqp.isUFormula k w,
      ih (isSemitermVec_qVecIter hw k) hqp hq⟩;

private lemma not_ex_subst {M : V} (hM : IsUFormula ℒₒᵣ M) (h : ∀ p : V, M ≠ ^∃ p) (w r : V) :
    Bootstrapping.subst ℒₒᵣ w M ≠ ^∃ r := by
  rcases hM.case with ⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl |
    ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, -, rfl⟩;
  · rw [substs_rel hR hv]; simp [qqRel, qqExs, pair_ext_iff];
  · rw [substs_nrel hR hv]; simp [qqNRel, qqExs, pair_ext_iff];
  · rw [substs_verum]; simp [qqVerum, qqExs, pair_ext_iff];
  · rw [substs_falsum]; simp [qqFalsum, qqExs, pair_ext_iff];
  · rw [substs_and hp hq]; simp [qqAnd, qqExs, pair_ext_iff];
  · rw [substs_or hp hq]; simp [qqOr, qqExs, pair_ext_iff];
  · rw [substs_all hp]; simp [qqAll, qqExs, pair_ext_iff];
  · exact absurd rfl (h p);

theorem SigmaSatisfaction.subst {n : ℕ} {m l w p e : V} (hw : IsSemitermVec ℒₒᵣ m l w)
    (hp : IsSemiformula ℒₒᵣ m p) (hp' : IsStrictSigma n p) :
    SigmaSatisfaction n (Bootstrapping.subst ℒₒᵣ w p) e ↔
      SigmaSatisfaction n p (termValVec e m w) := by
  induction n generalizing m l w p e with
  | zero => simpa using BoundedSatisfaction.subst hw hp hp';
  | succ n ih =>
    have hpi : ∀ {m l w q e' : V}, IsSemitermVec ℒₒᵣ m l w → IsSemiformula ℒₒᵣ m q →
      IsStrictPi n q →
        (PiSatisfaction n (Bootstrapping.subst ℒₒᵣ w q) e' ↔
          PiSatisfaction n q (termValVec e' m w)) := by
      intro m l w q e' hw hq hq';
      have hsq : IsStrictPi n (Bootstrapping.subst ℒₒᵣ w q) := hq'.subst hw hq;
      rw [show (PiSatisfaction n (Bootstrapping.subst ℒₒᵣ w q) e' ↔
            ¬SigmaSatisfaction n (neg ℒₒᵣ (Bootstrapping.subst ℒₒᵣ w q)) e') by
          rw [SigmaSatisfaction.neg_iff hsq (hq.subst hw).isUFormula]; simp,
        ← substs_neg hq hw,
        ih hw (by simp [hq]) (IsStrictHierarchy.neg hq.isUFormula hq'),
        SigmaSatisfaction.neg_iff hq' hq.isUFormula];
      simp;
    obtain ⟨K, M, hMK, hM⟩ := exists_ex_block p;
    have hMs : IsSemiformula ℒₒᵣ (m + K) M := (isSemiformula_qqQuants K m).mp (hMK ▸ hp);
    have hMpi : IsStrictPi n M := isStrictPi_ex_block n p M K hp' hMK hM;
    have hsubst : Bootstrapping.subst ℒₒᵣ w p
        = qqQuants 𝚺 (Bootstrapping.subst ℒₒᵣ (qVecIter w K) M) K := by
      rw [hMK, substs_qqQuants hMs.isUFormula K w];
    rw [blockSatisfaction n (Bootstrapping.subst ℒₒᵣ w p) _ K e
        (hp'.subst hw hp) (hp.subst hw).isUFormula hsubst
        (not_ex_subst hMs.isUFormula hM _),
      blockSatisfaction n p M K (termValVec e m w) hp' hp.isUFormula hMK hM];
    apply exists_congr;
    intro v;
    apply and_congr_right;
    intro hv;
    rw [hpi (isSemitermVec_qVecIter hw K) hMs hMpi, termValVec_qVecIter hw K v hv];

/-! ## Satisfaction under an externally supplied vector -/

noncomputable def sigmaSatisfactionVec (n k : ℕ) : 𝚺ᴬ-[n + 1].Semisentence (k + 1) := .mkSigma
  “p. ∃ e, !lenDef ↑k e ∧ (⋀ i, ∃ z, !nthDef z e ↑(i : Fin k).val ∧ z = #i.succ.succ.succ) ∧
    !(sigmaSatisfaction n).val p e”
  (by simp [lenDef.sigma_prop.mono (Nat.le_add_left 1 n),
        nthDef.sigma_prop.mono (Nat.le_add_left 1 n)])

theorem sigmaSatisfactionVec.defined (n k : ℕ) :
    𝚺ᴬ-[n + 1].Defined
      (fun v : Fin (k + 1) → V ↦ SigmaSatisfaction (n + 1) (v 0) (matrixToVec (v ·.succ)))
      (sigmaSatisfactionVec n k) := .mk fun v ↦ by
  simp only [sigmaSatisfactionVec, Nat.succ_eq_add_one, Nat.reduceAdd,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_ex,
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp₂,
    Semiterm.val_operator, Matrix.comp₀, Tarski.Structure.numeral_eq_numeral,
    numeral_eq_natCast_app, Semiterm.val_bvar, Matrix.cons_val_zero, HierarchySymbol.Defined.iff,
    Fin.isValue, Fin.Fin1.eq_one, Fin.succ_zero_eq_one, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.conj_hom_prop, Matrix.comp₃, Fin.succ_one_eq_two,
    Matrix.cons_app_two, Semiformula.eval_operator, Matrix.cons_val_succ,
    Tarski.Structure.eq_iff_eq, LogicalConnective.Prop.and_eq, exists_eq_left];
  constructor;
  · rintro ⟨x, hlen, hnth, hsat⟩;
    have hx : x = matrixToVec (v ·.succ) := by
      apply nth_ext' (k : V) hlen.symm (by simp);
      intro i hi;
      obtain ⟨j, rfl⟩ := lt_numeral_iff.mp (by simpa [← numeral_eq_natCast_app] using hi);
      simp [numeral_eq_natCast_app, hnth j];
    rwa [hx] at hsat;
  · intro hsat;
    exact ⟨matrixToVec (v ·.succ), by simp, fun i ↦ matrixToVec_nth _ i, hsat⟩;

end FFL.FirstOrder.Arithmetic.Bootstrapping
