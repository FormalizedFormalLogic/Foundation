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

def HierarchicalSatisfaction : Polarity → ℕ → V → V → Prop
  | .sigma, n, z, e => SigmaSatisfaction n z e
  | .pi, n, z, e => PiSatisfaction n z e

noncomputable def piOfSigma (m : ℕ) (σ : 𝚺ᴬ-[m + 1].Semisentence 2) :
    𝚷ᴬ-[m + 1].Semisentence 2 := .mkPi
  “z e. !(isStrictHierarchy 𝚷 (m + 1)).pi z ∧ !(isUFormula ℒₒᵣ).pi z ∧
    ∀ nz, !(negGraph ℒₒᵣ).val nz z → ¬!σ.val nz e”
  (by simp [(isStrictHierarchy 𝚷 (m + 1)).pi.pi_prop.mono (Nat.le_add_left 1 m),
    (isUFormula ℒₒᵣ).pi.pi_prop.mono (Nat.le_add_left 1 m),
    (negGraph ℒₒᵣ).sigma_prop.mono (Nat.le_add_left 1 m), σ.sigma_prop])

noncomputable def sigmaOfPi (m : ℕ) (π : 𝚷ᴬ-[m + 1].Semisentence 2) :
    𝚺ᴬ-[m + 2].Semisentence 2 := .mkSigma
  “z e. ∃ k q w e', !(qqQuantsDef 𝚺) z q k ∧ !(isStrictHierarchy 𝚷 (m + 1)).val q ∧
    !lenDef k w ∧ !vecAppendDef e' w e ∧ !π.val q e'”
  (by
    have h : 1 ≤ m + 2 := by omega;
    simp [(qqQuantsDef 𝚺).sigma_prop.mono h, lenDef.sigma_prop.mono h,
      vecAppendDef.sigma_prop.mono h, π.pi_prop.accum 𝚺])

noncomputable def sigmaZero : 𝚺ᴬ-[1].Semisentence 2 := .mkSigma
  “z e. ∃ k q w e', !(qqQuantsDef 𝚺) z q k ∧ !(isStrictHierarchy 𝚷 0).val q ∧ !lenDef k w ∧
    !vecAppendDef e' w e ∧ !boundedSatisfaction.val q e'”
  (by simp [(qqQuantsDef 𝚺).sigma_prop, lenDef.sigma_prop, vecAppendDef.sigma_prop,
    show ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 (isStrictHierarchy 𝚷 0).val from
      (isStrictHierarchy 𝚷 0).sigma.sigma_prop,
    show ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 boundedSatisfaction.val from boundedSatisfaction.sigma.sigma_prop])

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
  | _ + 1 => simp [piSatisfaction_succ_iff (z := z), hz, hz'];

private lemma piSatisfaction_iff_not_neg (hz : IsStrictPi n z) (hz' : IsUFormula ℒₒᵣ z) :
    PiSatisfaction n z e ↔ ¬SigmaSatisfaction n (neg ℒₒᵣ z) e := by
  simp [SigmaSatisfaction.neg_iff hz hz']

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

section
variable {n : ℕ} {z M K e : V}

private lemma exists_ex_block (z : V) : ∃ K M, z = qqQuants 𝚺 M K ∧ ∀ p : V, M ≠ ^∃ p := by
  have H (z : V) : ∃ K ≤ z, ∃ M ≤ z, z = qqQuants 𝚺 M K ∧ ∀ p < M, M ≠ ^∃ p := by
    induction z using ISigma1.sigma1_order_induction
    · definability;
    case ind z ih =>
      by_cases hz : ∃ p < z, z = ^∃ p;
      · obtain ⟨p, hp, rfl⟩ := hz;
        obtain ⟨K, hK, M, hM, rfl, hM'⟩ := ih p hp;
        exact ⟨K + 1, lt_iff_succ_le.mp (hK.trans_lt (lt_exists _)), M, hM.trans hp.le, by simp,
          hM'⟩;
      · exact ⟨0, by simp, z, by simp, by simp, fun p hp h ↦ hz ⟨p, hp, h⟩⟩;
  obtain ⟨K, -, M, -, h, hM⟩ := H z;
  exact ⟨K, M, h, fun p hp ↦ hM p (hp ▸ lt_exists p) hp⟩;

private lemma ex_block_dominates {q k : V} (hMK : z = qqQuants 𝚺 M K) (hM : ∀ p : V, M ≠ ^∃ p)
    (hqk : z = qqQuants 𝚺 q k) : ∃ j, K = k + j ∧ q = qqQuants 𝚺 M j := by
  rcases le_total k K with h | h;
  · obtain ⟨j, rfl⟩ := exists_add_of_le h;
    exact ⟨j, rfl, qqQuants_cancel k q M j (by rw [← hqk, hMK])⟩;
  · obtain ⟨j, rfl⟩ := exists_add_of_le h;
    have hMq : M = qqQuants 𝚺 q j := qqQuants_cancel K M q j (by rw [← hMK, hqk]);
    rcases zero_or_succ j with rfl | ⟨j, rfl⟩;
    · exact ⟨0, by simp, by simpa using hMq.symm⟩;
    · exact absurd hMq (by simpa using hM _);

private lemma isStrictSigma_of_isStrictPi_ex {p : V} (h : IsStrictPi (n + 1) (^∃ p)) :
    IsStrictSigma n (^∃ p) := by
  obtain ⟨k, q, heq, hq⟩ := h;
  rcases zero_or_succ k with rfl | ⟨k, rfl⟩;
  · obtain rfl : ^∃ p = q := by simpa using heq;
    exact hq;
  · simp [qqExs, qqAll, pair_ext_iff] at heq;

private lemma isBounded_ex_block (hz : IsBounded z) (hMK : z = qqQuants 𝚺 M K)
    (hM : ∀ p : V, M ≠ ^∃ p) : IsBounded M ∧ K ≤ 1 := by
  subst hMK;
  rcases zero_or_succ K with rfl | ⟨K, rfl⟩;
  · simpa using hz;
  · obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, heq⟩ := IsBounded.of_ex (by simpa using hz);
    rcases zero_or_succ K with rfl | ⟨K, rfl⟩;
    · obtain rfl : M = _ := by simpa using heq;
      exact ⟨IsBounded.and_iff.mpr ⟨by simp [Arithmetic.qqLT], hq⟩, by simp⟩;
    · simp [qqExs, qqAnd, pair_ext_iff] at heq;

private lemma isStrictPi_ex_block : ∀ (n : ℕ) (z M K : V), IsStrictSigma (n + 1) z →
    z = qqQuants 𝚺 M K → (∀ p : V, M ≠ ^∃ p) → IsStrictPi n M
  | n, _, M, _, ⟨k, q, hqk, hq⟩, hMK, hM => by
    obtain ⟨j, -, rfl⟩ := ex_block_dominates hMK hM hqk;
    rcases zero_or_succ j with rfl | ⟨j, rfl⟩;
    · simpa using hq;
    · match n with
      | 0 => exact (isBounded_ex_block hq rfl hM).1;
      | n + 1 =>
        have hs : IsStrictSigma n (qqQuants 𝚺 M (j + 1)) := by
          simpa using isStrictSigma_of_isStrictPi_ex (by simpa using hq);
        match n with
        | 0 => exact IsStrictHierarchy.of_bounded (isBounded_ex_block hs rfl hM).1;
        | n + 1 =>
          exact IsStrictHierarchy.mono (by omega) (isStrictPi_ex_block n _ M (j + 1) hs rfl hM);

private lemma isStrictPi_ex_block' (hz : IsStrictSigma n z) (hMK : z = qqQuants 𝚺 M K)
    (hM : ∀ p : V, M ≠ ^∃ p) : IsStrictPi n M := by
  match n with
  | 0 => exact (isBounded_ex_block hz hMK hM).1;
  | n + 1 => exact IsStrictHierarchy.mono (Nat.le_succ n) (isStrictPi_ex_block n z M K hz hMK hM);

/-! ### The $\Delta_0$ case -/

private lemma boundedSatisfaction_ex_iff {p : V} (h : IsBounded (^∃ p)) :
    BoundedSatisfaction (^∃ p) e ↔ ∃ x, BoundedSatisfaction p (x ∷ e) := by
  obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ := IsBounded.of_ex h;
  have hlt (x : V) : BoundedSatisfaction (Arithmetic.qqLT (qqBvar 0) (termBShift ℒₒᵣ t)) (x ∷ e) ↔
      x < termVal e t := by
    rw [BoundedSatisfaction.lt_iff (by simp) ht.termBShift];
    simp [termVal_termBShift ht x e];
  rw [show (^∃ ((Arithmetic.qqLT (qqBvar 0) (termBShift ℒₒᵣ t)) ^⋏ q) : V)
      = qqBex (termBShift ℒₒᵣ t) q from rfl, BoundedSatisfaction.bex_iff ht];
  simp [BoundedSatisfaction.and_iff, hlt];

private lemma boundedSatisfaction_block (hz : IsBounded z) (hMK : z = qqQuants 𝚺 M K)
    (hM : ∀ p : V, M ≠ ^∃ p) :
    BoundedSatisfaction z e ↔ ∃ w, len w = K ∧ BoundedSatisfaction M (vecAppend w e) := by
  obtain ⟨-, hK⟩ := isBounded_ex_block hz hMK hM;
  subst hMK;
  rcases zero_or_succ K with rfl | ⟨K, rfl⟩;
  · simp [len_zero_iff_eq_nil];
  · obtain rfl : K = 0 := by simpa using hK;
    rw [qqQuants_succ, qqQuants_zero, qqQuant_sigma] at hz ⊢;
    rw [boundedSatisfaction_ex_iff hz];
    simp [eq_singleton_iff_len_eq_one];

end

/-! ### The block characterization -/

private def BlockSatisfaction (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (n : ℕ) : Prop :=
  ∀ z M K e : V, IsStrictSigma (n + 1) z → IsUFormula ℒₒᵣ z → z = qqQuants 𝚺 M K →
    (∀ p : V, M ≠ ^∃ p) →
      (SigmaSatisfaction (n + 1) z e ↔ ∃ w, len w = K ∧ PiSatisfaction n M (vecAppend w e))

section
variable {n : ℕ} {z M K e : V}

private lemma pi_iff_of_sigma_iff {m : ℕ} (hmn : m ≤ n)
    (H : ∀ z e : V, IsStrictSigma m z → IsUFormula ℒₒᵣ z →
      (SigmaSatisfaction m z e ↔ SigmaSatisfaction n z e))
    (hz : IsStrictPi m z) (hz' : IsUFormula ℒₒᵣ z) :
    PiSatisfaction m z e ↔ PiSatisfaction n z e := by
  rw [piSatisfaction_iff_not_neg hz hz',
    piSatisfaction_iff_not_neg (IsStrictHierarchy.mono hmn hz) hz',
    H _ e (IsStrictHierarchy.neg hz' hz) hz'.neg];

private lemma pi_succ_iff_sigma_of
    (H : ∀ z e : V, IsStrictPi n z → IsUFormula ℒₒᵣ z →
      (SigmaSatisfaction (n + 1) z e ↔ PiSatisfaction n z e))
    (hz : IsStrictSigma n z) (hz' : IsUFormula ℒₒᵣ z) :
    PiSatisfaction (n + 1) z e ↔ SigmaSatisfaction n z e := by
  rw [piSatisfaction_iff_not_neg (IsStrictHierarchy.of_alt hz) hz',
    H _ e (IsStrictHierarchy.neg hz' hz) hz'.neg, PiSatisfaction.neg_iff hz hz', not_not];

private lemma sigma_block (hB : ∀ m < n, BlockSatisfaction V m) (hz : IsStrictSigma n z)
    (hz' : IsUFormula ℒₒᵣ z) (hMK : z = qqQuants 𝚺 M K) (hM : ∀ p : V, M ≠ ^∃ p) :
    SigmaSatisfaction n z e ↔ ∃ w, len w = K ∧ PiSatisfaction n M (vecAppend w e) := by
  induction n generalizing z M K e with
  | zero => simpa using boundedSatisfaction_block hz hMK hM;
  | succ n ih =>
    have H (z e : V) (hz : IsStrictSigma n z) (hz' : IsUFormula ℒₒᵣ z) :
        SigmaSatisfaction n z e ↔ SigmaSatisfaction (n + 1) z e := by
      obtain ⟨K, M, hMK, hM⟩ := exists_ex_block z;
      exact (ih (fun m hm ↦ hB m (by omega)) hz hz' hMK hM).trans
        (hB n (by omega) z M K e (IsStrictHierarchy.mono (Nat.le_succ n) hz) hz' hMK hM).symm;
    rw [hB n (by omega) z M K e hz hz' hMK hM];
    exact exists_congr fun w ↦ and_congr_right fun _ ↦ pi_iff_of_sigma_iff (Nat.le_succ n) H
      (isStrictPi_ex_block n z M K hz hMK hM) (isUFormula_qqQuants.mp (hMK ▸ hz'));

private lemma sigma_mono_step (hB : ∀ m ≤ n, BlockSatisfaction V m) (hz : IsStrictSigma n z)
    (hz' : IsUFormula ℒₒᵣ z) : SigmaSatisfaction n z e ↔ SigmaSatisfaction (n + 1) z e := by
  obtain ⟨K, M, hMK, hM⟩ := exists_ex_block z;
  exact (sigma_block (fun m hm ↦ hB m hm.le) hz hz' hMK hM).trans
    (hB n le_rfl z M K e (IsStrictHierarchy.mono (Nat.le_succ n) hz) hz' hMK hM).symm;

private lemma pi_mono_step (hB : ∀ m ≤ n, BlockSatisfaction V m) (hz : IsStrictPi n z)
    (hz' : IsUFormula ℒₒᵣ z) : PiSatisfaction n z e ↔ PiSatisfaction (n + 1) z e :=
  pi_iff_of_sigma_iff (Nat.le_succ n) (fun _ _ ↦ sigma_mono_step hB) hz hz'

private lemma piSatisfaction_ex_block (hB : ∀ m < n, BlockSatisfaction V m)
    (H : ∀ m < n, ∀ z e : V, IsStrictPi m z → IsUFormula ℒₒᵣ z →
      (SigmaSatisfaction (m + 1) z e ↔ PiSatisfaction m z e))
    (hz : IsStrictPi n z) (hz' : IsUFormula ℒₒᵣ z) (hMK : z = qqQuants 𝚺 M (K + 1))
    (hM : ∀ p : V, M ≠ ^∃ p) :
    PiSatisfaction n z e ↔ ∃ w, len w = K + 1 ∧ PiSatisfaction n M (vecAppend w e) := by
  match n with
  | 0 => simpa using boundedSatisfaction_block hz hMK hM;
  | n + 1 =>
    have hzs : IsStrictSigma n z := by
      subst hMK;
      simpa using isStrictSigma_of_isStrictPi_ex (by simpa using hz);
    rw [pi_succ_iff_sigma_of (H n (by omega)) hzs hz',
      sigma_block (fun m hm ↦ hB m (by omega)) hzs hz' hMK hM];
    exact exists_congr fun w ↦ and_congr_right fun _ ↦
      pi_mono_step (fun m hm ↦ hB m (by omega)) (isStrictPi_ex_block' hzs hMK hM)
        (isUFormula_qqQuants.mp (hMK ▸ hz'));

private lemma sigma_succ_iff_pi (hB : ∀ m ≤ n, BlockSatisfaction V m) (hz : IsStrictPi n z)
    (hz' : IsUFormula ℒₒᵣ z) : SigmaSatisfaction (n + 1) z e ↔ PiSatisfaction n z e := by
  induction n using Nat.strong_induction_on generalizing z e with
  | _ n ih =>
    obtain ⟨K, M, hMK, hM⟩ := exists_ex_block z;
    rw [hB n le_rfl z M K e (IsStrictHierarchy.of_alt hz) hz' hMK hM];
    rcases zero_or_succ K with rfl | ⟨K, rfl⟩;
    · simp [hMK, len_zero_iff_eq_nil];
    · exact (piSatisfaction_ex_block (fun m hm ↦ hB m hm.le)
        (fun m hm _ _ ↦ ih m hm fun i hi ↦ hB i (by omega)) hz hz' hMK hM).symm;

private lemma pi_succ_iff_sigma (hB : ∀ m ≤ n, BlockSatisfaction V m) (hz : IsStrictSigma n z)
    (hz' : IsUFormula ℒₒᵣ z) : PiSatisfaction (n + 1) z e ↔ SigmaSatisfaction n z e :=
  pi_succ_iff_sigma_of (fun _ _ ↦ sigma_succ_iff_pi hB) hz hz'

end

private lemma blockSatisfaction (n : ℕ) : BlockSatisfaction V n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z M K e hz hz' hMK hM;
    constructor;
    · intro h;
      obtain ⟨k, q, hqk, hq, w, hw, hsat⟩ := sigmaSatisfaction_succ_iff.mp h;
      obtain ⟨j, rfl, rfl⟩ := ex_block_dominates hMK hM hqk;
      rcases zero_or_succ j with rfl | ⟨j, rfl⟩;
      · exact ⟨w, by simpa using hw, by simpa using hsat⟩;
      · obtain ⟨u, hu, husat⟩ := (piSatisfaction_ex_block ih
          (fun m hm _ _ ↦ sigma_succ_iff_pi fun i hi ↦ ih i (by omega)) hq
          (isUFormula_qqQuants.mp (hqk ▸ hz')) rfl hM).mp hsat;
        exact ⟨vecAppend u w, by simp [hu, hw, add_comm], by simpa [vecAppend_assoc] using husat⟩;
    · rintro ⟨w, hw, hsat⟩;
      exact sigmaSatisfaction_succ_iff.mpr
        ⟨K, M, hMK, isStrictPi_ex_block n z M K hz hMK hM, w, hw, hsat⟩;

section
variable {n : ℕ} {z e : V}

theorem SigmaSatisfaction.of_pi (hz : IsStrictPi n z) (hz' : IsUFormula ℒₒᵣ z) :
    SigmaSatisfaction (n + 1) z e ↔ PiSatisfaction n z e :=
  sigma_succ_iff_pi (fun m _ ↦ blockSatisfaction m) hz hz'

theorem PiSatisfaction.of_sigma (hz : IsStrictSigma n z) (hz' : IsUFormula ℒₒᵣ z) :
    PiSatisfaction (n + 1) z e ↔ SigmaSatisfaction n z e :=
  pi_succ_iff_sigma (fun m _ ↦ blockSatisfaction m) hz hz'

theorem HierarchicalSatisfaction.of_alt {Γ : Polarity} (hz : IsStrictHierarchy Γ.alt n z)
    (hz' : IsUFormula ℒₒᵣ z) :
    HierarchicalSatisfaction Γ (n + 1) z e ↔ HierarchicalSatisfaction Γ.alt n z e := by
  cases Γ;
  · exact SigmaSatisfaction.of_pi hz hz';
  · exact PiSatisfaction.of_sigma hz hz';

end

section
variable {n : ℕ} {p e : V}

theorem SigmaSatisfaction.exs_iff : SigmaSatisfaction (n + 1) (^∃ p) e ↔
    ∃ x, SigmaSatisfaction (n + 1) p (x ∷ e) := by
  by_cases hp : IsStrictSigma (n + 1) p ∧ IsUFormula ℒₒᵣ p;
  · obtain ⟨K, M, hMK, hM⟩ := exists_ex_block p;
    have h (x : V) := blockSatisfaction n p M K (x ∷ e) hp.1 hp.2 hMK hM;
    rw [blockSatisfaction n (^∃ p) M (K + 1) e (IsStrictHierarchy.quant hp.1) (by simp [hp.2])
      (by simp [hMK]) hM];
    constructor;
    · rintro ⟨w, hw, hsat⟩;
      obtain ⟨u, x, hu, rfl⟩ := exists_vecAppend_singleton hw;
      exact ⟨x, (h x).mpr ⟨u, hu, by simpa [vecAppend_assoc] using hsat⟩⟩;
    · rintro ⟨x, hx⟩;
      obtain ⟨u, hu, hsat⟩ := (h x).mp hx;
      exact ⟨vecAppend u ?[x], by simp [hu], by simpa [vecAppend_assoc] using hsat⟩;
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
    exact ih.trans (sigma_mono_step (fun i _ ↦ blockSatisfaction i) (hz.mono hn) hz');

theorem PiSatisfaction.mono (hz : IsStrictPi m z) (hz' : IsUFormula ℒₒᵣ z) :
    PiSatisfaction m z e ↔ PiSatisfaction n z e := by
  induction n, h using Nat.le_induction with
  | base => rfl;
  | succ n hn ih =>
    exact ih.trans (pi_mono_step (fun i _ ↦ blockSatisfaction i) (hz.mono hn) hz');

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

section
variable {n : ℕ} {m l w p e : V}

lemma isSemitermVec_qVecIter (hw : IsSemitermVec ℒₒᵣ m l w) (k : V) :
    IsSemitermVec ℒₒᵣ (m + k) (l + k) (qVecIter w k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability;
  case zero => simpa using hw;
  case succ k ih =>
    rw [qVecIter_succ, ← add_assoc, ← add_assoc];
    exact ih.qVec;

lemma termValVec_qVecIter (hw : IsSemitermVec ℒₒᵣ m l w) (k : V) :
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

lemma IsStrictHierarchy.subst {Γ : Polarity} (hw : IsSemitermVec ℒₒᵣ m l w)
    (hp : IsSemiformula ℒₒᵣ m p) (h : IsStrictHierarchy Γ n p) :
    IsStrictHierarchy Γ n (Bootstrapping.subst ℒₒᵣ w p) := by
  induction n generalizing Γ m l w p with
  | zero => exact IsBounded.subst hw hp h;
  | succ n ih =>
    obtain ⟨k, q, rfl, hq⟩ := h;
    have hqp : IsSemiformula ℒₒᵣ (m + k) q := (isSemiformula_qqQuants k m).mp hp;
    exact ⟨k, Bootstrapping.subst ℒₒᵣ (qVecIter w k) q, substs_qqQuants hqp.isUFormula k w,
      ih (isSemitermVec_qVecIter hw k) hqp hq⟩;

private lemma not_ex_subst {M : V} (hM : IsUFormula ℒₒᵣ M) (h : ∀ p : V, M ≠ ^∃ p) :
    ∀ r : V, Bootstrapping.subst ℒₒᵣ w M ≠ ^∃ r := by
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

theorem SigmaSatisfaction.subst (hw : IsSemitermVec ℒₒᵣ m l w)
    (hp : IsSemiformula ℒₒᵣ m p) (hp' : IsStrictSigma n p) :
    SigmaSatisfaction n (Bootstrapping.subst ℒₒᵣ w p) e ↔
      SigmaSatisfaction n p (termValVec e m w) := by
  induction n generalizing m l w p e with
  | zero => simpa using BoundedSatisfaction.subst hw hp hp';
  | succ n ih =>
    obtain ⟨K, M, hMK, hM⟩ := exists_ex_block p;
    have hMs : IsSemiformula ℒₒᵣ (m + K) M := (isSemiformula_qqQuants K m).mp (hMK ▸ hp);
    have hMpi : IsStrictPi n M := isStrictPi_ex_block n p M K hp' hMK hM;
    have hw' := isSemitermVec_qVecIter hw K;
    rw [blockSatisfaction n _ (Bootstrapping.subst ℒₒᵣ (qVecIter w K) M) K e (hp'.subst hw hp)
        (hp.subst hw).isUFormula (by rw [hMK, substs_qqQuants hMs.isUFormula K w])
        (not_ex_subst hMs.isUFormula hM),
      blockSatisfaction n p M K (termValVec e m w) hp' hp.isUFormula hMK hM];
    exact exists_congr fun v ↦ and_congr_right fun hv ↦ by
      rw [← termValVec_qVecIter hw K v hv,
        piSatisfaction_iff_not_neg (hMpi.subst hw' hMs) (hMs.subst hw').isUFormula,
        ← substs_neg hMs hw', ih hw' (by simp [hMs]) (IsStrictHierarchy.neg hMs.isUFormula hMpi),
        SigmaSatisfaction.neg_iff hMpi hMs.isUFormula, not_not];

end

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
  suffices (∃ x, ↑k = len x ∧ (∀ i : Fin k, x.[↑↑i] = v i.succ) ∧
      SigmaSatisfaction (n + 1) (v 0) x) ↔ SigmaSatisfaction (n + 1) (v 0) (matrixToVec (v ·.succ))
    by simpa [sigmaSatisfactionVec, numeral_eq_natCast_app] using this;
  constructor;
  · rintro ⟨x, hlen, hnth, hsat⟩;
    suffices x = matrixToVec (v ·.succ) from this ▸ hsat;
    apply nth_ext' (k : V) hlen.symm (by simp);
    intro i hi;
    obtain ⟨j, rfl⟩ := lt_numeral_iff.mp (by simpa [← numeral_eq_natCast_app] using hi);
    simp [numeral_eq_natCast_app, hnth j];
  · exact fun hsat ↦ ⟨matrixToVec (v ·.succ), by simp, fun i ↦ matrixToVec_nth _ i, hsat⟩;

end FFL.FirstOrder.Arithmetic.Bootstrapping
