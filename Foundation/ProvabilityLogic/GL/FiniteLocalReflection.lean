module

public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Reflection
public import Foundation.ProvabilityLogic.GL.Arithmetic

/-!
# Collapsing finitely many local reflection instances

If `T` derives `σ` from finitely many local reflection instances `𝔅 τᵢ 🡒 τᵢ`, then it derives `σ`
from the instances at the sentences `ρ₀ := σ`, `ρᵢ₊₁ := ρᵢ ⋎ 𝔅 ρᵢ`, which depend on `σ` alone.

## References

- [Bek99, Lemma 4.2]
- [Bek99, Lemma 5.2]
-/

@[expose] public section

namespace FFL.FirstOrder.ProvabilityAbstraction.Provability

variable {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T)

def collapseSeq (σ : Sentence L) : ℕ → Sentence L
  | 0 => σ
  | i + 1 => collapseSeq σ i ⋎ 𝔅 (collapseSeq σ i)

end FFL.FirstOrder.ProvabilityAbstraction.Provability

namespace FFL.ProvabilityLogic.FiniteLocalReflection

open Kripke Kripke.Model Kripke.Model.World

variable {α : Type*}

def seq (B : Formula α) : ℕ → Formula α
  | 0 => B
  | i + 1 => seq B i ⋎ □(seq B i)

variable {m : ℕ}

def hyp (m : ℕ) : Formula (Option (Fin (m + 1))) :=
  (⋀(List.ofFn fun i : Fin (m + 1) ↦ □#(some i) 🡒 #(some i))) 🡒 #none

def reflection (m : ℕ) : Formula (Option (Fin (m + 1))) :=
  ⋀(List.ofFn fun i : Fin (m + 1) ↦ □(seq (#none) i) 🡒 seq (#none) i)

section Semantics

variable {κ : Type*} [Nonempty κ] {M : Model κ (Option (Fin (m + 1)))}

lemma not_forces_seq_succ {x : M.World} {B : Formula _} {i : ℕ} :
    x ⊮[M] seq B (i + 1) ↔ x ⊮[M] seq B i ∧ ∃ y, x ≺ y ∧ y ⊮[M] seq B i := by
  grind [seq];

lemma not_forces_of_not_forces_seq {x : M.World} {B : Formula _} {i : ℕ}
    (h : x ⊮[M] seq B i) : x ⊮[M] B := by
  induction i with
  | zero => exact h;
  | succ i ih => exact ih (not_forces_seq_succ.mp h).1;

noncomputable def refuted (x : M.World) : Finset (Fin (m + 1)) := by
  classical
  exact Finset.univ.filter fun i ↦ ∃ z, (z = x ∨ x ≺ z) ∧ z ⊮[M] #(some i)

variable [M.IsFiniteGL]

lemma card_refuted {w : M.World} (hw : ∀ x, x = w ∨ w ≺ x → x ⊩[M] hyp m) :
    ∀ k x, (x = w ∨ w ≺ x) → x ⊮[M] seq (#none) k → k + 1 ≤ (refuted x).card := by
  classical
  have witness : ∀ x, (x = w ∨ w ≺ x) → x ⊮[M] #none →
      ∃ i, x ⊩[M] □#(some i) ∧ x ⊮[M] #(some i) := by
    intro x hx hq;
    rcases forces_imp.mp (hw x hx) with h | h;
    · rw [forces_conj₂] at h;
      push Not at h;
      obtain ⟨A, hA, hxA⟩ := h;
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA;
      exact ⟨i, by grind⟩;
    · exact absurd h hq;
  intro k;
  induction k with
  | zero =>
    intro x hx hs;
    obtain ⟨i, -, hi⟩ := witness x hx hs;
    apply Finset.card_pos.mpr;
    use i;
    simp only [refuted];
    grind;
  | succ k ih =>
    intro x hx hs;
    obtain ⟨hk, y, hxy, hy⟩ := not_forces_seq_succ.mp hs;
    have hrel : ∀ {a b c : M.World}, a ≺ b → (c = b ∨ b ≺ c) → a ≺ c := by
      rintro a b c hab (rfl | hbc);
      · exact hab;
      · exact IsTrans.trans _ _ _ hab hbc;
    have hy' : y = w ∨ w ≺ y := by grind;
    obtain ⟨i, hbox, hi⟩ := witness x hx (not_forces_of_not_forces_seq hk);
    have hsub : refuted y ⊆ refuted x := by simp only [refuted]; grind;
    have hnot : i ∉ refuted y := by simp only [refuted]; grind;
    have hin : i ∈ refuted x := by simp only [refuted]; grind;
    have := ih y hy' hy;
    calc k + 1 + 1 ≤ (refuted y).card + 1 := by omega
      _ = (insert i (refuted y)).card := (Finset.card_insert_of_notMem hnot).symm
      _ ≤ (refuted x).card := Finset.card_le_card (Finset.insert_subset hin hsub)

end Semantics

lemma collapse_mem (m : ℕ) : 𝐆𝐋 ⊢ hyp m 🡒 □hyp m 🡒 reflection m 🡒 #none := by
  classical
  rw [Logic.GL.iff_valid_finite];
  intro κ _ M _ w;
  simp only [forces_imp];
  by_contra! hc;
  obtain ⟨hH, hbH, hR, hq⟩ := hc;
  have hw : ∀ x, x = w ∨ w ≺ x → x ⊩[M] hyp m := by
    rintro x (rfl | hx);
    · exact hH;
    · exact forces_box.mp hbH x hx;
  have hR' : ∀ i : Fin (m + 1),
      w ⊩[M] □(seq (#none) i) 🡒 seq (#none) i := by
    intro i;
    exact forces_conj₂.mp hR _ (List.mem_ofFn.mpr ⟨i, rfl⟩);
  have hs : ∀ k ≤ m + 1, w ⊮[M] seq (#none) k := by
    intro k;
    induction k with
    | zero => intro _; exact hq;
    | succ k ih =>
      intro hk;
      have hk' := ih (by omega);
      have hbox := hR' ⟨k, by omega⟩;
      grind [not_forces_seq_succ];
  have := card_refuted hw (m + 1) w (by simp) (hs (m + 1) le_rfl);
  have := (refuted w).card_le_univ;
  simp at this;
  omega;

end FFL.ProvabilityLogic.FiniteLocalReflection

namespace FFL.FirstOrder.ProvabilityAbstraction.Provability

open FFL.Entailment FFL.ProvabilityLogic FFL.ProvabilityLogic.FiniteLocalReflection

variable {L : Language} [L.ReferenceableBy L] [L.DecidableEq] {T₀ T : Theory L}
  (𝔅 : Provability T₀ T) [T₀ ⪯ T]

section interpret

variable {α : Type*} {f : Realization α L}

variable [𝔅.HBL2]

omit [L.DecidableEq] in
lemma interpret_seq (B : ProvabilityLogic.Formula α) (i : ℕ) :
    T ⊢ (seq B i).interpret f 𝔅 🡘 𝔅.collapseSeq (B.interpret f 𝔅) i := by
  induction i with
  | zero => simp only [seq, collapseSeq]; cl_prover;
  | succ i ih =>
    have hb : T ⊢ 𝔅 ((seq B i).interpret f 𝔅) 🡘 𝔅 (𝔅.collapseSeq (B.interpret f 𝔅) i) :=
      WeakerThan.pbl (𝔅.ext ih);
    simp only [seq, collapseSeq, ProvabilityLogic.Formula.interpret];
    cl_prover [ih, hb];

end interpret

theorem collapse_localReflection [𝔅.HBL] [Diagonalization T₀] {m : ℕ} {σ : Sentence L}
    {τ : Fin (m + 1) → Sentence L} (h : T ⊢ (⩕ i, 𝔅.refl (τ i)) 🡒 σ) :
    T ⊢ (⩕ i : Fin (m + 1), 𝔅.refl (𝔅.collapseSeq σ i)) 🡒 σ := by
  classical
  let f : Realization (Option (Fin (m + 1))) L := ⟨fun o ↦ o.elim σ τ⟩
  have hH : T ⊢ (hyp m).interpret f 𝔅 := by
    have : T ⊢ (⋀(List.ofFn fun i ↦
          □#(some i) 🡒 #(some i))).interpret f 𝔅 🡒
        ⩕ i, 𝔅.refl (τ i) :=
      right_Uconj_intro _ _ fun i ↦ interpret_conj_left (List.mem_ofFn.mpr ⟨i, rfl⟩);
    simp only [hyp, ProvabilityLogic.Formula.interpret] at this ⊢;
    cl_prover [this, h];
  have hbox : T ⊢ 𝔅 ((hyp m).interpret f 𝔅) := WeakerThan.pbl (𝔅.D1 hH);
  have hG₀ : T₀ ⊢ (hyp m 🡒 □hyp m 🡒 reflection m 🡒 #none).interpret f 𝔅 :=
    Logic.GL.arithmetical_soundness (collapse_mem m);
  have hG : T ⊢ (hyp m 🡒 □hyp m 🡒 reflection m 🡒 #none).interpret f 𝔅 := WeakerThan.pbl hG₀;
  have hR : T ⊢ (⩕ i : Fin (m + 1), 𝔅.refl (𝔅.collapseSeq σ i)) 🡒
      (reflection m).interpret f 𝔅 := by
    apply interpret_conj_right;
    intro B hB;
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB;
    have e := interpret_seq 𝔅 (f := f) (#none) i;
    have eb : T ⊢ 𝔅 ((seq (#none) i).interpret f 𝔅) 🡘 𝔅 (𝔅.collapseSeq σ i) :=
      WeakerThan.pbl (𝔅.ext e);
    have l := left_Uconj_intro (𝓢 := T)
      (fun i : Fin (m + 1) ↦ 𝔅.refl (𝔅.collapseSeq σ i)) i;
    simp only [ProvabilityLogic.Formula.interpret] at e eb l ⊢;
    cl_prover [e, eb, l];
  simp only [ProvabilityLogic.Formula.interpret] at hG;
  cl_prover [hH, hbox, hG, hR];

section iterate

variable [𝔅.HBL]

omit [L.DecidableEq] in
lemma collapseSeq_bot (i : ℕ) : T ⊢ 𝔅.collapseSeq ⊥ i 🡘 𝔅^[i] ⊥ := by
  induction i with
  | zero => simp only [collapseSeq, Function.iterate_zero, id]; cl_prover;
  | succ i ih =>
    have hb : T ⊢ 𝔅 (𝔅.collapseSeq ⊥ i) 🡘 𝔅^[i + 1] ⊥ := by
      rw [Function.iterate_succ_apply']; exact WeakerThan.pbl (𝔅.ext ih);
    have hm : T ⊢ 𝔅^[i] ⊥ 🡒 𝔅^[i + 1] ⊥ := boxBot_monotone (by omega);
    simp only [collapseSeq];
    cl_prover [ih, hb, hm];

end iterate

theorem iterate_bot_of_refutable_localReflection [𝔅.HBL] [Diagonalization T₀] {m : ℕ}
    {τ : Fin (m + 1) → Sentence L} (h : T ⊢ ∼⩕ i, 𝔅.refl (τ i)) :
    T ⊢ 𝔅^[m + 1] ⊥ := by
  have hc := 𝔅.collapse_localReflection (σ := ⊥) (τ := τ) (by cl_prover [h]);
  have hr : T ⊢ (∼𝔅^[m + 1] ⊥ : Sentence L) 🡒
      ⩕ i : Fin (m + 1), 𝔅.refl (𝔅.collapseSeq ⊥ i) :=
    right_Uconj_intro _ _ fun i ↦ by
      have e := 𝔅.collapseSeq_bot i;
      have eb : T ⊢ 𝔅 (𝔅.collapseSeq ⊥ i) 🡘 𝔅^[i + 1] ⊥ := by
        rw [Function.iterate_succ_apply']; exact WeakerThan.pbl (𝔅.ext e);
      have hm : T ⊢ 𝔅^[i + 1] ⊥ 🡒 𝔅^[m + 1] ⊥ := boxBot_monotone (by omega);
      cl_prover [e, eb, hm];
  cl_prover [hc, hr];

end FFL.FirstOrder.ProvabilityAbstraction.Provability

end
