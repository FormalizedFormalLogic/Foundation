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

namespace FFL.ProvabilityLogic.FiniteLocalReflection

open Kripke Kripke.Model Kripke.Model.World

variable {α : Type*} {m : ℕ}

def seq (B : Formula α) : ℕ → Formula α
  | 0 => B
  | i + 1 => seq B i ⋎ □(seq B i)

def hyp (m : ℕ) : Formula (Option (Fin (m + 1))) :=
  (⋀(List.ofFn fun i : Fin (m + 1) ↦ □#(some i) 🡒 #(some i))) 🡒 #none

def reflection (m : ℕ) : Formula (Option (Fin (m + 1))) :=
  ⋀(List.ofFn fun i : Fin (m + 1) ↦ □(seq (#none) i) 🡒 seq (#none) i)

section Semantics

variable {κ : Type*} [Nonempty κ] {M : Model κ (Option (Fin (m + 1)))} {x w : M.World} {k : ℕ}

lemma not_forces_seq_succ {B : Formula _} :
    x ⊮[M] seq B (k + 1) ↔ x ⊮[M] seq B k ∧ ∃ y, x ≺ y ∧ y ⊮[M] seq B k := by
  grind [seq];

open scoped Classical in
noncomputable def refuted (x : M.World) : Finset (Fin (m + 1)) :=
  {i | ∃ z, (z = x ∨ x ≺ z) ∧ z ⊮[M] #(some i)}

lemma card_refuted [M.IsFiniteGL] (hw : w ⊩[M] hyp m) (hbw : w ⊩[M] □hyp m) (hx : x = w ∨ w ≺ x)
    (hs : x ⊮[M] seq (#none) k) : k + 1 ≤ (refuted x).card := by
  have witness : ∀ {x k}, (x = w ∨ w ≺ x) → x ⊮[M] seq (#none) k →
      ∃ i, x ⊩[M] □#(some i) ∧ x ⊮[M] #(some i) := by
    intro x k hx hs;
    induction k <;> grind [seq, hyp, forces_conj₂];
  have htrans : ∀ {a b c : M.World}, a ≺ b → b ≺ c → a ≺ c := IsTrans.trans _ _ _;
  induction k generalizing x with
  | zero =>
    obtain ⟨i, -, hi⟩ := witness hx hs;
    exact Finset.card_pos.mpr ⟨i, by grind [refuted]⟩;
  | succ k ih =>
    obtain ⟨-, y, hxy, hy⟩ := not_forces_seq_succ.mp hs;
    obtain ⟨i, hbox, hi⟩ := witness hx hs;
    calc k + 1 + 1 ≤ (refuted y).card + 1 := by grind
      _ = (insert i (refuted y)).card :=
        (Finset.card_insert_of_notMem <| by grind [refuted]).symm
      _ ≤ (refuted x).card :=
        Finset.card_le_card <| Finset.insert_subset (by grind [refuted]) (by grind [refuted])

end Semantics

lemma collapse_mem (m : ℕ) : 𝐆𝐋 ⊢ hyp m 🡒 □hyp m 🡒 reflection m 🡒 #none := by
  rw [Logic.GL.iff_valid_finite];
  intro κ _ M _ w;
  simp only [forces_imp];
  by_contra! ⟨hH, hbH, hR, hq⟩;
  have hs : ∀ k ≤ m + 1, w ⊮[M] seq (#none) k := by
    intro k hk;
    induction k with
    | zero => exact hq;
    | succ k ih =>
      have := forces_conj₂.mp hR _ (List.mem_ofFn.mpr ⟨⟨k, by omega⟩, rfl⟩);
      grind [not_forces_seq_succ];
  simpa using (card_refuted hH hbH (by simp) (hs (m + 1) le_rfl)).trans (refuted w).card_le_univ;

end FFL.ProvabilityLogic.FiniteLocalReflection

namespace FFL.FirstOrder.ProvabilityAbstraction.Provability

open FFL.Entailment FFL.ProvabilityLogic FFL.ProvabilityLogic.FiniteLocalReflection

variable {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T)

def collapseSeq (σ : Sentence L) : ℕ → Sentence L
  | 0 => σ
  | i + 1 => collapseSeq σ i ⋎ 𝔅 (collapseSeq σ i)

variable [L.DecidableEq] [T₀ ⪯ T] [𝔅.HBL] [Diagonalization T₀] {m : ℕ}

theorem collapse_localReflection {σ : Sentence L} {τ : Fin (m + 1) → Sentence L}
    (h : T ⊢ (⩕ i, 𝔅.refl (τ i)) 🡒 σ) :
    T ⊢ (⩕ i : Fin (m + 1), 𝔅.refl (𝔅.collapseSeq σ i)) 🡒 σ := by
  let f : Realization (Option (Fin (m + 1))) L := ⟨fun o ↦ o.elim σ τ⟩
  have hH : T ⊢ (hyp m).interpret f 𝔅 :=
    C_trans (right_Uconj_intro _ _ fun i ↦ interpret_conj_left <| List.mem_ofFn.mpr ⟨i, rfl⟩) h;
  have hG : T ⊢ (hyp m 🡒 □hyp m 🡒 reflection m 🡒 #none).interpret f 𝔅 :=
    WeakerThan.pbl <| Logic.GL.arithmetical_soundness (𝔅 := 𝔅) (collapse_mem m);
  have hR : T ⊢ (⩕ i : Fin (m + 1), 𝔅.refl (𝔅.collapseSeq σ i)) 🡒 (reflection m).interpret f 𝔅 := by
    have e : ∀ i, T ⊢ (seq (#none) i).interpret f 𝔅 🡘 𝔅.collapseSeq σ i := by
      intro i;
      induction i with
      | zero => exact E_id;
      | succ i ih =>
        simp only [seq, collapseSeq, Formula.interpret];
        cl_prover [ih, WeakerThan.pbl (𝓣 := T) (𝔅.ext ih)];
    apply interpret_conj_right;
    intro B hB;
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB;
    apply C_trans (left_Uconj_intro _ i);
    simp only [Formula.interpret];
    cl_prover [e i, WeakerThan.pbl (𝓣 := T) (𝔅.ext (e i))];
  exact C_trans hR <| hG ⨀ hH ⨀ WeakerThan.pbl (𝔅.D1 hH);

theorem iterate_bot_of_refutable_localReflection {τ : Fin (m + 1) → Sentence L}
    (h : T ⊢ ∼⩕ i, 𝔅.refl (τ i)) : T ⊢ 𝔅^[m + 1] ⊥ := by
  have e : ∀ i, T ⊢ 𝔅.collapseSeq ⊥ i 🡘 𝔅^[i] ⊥ := by
    intro i;
    induction i with
    | zero => exact E_id;
    | succ i ih =>
      have hb : T ⊢ 𝔅 (𝔅.collapseSeq ⊥ i) 🡘 𝔅^[i + 1] ⊥ := by
        rw [Function.iterate_succ_apply']; exact WeakerThan.pbl (𝓣 := T) (𝔅.ext ih);
      simp only [collapseSeq];
      cl_prover [ih, hb, boxBot_monotone (𝔅 := 𝔅) (Nat.le_succ i)];
  have hr : T ⊢ ∼𝔅^[m + 1] ⊥ 🡒 ⩕ i : Fin (m + 1), 𝔅.refl (𝔅.collapseSeq ⊥ i) :=
    right_Uconj_intro _ _ fun i ↦ by
      have : T ⊢ 𝔅.collapseSeq ⊥ i ⋎ 𝔅 (𝔅.collapseSeq ⊥ i) 🡘 𝔅^[i + 1] ⊥ := e (i + 1);
      cl_prover [this, boxBot_monotone (𝔅 := 𝔅) i.isLt];
  have := 𝔅.collapse_localReflection (σ := ⊥) (τ := τ) (by cl_prover [h]);
  cl_prover [this, hr];

end FFL.FirstOrder.ProvabilityAbstraction.Provability

end
