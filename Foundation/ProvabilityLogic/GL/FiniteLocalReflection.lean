module

public import Foundation.ProvabilityLogic.GL.Basic

/-!
# The modal core of collapsing finitely many local reflection instances

With `ρ₀ := q`, `ρᵢ₊₁ := ρᵢ ⋎ □ρᵢ` and `H := (⋀_{i ≤ m} □pᵢ 🡒 pᵢ) 🡒 q`,
`GL ⊢ H 🡒 □H 🡒 (⋀_{i ≤ m} □ρᵢ 🡒 ρᵢ) 🡒 q`.

## References

- [Bek99, Lemma 4.2]
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
    x ⊮ seq B (k + 1) ↔ x ⊮ seq B k ∧ ∃ y, x ≺ y ∧ y ⊮ seq B k := by
  grind [seq];

open scoped Classical in
noncomputable def refuted (x : M.World) : Finset (Fin (m + 1)) :=
  {i | ∃ z, (z = x ∨ x ≺ z) ∧ z ⊮ #(some i)}

lemma card_refuted [M.IsFiniteGL] (hw : w ⊩ hyp m) (hbw : w ⊩ □hyp m) (hx : x = w ∨ w ≺ x)
    (hs : x ⊮ seq (#none) k) : k + 1 ≤ (refuted x).card := by
  have witness : ∀ {x k}, (x = w ∨ w ≺ x) → x ⊮ seq (#none) k →
      ∃ i, x ⊩ □#(some i) ∧ x ⊮ #(some i) := by
    intro x k hx hs;
    induction k <;> grind [seq, hyp, forces_conj₂];
  induction k generalizing x with
  | zero =>
    obtain ⟨i, -, hi⟩ := witness hx hs;
    exact Finset.card_pos.mpr ⟨i, by grind [refuted]⟩;
  | succ k ih =>
    obtain ⟨-, y, hxy, hy⟩ := not_forces_seq_succ.mp hs;
    obtain ⟨i, hbox, hi⟩ := witness hx hs;
    calc k + 1 + 1 ≤ (refuted y).card + 1 := by grind [IsTrans.trans (r := M.Rel)]
      _ = (insert i (refuted y)).card :=
        (Finset.card_insert_of_notMem <| by grind [refuted, IsTrans.trans (r := M.Rel)]).symm
      _ ≤ (refuted x).card :=
        Finset.card_le_card <| Finset.insert_subset (by grind [refuted]) <| by
          grind [refuted, IsTrans.trans (r := M.Rel)]

end Semantics

lemma collapse_mem (m : ℕ) : 𝐆𝐋 ⊢ hyp m 🡒 □hyp m 🡒 reflection m 🡒 #none := by
  rw [Logic.GL.iff_valid_finite];
  intro κ _ M _ w hH hbH hR;
  by_contra! hq;
  have hs : ∀ k ≤ m + 1, w ⊮ seq (#none) k := by
    intro k hk;
    induction k with
    | zero => exact hq;
    | succ k ih =>
      have := forces_conj₂.mp hR _ (List.mem_ofFn.mpr ⟨⟨k, by omega⟩, rfl⟩);
      grind [not_forces_seq_succ];
  simpa using (card_refuted hH hbH (by simp) (hs (m + 1) le_rfl)).trans (refuted w).card_le_univ;

end FFL.ProvabilityLogic.FiniteLocalReflection

end
