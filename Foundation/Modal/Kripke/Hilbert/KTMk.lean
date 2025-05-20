import Foundation.Modal.Kripke.AxiomMk
import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filtration
import Foundation.Modal.Logic.Basic
import Foundation.Modal.Entailment.KT
import Foundation.Modal.Kripke.Hilbert.GrzPoint2

namespace List

variable {α} {l : List α}

lemma nodup_iff_get_ne_get : l.Nodup ↔ ∀ i j : Fin l.length, i < j → l[i] ≠ l[j] := by
  apply Iff.trans nodup_iff_getElem?_ne_getElem?;
  constructor;
  . rintro h ⟨i, _⟩ ⟨j, hj⟩ hij;
    have := h i j (by omega) hj;
    simp_all;
  . rintro h i j hij hj;
    rw [getElem?_eq_getElem, getElem?_eq_getElem];
    simpa [Option.some.injEq] using h ⟨i, by omega⟩ ⟨j, by omega⟩ hij;

end List


lemma List.Nodup.infinite_of_infinite : Infinite {l : List α // l.Nodup} → Infinite α := by
  contrapose!;
  simp only [not_infinite_iff_finite];
  intro _;
  exact List.Nodup.finite;

namespace LO.Entailment.Modal

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]
variable {𝓢 : S} {φ ψ : F}

section

protected class KTMk (𝓢 : S) extends Entailment.Modal.KT 𝓢, Entailment.Modal.HasAxiomMk 𝓢

end

end LO.Entailment.Modal



namespace LO.Modal

namespace Hilbert

section

open Deduction

variable {α} [DecidableEq α] {H : Hilbert α}

class HasMk (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_Mk : Axioms.Modal.Mk (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [H.HasMk] : Entailment.Modal.HasAxiomMk H where
  Mk φ ψ := by
    apply maxm;
    use Axioms.Modal.Mk (.atom $ HasMk.p H) (.atom $ HasMk.q H);
    constructor;
    . exact HasMk.mem_Mk;
    . use (λ b => if b = (HasMk.q H) then ψ else if b = (HasMk.p H) then φ else (.atom b));
      simp [HasMk.ne_pq];

end

protected abbrev KTMk : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Modal.Mk (.atom 0) (.atom 1)}⟩
instance : (Hilbert.KTMk).HasK where p := 0; q := 1;
instance : (Hilbert.KTMk).HasT where p := 0
instance : (Hilbert.KTMk).HasMk where p := 0; q := 1
instance : Entailment.Modal.KTMk (Hilbert.KTMk) where

end Hilbert



namespace Kripke

protected abbrev FrameClass.refl_makinson : FrameClass := { F | IsRefl _ F ∧ SatisfiesMakinsonCondition _ F.Rel }

end Kripke



open Kripke
open Hilbert.Kripke
open Geachean

namespace Hilbert.KTMk.Kripke

instance sound : Sound (Hilbert.KTMk) Kripke.FrameClass.refl_makinson := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_axiomMk_of_satisfiesMakinsonCondition;

instance consistent : Entailment.Consistent (Hilbert.KTMk) := consistent_of_sound_frameclass Kripke.FrameClass.refl_makinson $ by
  use whitepoint;
  constructor;
  . infer_instance;
  . constructor;
    intro x;
    use x;
    tauto;

instance canonical : Canonical (Hilbert.KTMk) Kripke.FrameClass.refl_makinson := sorry

instance complete : Complete (Hilbert.KTMk) Kripke.FrameClass.refl_makinson := inferInstance


section

open Formula.Kripke
open Entailment

set_option pp.proofs true in
lemma validate_axiomFour_of_finite_model {M : Kripke.Model} (hM : M ⊧* Hilbert.KTMk.logic)
  : Finite M → ∀ φ : Formula ℕ, M ⊧ Axioms.Four φ := by
  contrapose!;
  rintro ⟨φ, hφ⟩;
  apply not_finite_iff_infinite.mpr;
  apply List.Nodup.infinite_of_infinite;
  have H : ∀ n : ℕ+, ∃ l : List M.World, l.Nodup ∧ l.length = n ∧ List.Chain' (· ≺ ·) l ∧ (∀ i : Fin l.length, l[i] ⊧ □^[(i + 1)]φ ⋏ ∼□^[(i + 2)]φ) := by
    intro n;
    induction n with
    | one =>
      replace ⟨x₀, hφ⟩ := ValidOnModel.exists_world_of_not hφ;
      use [x₀];
      simpa using hφ;
    | succ n ih =>
      obtain ⟨l, hl_nodup, hl_len, hl_chain, hl⟩ := ih;
      let m : Fin l.length := ⟨n - 1, by simp [hl_len]⟩;
      have : l[m] ⊧ ◇(□^[(m + 2)]φ ⋏ ∼□^[(m + 3)]φ) := Satisfies.mdp ?_ $ hl m;
      obtain ⟨y, Rmy, hy₂⟩ := Satisfies.dia_def.mp this;
      let l' := l.concat y;
      use l';
      have hl' : ∀ (i : Fin l'.length), l'[i] ⊧ □^[(i + 1)]φ ⋏ ∼□^[(i + 2)]φ := by
        rintro ⟨i, hi'⟩;
        replace hi : i < l.length ∨ i = l.length := by
          simp [l'] at hi';
          omega;
        rcases hi with (hi | rfl);
        . let i : Fin (l.length) := ⟨i, by omega⟩;
          generalize ei' : (⟨i, hi'⟩ : Fin l'.length) = i';
          simpa [
            show l[i] = l'[i'] by simp [←ei', l'],
            show □^[(i + 1)]φ = □^[(i' + 1)]φ by simp [←ei'],
            show ∼□^[(i + 2)]φ = ∼□^[(i' + 2)]φ by simp [←ei']
          ] using @hl i;
        . simpa [l', hl_len, m] using hy₂;
      refine ⟨?_, by simpa [l'], ?_, hl'⟩;
      . apply List.nodup_iff_get_ne_get.mpr;
        rintro ⟨i, hi⟩ ⟨j, hj⟩ hij eij;
        replace hij : i < j := hij;
        apply Satisfies.not_def.mp $ Satisfies.and_def.mp (hl' ⟨i, hi⟩) |>.2;
        apply Satisfies.mdp ?_ $ eij ▸ Satisfies.and_def.mp (hl' ⟨j, hj⟩) |>.1;
        apply hM.realize;
        obtain ⟨c, hc, rfl⟩ := lt_iff_exists_add.mp hij;
        match c with
        | 0 => contradiction;
        | n + 1 =>
          suffices Hilbert.KTMk ⊢! □^[((i + 2) + n)]φ ➝ □^[(i + 2)]φ by
            simp_all [
              show (i + (n + 1)) = (i + n) + 1 by omega,
              show (i + 2) + n = (i + n) + 2 by omega
            ];
          apply reduce_box_in_CAnt!;
      . apply List.chain'_concat_of_not_nil (List.length_pos_iff_ne_nil.mp (by simp [hl_len])) |>.mpr;
        constructor;
        . assumption;
        . convert Rmy;
          trans l[l.length - 1]'(by simp [hl_len]);
          . apply List.getLast_eq_getElem;
          . simp [m, hl_len];
      . intro h;
        have : l[m] ⊧ □^[(m + 1)]φ ⋏ ∼□^[(m + 2)]φ ➝ ◇(□^[(m + 2)]φ ⋏ ◇(∼□^[(m + 2)]φ)) := by
          apply hM.realize;
          simp;
        replace : l[m] ⊧ ◇(□^[(m + 2)]φ ⋏ ◇(∼□^[(m + 2)]φ)) := this h;
        obtain ⟨y, hy₁, hy₂⟩ := Satisfies.dia_def.mp this;
        apply Satisfies.dia_def.mpr;
        use y;
        constructor;
        . assumption;
        . apply Satisfies.and_def.mpr;
          constructor;
          . exact Satisfies.and_def.mp hy₂ |>.1;
          . apply Satisfies.not_def.mpr;
            simpa using Satisfies.box_dn.not.mp $ Satisfies.not_def.mp $ Satisfies.dia_dual.mp $ Satisfies.and_def.mp hy₂ |>.2;
  apply Infinite.of_injective (β := ℕ+) (λ n => ⟨H n |>.choose, H n |>.choose_spec.1⟩);
  intro i j;
  simp only [Subtype.mk.injEq];
  contrapose!;
  suffices i ≠ j → (H i).choose.length ≠ (H j).choose.length by tauto;
  rw [H i |>.choose_spec.2.1, H j |>.choose_spec.2.1];
  simp;

end



end Hilbert.KTMk.Kripke

end LO.Modal
