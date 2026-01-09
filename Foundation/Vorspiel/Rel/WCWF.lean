module
import Foundation.Vorspiel.Rel.CWF
import Mathlib.Data.Fintype.Pigeonhole

section

abbrev WeaklyConverseWellFounded {α} (rel : Rel α α) := ConverseWellFounded (rel.IrreflGen)

@[mk_iff]
class IsWeaklyConverseWellFounded (α) (rel : Rel α α) where wcwf : WeaklyConverseWellFounded rel

end


section

variable {α : Type*} {rel : α → α → Prop}

lemma dependent_choice (h : ∃ s : Set α, s.Nonempty ∧ ∀ a ∈ s, ∃ b ∈ s, rel a b)
  : ∃ f : ℕ → α, ∀ x, rel (f x) (f (x + 1)) := by
  obtain ⟨s, ⟨x, hx⟩, h'⟩ := h;
  choose! f hfs hR using h';
  use fun n ↦ f^[n] x;
  intro n;
  simp only [Function.iterate_succ'];
  refine hR (f^[n] x) ?a;
  induction n with
  | zero => simpa;
  | succ n ih => simp only [Function.iterate_succ']; apply hfs _ ih;

lemma Finite.exists_ne_map_eq_of_infinite_lt {α β} [LinearOrder α] [Infinite α] [Finite β] (f : α → β)
  : ∃ x y : α, (x < y) ∧ f x = f y
  := by
    obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite f;
    rcases lt_trichotomy i j with (hij | _ | hij);
    . use i, j;
    . contradiction;
    . use j, i; simp [hij, e];


lemma antisymm_of_weaklyConverseWellFounded : WeaklyConverseWellFounded rel → AntiSymmetric rel := by
  dsimp [AntiSymmetric];
  contrapose!;
  rintro ⟨x, y, Rxy, Ryz, hxy⟩;
  apply ConverseWellFounded.iff_has_max.not.mpr;
  push_neg;
  use {x, y};
  constructor;
  . simp;
  . intro z hz;
    by_cases z = x;
    . use y; simp_all [Rel.IrreflGen];
    . use x; simp_all [Rel.IrreflGen];

instance [IsWeaklyConverseWellFounded _ rel] : IsAntisymm _ rel := ⟨by
  apply antisymm_of_weaklyConverseWellFounded;
  apply isWeaklyConverseWellFounded_iff _ _ |>.mp;
  assumption;
⟩


lemma weaklyConverseWellFounded_of_finite_trans_antisymm (hFin : Finite α) (R_trans : Transitive rel)
  : AntiSymmetric rel → WeaklyConverseWellFounded rel := by
    dsimp [AntiSymmetric]
    contrapose!;
    intro hWCWF;
    replace hWCWF := ConverseWellFounded.iff_has_max.not.mp hWCWF;
    push_neg at hWCWF;
    obtain ⟨f, hf⟩ := dependent_choice hWCWF; clear hWCWF;
    dsimp [Rel.IrreflGen] at hf;

    obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite_lt f;
    use (f i), (f (i + 1));
    have ⟨hi₁, hi₂⟩ := hf i;
    refine ⟨(by assumption), ?_, (by assumption)⟩;

    have : i + 1 < j := lt_iff_le_and_ne.mpr ⟨by omega, by aesop⟩;
    have H : ∀ i j, i < j → rel (f i) (f j) := by
      intro i j hij
      induction hij with
      | refl => exact hf i |>.1;
      | step _ ih => exact R_trans ih $ hf _ |>.1;
    have := H (i + 1) j this;
    simpa [e];

instance [Finite α] [IsTrans _ rel] [IsAntisymm _ rel] : IsWeaklyConverseWellFounded α rel := ⟨by
  apply weaklyConverseWellFounded_of_finite_trans_antisymm;
  . assumption;
  . exact IsTrans.trans;
  . exact IsAntisymm.antisymm;
⟩

end
