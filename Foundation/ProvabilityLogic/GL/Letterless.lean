module

public import Foundation.ProvabilityLogic.GL.Basic
public import Foundation.ProvabilityLogic.Letterless
public import Foundation.ProvabilityLogic.Kripke.FiniteLineModel

/-!
# Letterless formulas in `GL` and its quasi-normal extensions

## References

- [Art86]
- [Boo94]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Formula Kripke Kripke.Model Kripke.Model.World LetterlessFormula

namespace LetterlessFormula

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} [Fintype M.World] [M.IsGL] {x : M.World}
         {A : LetterlessFormula}

lemma forces_lift_iff : x ⊩[M] A.lift ↔ x.rank ∈ spectrum A := by
  induction A using Formula.rec' generalizing x with
  | atom a => exact a.elim;
  | falsum => simp;
  | imp A B ihA ihB => simp [forces_imp, ihA, ihB, or_iff_not_imp_left];
  | box A ih =>
    suffices (∀ y, x ≺ y → y.rank ∈ spectrum A) ↔ ∀ i < x.rank, i ∈ spectrum A by
      simpa [forces_box, ih];
    constructor;
    . intro h i hi;
      obtain ⟨y, Rxy, rfl⟩ := exists_rel_rank_eq_of_lt hi;
      exact h y Rxy;
    . exact fun h y Rxy ↦ h _ (rank_lt_of_rel Rxy);

end LetterlessFormula

namespace Logic.GL

universe u

variable {α : Type u} {A : LetterlessFormula} {X : LetterlessFormulaSet}

lemma lift_mem_iff : A.lift ∈ (𝐆𝐋 : Logic α) ↔ spectrum A = Set.univ := by
  classical
  constructor;
  . intro h;
    apply Set.eq_univ_of_forall;
    intro n;
    simpa using forces_lift_iff.mp <| Logic.GL.sound (finiteLineModel n α) h (Fin.last n);
  . intro h;
    apply iff_valid_finite.mpr;
    intro _ _ M _ x;
    have : Fintype M.World := Fintype.ofFinite _;
    exact forces_lift_iff.mpr (by simp [h]);

lemma mem_iff_spectrum_eq_univ : A ∈ (𝐆𝐋 : Logic Empty) ↔ spectrum A = Set.univ := by
  simpa using lift_mem_iff (α := Empty) (A := A);

lemma exists_finset_of_mem_sumQuasiNormal {B : Formula α} (h : B ∈ 𝐆𝐋 +ᴸ X.lift) :
    ∃ Y : Finset LetterlessFormula, ↑Y ⊆ X ∧
      ∀ {κ : Type} [Nonempty κ] (M : Model κ α) [Fintype M.World] [M.IsGL] (x : M.World),
        (∀ C ∈ Y, x.rank ∈ spectrum C) → x ⊩[M] B := by
  classical
  induction h with
  | mem₁ h => exact ⟨∅, by simp, fun M _ _ x _ ↦ Logic.GL.sound M h x⟩;
  | mem₂ h =>
    obtain ⟨C, hC, rfl⟩ := h;
    exact ⟨{C}, by simpa, fun M _ _ x hx ↦ forces_lift_iff.mpr (hx C (by simp))⟩;
  | mdp _ _ ih₁ ih₂ =>
    obtain ⟨Y₁, hY₁, h₁⟩ := ih₁;
    obtain ⟨Y₂, hY₂, h₂⟩ := ih₂;
    use Y₁ ∪ Y₂;
    and_intros;
    . simp [hY₁, hY₂];
    . intro _ _ M _ _ x hx;
      exact h₁ M x (fun C hC ↦ hx C (by simp [hC])) (h₂ M x fun C hC ↦ hx C (by simp [hC]));
  | subst _ ih =>
    obtain ⟨Y, hY, h⟩ := ih;
    exact ⟨Y, hY, fun M _ _ x hx ↦ forces_subst.mp (h (M.subst _) x hx)⟩;

lemma spectrum_subset_of_lift_mem_sumQuasiNormal (h : A.lift ∈ (𝐆𝐋 : Logic α) +ᴸ X.lift) :
    X.spectrum ⊆ spectrum A := by
  obtain ⟨Y, hY, h⟩ := exists_finset_of_mem_sumQuasiNormal h;
  intro n hn;
  simpa using forces_lift_iff.mp <|
    h (finiteLineModel n α) (Fin.last n) fun C hC ↦ by
      simpa using LetterlessFormulaSet.mem_spectrum.mp hn C (hY hC);

theorem lift_mem_sumQuasiNormal_iff (h : (∃ B ∈ X, (spectrum B).Finite) ∨ (trace A).Finite) :
    A.lift ∈ (𝐆𝐋 : Logic α) +ᴸ X.lift ↔ X.spectrum ⊆ spectrum A := by
  classical
  constructor;
  . exact spectrum_subset_of_lift_mem_sumQuasiNormal;
  . intro hXA;
    obtain ⟨Y, hY, hA⟩ := exists_finset_of_spectrum_subset hXA h;
    apply sumQuasiNormal_of_conj (Γ := Y.image lift);
    . simp only [Finset.mem_image, forall_exists_index, and_imp];
      rintro _ C hC rfl;
      exact .mem₂ ⟨C, hY hC, rfl⟩;
    . apply iff_valid_finite.mpr;
      intro _ _ M _ x hx;
      have : Fintype M.World := Fintype.ofFinite _;
      have hx : ∀ C ∈ Y, x ⊩[M] C.lift :=
        fun C hC ↦ forces_conj.mp hx _ (Finset.mem_image_of_mem _ hC);
      exact forces_lift_iff.mpr <| hA _ fun C hC ↦ forces_lift_iff.mp (hx C hC);

variable {Y : LetterlessFormulaSet}

theorem sumQuasiNormal_subset_iff
    (h : (∃ B ∈ Y, (spectrum B).Finite) ∨ ∀ A ∈ X, (trace A).Finite) :
    ((𝐆𝐋 : Logic α) +ᴸ X.lift) ⊆ (𝐆𝐋 +ᴸ Y.lift) ↔ Y.spectrum ⊆ X.spectrum := by
  rw [sumQuasiNormal.subset_iff];
  constructor;
  . intro hs n hn;
    exact LetterlessFormulaSet.mem_spectrum.mpr fun A hA ↦
      spectrum_subset_of_lift_mem_sumQuasiNormal (hs ⟨A, hA, rfl⟩) hn;
  . rintro hs _ ⟨A, hA, rfl⟩;
    apply (lift_mem_sumQuasiNormal_iff (h.imp_right (· A hA))).mpr;
    exact fun n hn ↦ LetterlessFormulaSet.mem_spectrum.mp (hs hn) A hA;

theorem sumQuasiNormal_eq_iff
    (h : ((∃ B ∈ X, (spectrum B).Finite) ∧ ∃ B ∈ Y, (spectrum B).Finite) ∨
      ((∀ A ∈ X, (trace A).Finite) ∧ ∀ A ∈ Y, (trace A).Finite)) :
    ((𝐆𝐋 : Logic α) +ᴸ X.lift) = (𝐆𝐋 +ᴸ Y.lift) ↔ X.spectrum = Y.spectrum := by
  rw [Set.Subset.antisymm_iff, Set.Subset.antisymm_iff,
    sumQuasiNormal_subset_iff (h.imp And.right And.left),
    sumQuasiNormal_subset_iff (h.imp And.left And.right)];
  tauto;

end Logic.GL

end FFL.ProvabilityLogic

end
