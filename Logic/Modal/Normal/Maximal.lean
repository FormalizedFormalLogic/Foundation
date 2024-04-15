import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Deduction

/-!
  # Maximality of `𝐓𝐫𝐢𝐯` and `𝐕𝐞𝐫`

  `𝐓𝐫𝐢𝐯` and `𝐕𝐞𝐫` are maximal in normal modal logic.
-/

namespace LO.Modal.Normal

variable {α} [DecidableEq α]

namespace Formula

def TrivTranslation : Formula α → Formula α
  | atom a => atom a
  | box p => p.TrivTranslation
  | ⊥ => ⊥
  | p ⟶ q => (p.TrivTranslation) ⟶ (q.TrivTranslation)
  | p ⋏ q => (p.TrivTranslation) ⋏ (q.TrivTranslation)
  | p ⋎ q => (p.TrivTranslation) ⋎ (q.TrivTranslation)

postfix:75 "ᵀ" => TrivTranslation

@[simp] lemma TrivTranslation.degree_zero : pᵀ.degree = 0 := by induction p <;> simp [TrivTranslation, degree, *];

def TrivTranslation.toPropFormula (p : Formula α) : LO.Propositional.Intuitionistic.Formula α := pᵀ.toPropFormula (by simp)

@[simp]
def VerTranslation : Formula α → Formula α
  | atom a => atom a
  | box _ => ⊤
  | ⊥ => ⊥
  | p ⟶ q => (p.VerTranslation) ⟶ (q.VerTranslation)
  | p ⋏ q => (p.VerTranslation) ⋏ (q.VerTranslation)
  | p ⋎ q => (p.VerTranslation) ⋎ (q.VerTranslation)

postfix:75 "ⱽ" => VerTranslation

@[simp] lemma VerTranslation.degree_zero : pⱽ.degree = 0 := by induction p <;> simp [VerTranslation, degree, *];

def VerTranslation.toPropFormula (p : Formula α) : LO.Propositional.Intuitionistic.Formula α := pⱽ.toPropFormula (by simp)

end Formula

open Hilbert

variable {Λ : AxiomSet α}

def Deduction.ofTrivSubset (_ : 𝐓𝐫𝐢𝐯 ⊆ Λ) : (Hilbert.Triv (Deduction (Λ : AxiomSet α))) where
  K _ _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  T _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  Tc _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);

def Deduction.ofVerSubset (_ : 𝐕𝐞𝐫 ⊆ Λ) : (Hilbert.Ver (Deduction (Λ : AxiomSet α))) where
  K _ _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  Verum _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);

lemma deducible_iff_trivTranslation (hTriv : 𝐓𝐫𝐢𝐯 ⊆ Λ) : Γ ⊢ᴹ[Λ]! p ⟷ pᵀ := by
  have := Deduction.ofTrivSubset hTriv;
  induction p using Formula.rec' with
  | hbox p ih => exact iff_trans'! (iff_symm'! $ boxtriv!) ih;
  | hatom _ => apply iff_id!
  | hfalsum => apply iff_id!
  | himp _ _ ih₁ ih₂ => exact imp_iff'! ih₁ ih₂;
  | hand _ _ ih₁ ih₂ => exact conj_iff'! ih₁ ih₂;
  | hor _ _ ih₁ ih₂ => exact disj_iff'! ih₁ ih₂

lemma deducible_iff_verTranslation (hVer : 𝐕𝐞𝐫 ⊆ Λ) : Γ ⊢ᴹ[Λ]! p ⟷ pⱽ := by
  have := Deduction.ofVerSubset hVer;
  induction p using Formula.rec' with
  | hbox =>
    apply iff_intro'!;
    . exact imply₁'! verum!
    . exact imply₁'! boxarbitary!;
  | hatom _ => apply iff_id!
  | hfalsum => apply iff_id!
  | himp _ _ ih₁ ih₂ => exact imp_iff'! ih₁ ih₂;
  | hand _ _ ih₁ ih₂ => exact conj_iff'! ih₁ ih₂;
  | hor _ _ ih₁ ih₂ => exact disj_iff'! ih₁ ih₂

end LO.Modal.Normal
