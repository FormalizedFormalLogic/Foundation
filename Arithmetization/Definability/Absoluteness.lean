import Arithmetization.Definability.BoundedBoldface

noncomputable section

namespace LO.FirstOrder.Arith

open LO.Arith

lemma nat_modelsWithParam_iff_models_substs {v : Fin k → ℕ} {p : Semisentence ℒₒᵣ k} :
    ℕ ⊧ₘ[v] p ↔ ℕ ⊧ₘ (Rew.substs (fun i ↦ Semiterm.Operator.numeral ℒₒᵣ (v i)) |>.hom p) := by
  simp [models_iff]

variable (M : Type*) [ORingStruc M] [M ⊧ₘ* 𝐏𝐀⁻]

lemma modelsWithParam_iff_models_substs {v : Fin k → ℕ} {p : Semisentence ℒₒᵣ k} :
    M ⊧ₘ[fun i ↦ v i] p ↔ M ⊧ₘ (Rew.substs (fun i ↦ Semiterm.Operator.numeral ℒₒᵣ (v i)) |>.hom p) := by
  simp [models_iff, numeral_eq_natCast]

lemma shigmaZero_absolute {k} (p : 𝚺₀.Semisentence k) (v : Fin k → ℕ) :
    ℕ ⊧ₘ[v] p.val ↔ M ⊧ₘ[fun i ↦ (v i)] p.val :=
  ⟨by simp [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]; exact nat_extention_sigmaOne M (by simp),
   by simp [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]; exact nat_extention_piOne M (by simp)⟩

lemma Defined.shigmaZero_absolute {k} {R : (Fin k → ℕ) → Prop} {R' : (Fin k → M) → Prop} {p : 𝚺₀.Semisentence k}
    (hR : 𝚺₀.Defined R p) (hR' : 𝚺₀.Defined R' p) (v : Fin k → ℕ) :
    R v ↔ R' (fun i ↦ (v i : M)) := by
  simpa [hR.iff, hR'.iff] using Arith.shigmaZero_absolute M p v

lemma DefinedFunction.shigmaZero_absolute_func {k} {f : (Fin k → ℕ) → ℕ} {f' : (Fin k → M) → M} {p : 𝚺₀.Semisentence (k + 1)}
    (hf : 𝚺₀.DefinedFunction f p) (hf' : 𝚺₀.DefinedFunction f' p) (v : Fin k → ℕ) :
    (f v : M) = f' (fun i ↦ (v i)) := by
  simpa using Defined.shigmaZero_absolute M hf hf' (f v :> v)

lemma sigmaOne_upward_absolute {k} (p : 𝚺₁.Semisentence k) (v : Fin k → ℕ) :
    ℕ ⊧ₘ[v] p.val → M ⊧ₘ[fun i ↦ (v i)] p.val := by
  simp [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]
  exact nat_extention_sigmaOne M (by simp)

lemma piOne_downward_absolute {k} (p : 𝚷₁.Semisentence k) (v : Fin k → ℕ) :
    M ⊧ₘ[fun i ↦ (v i)] p.val → ℕ ⊧ₘ[v] p.val := by
  simp [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]
  exact nat_extention_piOne M (by simp)

lemma deltaOne_absolute {k} (p : 𝚫₁.Semisentence k)
    (properNat : p.ProperOn ℕ) (proper : p.ProperOn M) (v : Fin k → ℕ) :
    ℕ ⊧ₘ[v] p.val ↔ M ⊧ₘ[fun i ↦ (v i)] p.val :=
  ⟨by simpa [HierarchySymbol.Semiformula.val_sigma] using sigmaOne_upward_absolute M p.sigma v,
   by simpa [proper.iff', properNat.iff'] using piOne_downward_absolute M p.pi v⟩

lemma Defined.shigmaOne_absolute {k} {R : (Fin k → ℕ) → Prop} {R' : (Fin k → M) → Prop} {p : 𝚫₁.Semisentence k}
    (hR : 𝚫₁.Defined R p) (hR' : 𝚫₁.Defined R' p) (v : Fin k → ℕ) :
    R v ↔ R' (fun i ↦ (v i : M)) := by
  simpa [hR.df.iff, hR'.df.iff] using deltaOne_absolute M p hR.proper hR'.proper v

lemma DefinedFunction.shigmaOne_absolute_func {k} {f : (Fin k → ℕ) → ℕ} {f' : (Fin k → M) → M} {p : 𝚺₁.Semisentence (k + 1)}
    (hf : 𝚺₁.DefinedFunction f p) (hf' : 𝚺₁.DefinedFunction f' p) (v : Fin k → ℕ) :
    (f v : M) = f' (fun i ↦ (v i)) := by
  simpa using Defined.shigmaOne_absolute M hf.graph_delta hf'.graph_delta (f v :> v)

end LO.FirstOrder.Arith

end
