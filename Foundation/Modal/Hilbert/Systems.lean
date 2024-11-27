import Foundation.Modal.Hilbert.Preliminaries
import Foundation.Modal.System.Preliminaries

namespace LO.Modal.Hilbert

protected abbrev K (α) : Hilbert α := ⟨𝗞, ⟮Nec⟯⟩
instance : (Hilbert.K α).IsNormal where


protected abbrev ExtK {α} (Ax : Theory α) : Hilbert α := ⟨𝗞 ∪ Ax, ⟮Nec⟯⟩
instance : (Hilbert.ExtK Ax).IsNormal where
  has_axiomK := by simp;

namespace ExtK

variable {α} {Ax : Theory α}

lemma K_is_extK_of_empty : (Hilbert.K α) = (Hilbert.ExtK ∅) := by aesop;

lemma K_is_extK_of_AxiomK : (Hilbert.K α) = (Hilbert.ExtK 𝗞) := by aesop;

lemma def_ax : (Hilbert.ExtK Ax).axioms = (𝗞 ∪ Ax) := rfl

lemma maxm! (h : φ ∈ Ax) : (Hilbert.ExtK Ax) ⊢! φ := ⟨Deduction.maxm (by simp [Hilbert.ExtK]; tauto)⟩

@[simp]
lemma weakerThan : (Hilbert.K α) ≤ₛ (Hilbert.ExtK Ax) := normal_weakerThan_of_subset $ by
  simp_all only [Set.subset_union_left];

end ExtK


protected abbrev KT (α) : Hilbert α := Hilbert.ExtK $ 𝗧
instance : System.KT (Hilbert.KT α) where
  T _ := Deduction.maxm $ by aesop;

protected abbrev KB (α) : Hilbert α := Hilbert.ExtK $ 𝗕
instance : System.KB (Hilbert.KB α) where
  B _ := Deduction.maxm $ by aesop;

protected abbrev KD (α) : Hilbert α := Hilbert.ExtK $ 𝗗
instance : System.KD (Hilbert.KD α) where
  D _ := Deduction.maxm $ by aesop;

protected abbrev KP (α) : Hilbert α := Hilbert.ExtK $ 𝗣
instance : System.KP (Hilbert.KP α) where
  P := Deduction.maxm $ by aesop;

protected abbrev KTB (α) : Hilbert α := Hilbert.ExtK $ 𝗧 ∪ 𝗕

protected abbrev K4 (α) : Hilbert α := Hilbert.ExtK $ 𝟰
instance : System.K4 (Hilbert.K4 α) where
  Four _ := Deduction.maxm $ by aesop;

protected abbrev K5 (α) : Hilbert α := Hilbert.ExtK $ 𝟱
instance : System.K5 (Hilbert.K5 α) where
  Five _ := Deduction.maxm $ by aesop;


protected abbrev ExtS4 {α} (Ax : Theory α) : Hilbert α := Hilbert.ExtK (𝗧 ∪ 𝟰 ∪ Ax)

namespace ExtS4

instance : System.S4 (Hilbert.ExtS4 Ax) where
  T _ := Deduction.maxm $ by aesop;
  Four _ := Deduction.maxm $ by aesop;

@[simp] lemma def_ax : (Hilbert.ExtS4 Ax).axioms = (𝗞 ∪ 𝗧 ∪ 𝟰 ∪ Ax) := by aesop;

end ExtS4

protected abbrev S4 (α) : Hilbert α := Hilbert.ExtS4 $ ∅

protected abbrev S4Dot2 (α) : Hilbert α := Hilbert.ExtS4 $ .𝟮
instance : System.S4Dot2 (Hilbert.S4Dot2 α) where
  Dot2 _ := Deduction.maxm $ by aesop

protected abbrev S4Dot3 (α) : Hilbert α := Hilbert.ExtS4 $ .𝟯
instance : System.S4Dot3 (Hilbert.S4Dot3 α) where
  Dot3 _ _:= Deduction.maxm $ by aesop;

protected abbrev S4Grz (α) : Hilbert α := Hilbert.ExtS4 $ 𝗚𝗿𝘇

protected abbrev KT4B (α) : Hilbert α := Hilbert.ExtS4 $ 𝗕


protected abbrev S5 (α) : Hilbert α := Hilbert.ExtK $ 𝗧 ∪ 𝟱
instance : System.S5 (Hilbert.S5 α) where
  T _ := Deduction.maxm $ by aesop;
  Five _ := Deduction.maxm $ by aesop;

protected abbrev Triv (α) : Hilbert α := Hilbert.ExtK $ 𝗧 ∪ 𝗧𝗰
instance : System.Triv (Hilbert.Triv α) where
  T _ := Deduction.maxm $ by aesop;
  Tc _ := Deduction.maxm $ by aesop;

protected abbrev Ver (α) : Hilbert α := Hilbert.ExtK $ 𝗩𝗲𝗿
instance : System.Ver (Hilbert.Ver α) where
  Ver _ := Deduction.maxm $ by aesop;

protected abbrev GL (α) : Hilbert α := Hilbert.ExtK $ 𝗟
instance : System.GL (Hilbert.GL α) where
  L _ := Deduction.maxm $ by aesop;

protected abbrev Grz (α) : Hilbert α := Hilbert.ExtK $ 𝗚𝗿𝘇
instance : System.Grz (Hilbert.Grz α) where
  Grz _ := Deduction.maxm $ by aesop;

/--
  Solovey's Provability Logic of True Arithmetic.
  Remark necessitation is *not* permitted.
-/
protected abbrev GLS (α) : Hilbert α := ⟨(Hilbert.GL α).theorems ∪ 𝗧, ∅⟩
instance : System.HasAxiomK (Hilbert.GLS α) where
  K _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) $ by simp [Hilbert.theorems, System.theory, System.axiomK!];
instance : System.HasAxiomL (Hilbert.GLS α) where
  L _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) $ by simp [Hilbert.theorems, System.theory, System.axiomK!];
instance : System.HasAxiomT (Hilbert.GLS α) where
  T _ := Deduction.maxm $ by aesop;

/-- Logic of Pure Necessitation -/
protected abbrev N (α) : Hilbert α := ⟨∅, ⟮Nec⟯⟩
instance : (Hilbert.N α).HasNecOnly where


end LO.Modal.Hilbert
