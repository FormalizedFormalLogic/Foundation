import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.List

namespace List

variable {l l₁ l₂ : List α}
variable {R : α → α → Prop}

lemma Chain'.nodup_of_trans_irreflex (R_trans : Transitive R) (R_irrefl : Irreflexive R) (h_chain : l.Chain' R) : l.Nodup := by
  by_contra hC;
  replace ⟨d, hC⟩ := List.exists_duplicate_iff_not_nodup.mpr hC;
  have := List.duplicate_iff_sublist.mp hC;
  have := @List.Chain'.sublist α R [d, d] l ⟨by aesop⟩ h_chain this;
  simp at this;
  exact R_irrefl d this;

instance finiteNodupList [DecidableEq α] [Finite α] : Finite { l : List α // l.Nodup } := @fintypeNodupList α _ (Fintype.ofFinite α) |>.finite

lemma chains_finite [DecidableEq α] [Finite α] (R_trans : Transitive R) (R_irrefl : Irreflexive R) : Finite { l : List α // l.Chain' R } := by
  apply @Finite.of_injective { l : List α // l.Chain' R } { l : List α // l.Nodup } _ ?f;
  case f => intro ⟨l, hl⟩; refine ⟨l, List.Chain'.nodup_of_trans_irreflex R_trans R_irrefl hl⟩;
  simp [Function.Injective];

end List
