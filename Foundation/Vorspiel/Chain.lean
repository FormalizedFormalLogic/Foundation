import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.List
import Mathlib.Data.Fintype.EquivFin

namespace List

variable {l l₁ l₂ : List α}
variable {R : α → α → Prop}

lemma Chain'.nodup_of_trans_irreflex [IsTrans _ R] [IsIrrefl _ R] (h_chain : l.Chain' R) : l.Nodup := by
  by_contra hC;
  replace ⟨d, hC⟩ := List.exists_duplicate_iff_not_nodup.mpr hC;
  have := List.duplicate_iff_sublist.mp hC;
  have := @List.Chain'.sublist α R [d, d] l ⟨IsTrans.trans⟩ h_chain this;
  simp at this;
  exact IsIrrefl.irrefl d this;

instance finiteNodupList [DecidableEq α] [Finite α] : Finite { l : List α // l.Nodup } := @fintypeNodupList α (Fintype.ofFinite α) |>.finite

lemma chains_finite [DecidableEq α] [Finite α] [IsTrans _ R] [IsIrrefl _ R] : Finite { l : List α // l.Chain' R } := by
  apply @Finite.of_injective { l : List α // l.Chain' R } { l : List α // l.Nodup } _ ?f;
  case f => intro ⟨l, hl⟩; refine ⟨l, List.Chain'.nodup_of_trans_irreflex hl⟩;
  simp [Function.Injective];

end List
