import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.List
import Mathlib.Data.Fintype.EquivFin

namespace List

section

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

end

/--
```
  ChainI R x y [a, b, c, d] ↔ x = a ∧ R a b ∧ R b c ∧ R c d ∧ d = y
```
 -/
inductive ChainI {α : Type*} (R : α → α → Prop) : α → α → List α → Prop
  | singleton (a : α) : ChainI R a a [a]
  | cons {a b c : α} {l : List α} : R a b → ChainI R b c l → ChainI R a c (a :: l)

attribute [simp] ChainI.singleton

namespace ChainI

variable {α : Type*} {R : α → α → Prop}

@[simp] lemma not_nil (a b) : ¬ChainI R a b [] := by rintro ⟨⟩

lemma not_mem_of_rel (IR : Irreflexive R) (TR : Transitive R) {a b x l} : ChainI R a b l → R x a → x ∉ l := by
  rintro (_ | _)
  case singleton => simp; intro hR; rintro rfl; exact IR _ hR
  case cons a' l Raa' h =>
    intro Rxa
    have : x ≠ a := by rintro rfl; exact IR _ Rxa
    have : x ∉ l :=
      have : R x a' := TR Rxa Raa'
      not_mem_of_rel IR TR h this
    simp_all

lemma nodup (IR : Irreflexive R) (TR : Transitive R) {a b l} : ChainI R a b l → l.Nodup :=
  match l with
  |      [] => by simp
  | a' :: l => by
    rintro (_ | _)
    case singleton => simp
    case cons a' Raa' h =>
      have ih : l.Nodup := nodup IR TR h
      have notin :a ∉ l := not_mem_of_rel IR TR h Raa'
      simp_all

lemma finite_of_irreflexive_of_transitive [Finite α] (IR : Irreflexive R) (TR : Transitive R) (a b : α) :
    Finite {l : List α // l.ChainI R a b} := by
  haveI : Fintype α := Fintype.ofFinite α
  let f : {l : List α // l.ChainI R a b} → {l : List α // l.Nodup} := fun l ↦ ⟨l, l.prop.nodup IR TR⟩
  have : Function.Injective f := by intro ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩; simp [f]
  exact Finite.of_injective f this

end ChainI

end List
