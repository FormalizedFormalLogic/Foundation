import Foundation.Vorspiel.Vorspiel

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

namespace ChainI

variable {α : Type*} {R : α → α → Prop}

@[simp] lemma not_nil (a b) : ¬ChainI R a b [] := by rintro ⟨⟩

@[simp] lemma singletob_iff (a b x) : ChainI R a b [x] ↔ a = x ∧ x = b := by
  constructor
  · rintro ⟨⟩ <;> simp_all
  · rintro ⟨rfl, rfl⟩; simp [ChainI.singleton]

attribute [simp] ChainI.singleton

lemma cons_iff : ChainI R a b (c :: l) ↔ a = c ∧ ChainI R c b (c :: l) := by
  constructor
  · rintro (_ | _)
    · simp
    case cons a' hR h =>
    simp [h.cons hR]
  · rintro ⟨rfl, _⟩
    assumption

lemma cons_cons_iff :
    ChainI R a b (c :: d ::  l) ↔ a = c ∧ R c d ∧ ChainI R d b (d :: l) := by
  constructor
  · rintro ⟨⟩
    case cons d' hR hC =>
      rcases cons_iff.mp hC with ⟨rfl, hC⟩
      simp_all
  · rintro ⟨rfl, hR, hC⟩
    exact hC.cons hR

lemma not_mem_of_rel (IR : Irreflexive R) (TR : Transitive R) {a b x : α} {l : List α} : ChainI R a b l → R x a → x ∉ l := by
  match l with
  |      [] => simp
  | a' :: l =>
    rintro (_ | _)
    case singleton => simp; intro hR; rintro rfl; exact IR _ hR
    case cons a' Raa' h =>
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

lemma cons_eq {l} : ChainI R a b (a' :: l) → a = a' := by
  rintro ⟨⟩ <;> simp

lemma eq_of {l} (h₁ : ChainI R a₁ b₁ l) (h₂ : ChainI R a₂ b₂ l) : a₁ = a₂ ∧ b₁ = b₂ := by
  match l with
  |          [] => simp_all
  |         [i] =>
    rcases h₁; rcases h₂
    · simp
    · simp_all
    · simp_all
  | j :: i :: l =>
    rcases h₁; rcases h₂
    case cons h₁ _ _ h₂ =>
    simp [(eq_of h₁ h₂).2]

lemma prec_exists_of_ne {l} (h : ChainI R a b l) :
    a ≠ b → ∃ l' c, R a c ∧ l = a :: c :: l' ∧ ChainI R c b (c :: l') := by
  intro _
  match l with
  |            [] => rcases h
  |          [b'] => rcases h <;> simp_all
  | b' :: c :: l' =>
    rcases h
    case cons c' hR h =>
      rcases show c' = c from cons_eq h
      exact ⟨l', _, hR, rfl, h⟩

lemma tail_exists (h : ChainI R a b l) : ∃ l', l = a :: l' := by
  match l with
  |            [] => rcases h
  |          [b'] => rcases h <;> simp_all
  | b' :: c :: l' =>
    rcases h
    case cons c' hR h =>
      rcases show c' = c from cons_eq h
      exact ⟨_, rfl⟩

lemma append_singleton_append_iff {l₁ l₂ : List α} :
    ChainI R a b (l₁ ++ c :: l₂) ↔ ChainI R a c (l₁ ++ [c]) ∧ ChainI R c b (c :: l₂) := by
  match l₁ with
  |           [] => simp [cons_iff (a := a)]
  |          [x] => simp [cons_cons_iff, and_assoc]
  | x :: y :: l₁ =>
    have ih : ChainI R y b (y :: (l₁ ++ c :: l₂)) ↔ ChainI R y c (y :: (l₁ ++ [c])) ∧ ChainI R c b (c :: l₂) :=
      append_singleton_append_iff (l₁ := y :: l₁) (l₂ := l₂) (c := c) (a := y) (b := b)
    simp [cons_cons_iff, ih, and_assoc]

lemma rel_of_infix (hC : ChainI R a b l) (x y) (h : [x, y] <:+: l) : R x y := by
  rcases h with ⟨l₁, l₂, rfl⟩
  have : ChainI R x b (x :: y :: l₂) := by
    simp [append_singleton_append_iff (l₂ := y :: l₂)] at hC
    exact hC.2
  exact cons_cons_iff.mp this |>.2.1

lemma infix_of_suffix_of (h : ChainI R a b l₁) : x :: l₁ <:+ l₂ → [x, a] <:+: l₂ := by
  intro hx
  rcases h.tail_exists with ⟨l₁', rfl⟩
  exact List.infix_iff_prefix_suffix.mpr ⟨x :: a :: l₁', by simp, hx⟩

lemma prefix_suffix : ChainI R a b l → [a] <+: l ∧ [b] <:+ l := by
  match l with
  |           [] => simp
  |          [x] => simp; rintro rfl rfl; simp
  | x :: y :: l₁ =>
    rintro ⟨⟩
    case cons z hR h =>
      simpa using List.suffix_cons_of h.prefix_suffix.2

end ChainI

lemma single_suffix_uniq {l : List α} (ha : [a] <:+ l) (hb : [b] <:+ l) : a = b := by
  rcases ha with ⟨la, rfl⟩
  rcases hb with ⟨lb, e⟩
  exact Eq.symm (List.concat_inj.mp <| by { simpa using e }).2

end List
