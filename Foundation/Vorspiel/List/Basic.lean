module
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.List.GetD
public import Foundation.Vorspiel.Matrix

@[expose]
public section

namespace List

variable {l : List α}

variable {α : Type u} {β: Type v}

lemma getI_map_range [Inhabited α] (f : ℕ → α) (h : i < n) : ((List.range n).map f).getI i = f i := by
  simpa [h] using List.getI_eq_getElem ((List.range n).map f) (n := i) (by simpa using h)

def subsetSet (l : List α) (s : Set α) [DecidablePred s] : Bool :=
  l.foldr (fun a ih => s a && ih) true

def upper : List ℕ → ℕ
  | []      => 0
  | n :: ns => max (n + 1) ns.upper

@[simp] lemma upper_nil : upper [] = 0 := rfl

@[simp] lemma upper_cons (n : ℕ) (ns : List ℕ) : upper (n :: ns) = max (n + 1) ns.upper := rfl

lemma lt_upper (l : List ℕ) {n} (h : n ∈ l) : n < l.upper := by
  induction' l with n ns ih
  case nil => simp at h
  case cons m =>
    suffices m < n + 1 ∨ m < ns.upper by simpa
    rcases show m = n ∨ m ∈ ns by simpa using h with (rfl | h)
    · exact Or.inl (Nat.lt_succ_self _)
    · exact Or.inr (ih h)

section finset

variable [DecidableEq α] [DecidableEq β]

lemma toFinset_map {f : α → β} (l : List α) : (l.map f).toFinset = Finset.image f l.toFinset := by
  induction l <;> simp [*]

lemma toFinset_mono {l l' : List α} (h : l ⊆ l') : l.toFinset ⊆ l'.toFinset := by
  intro a; simp only [mem_toFinset]; intro ha; exact h ha

end finset

section sup

variable [SemilatticeSup α] [OrderBot α]

def sup : List α → α
  |      [] => ⊥
  | a :: as => a ⊔ as.sup

@[simp] lemma sup_nil : ([] : List α).sup = ⊥ := rfl

@[simp] lemma sup_cons (a : α) (as : List α) : (a :: as).sup = a ⊔ as.sup := rfl

lemma le_sup {a} {l : List α} : a ∈ l → a ≤ l.sup := by
  induction' l with a l ih
  · simp
  case cons _ b =>
    intro h
    rcases show b = a ∨ b ∈ l by simpa using h with (rfl | h)
    · simp
    · exact le_sup_of_le_right (ih h)

lemma sup_ofFn (f : Fin n → α) : (ofFn f).sup = Finset.sup Finset.univ f := by
  induction' n with n ih
  · simp
  · have h₁ : (Finset.univ : Finset (Fin (n + 1))) = insert 0 ((Finset.univ : Finset (Fin n)).image Fin.succ) := by
      ext i; simp
    have h₂ : Finset.sup Finset.univ (fun i ↦ f (Fin.succ i)) = Finset.sup {0}ᶜ f := by
      simpa [Function.comp] using Eq.symm <| Finset.sup_image (Finset.univ : Finset (Fin n)) Fin.succ f
    calc
      (ofFn f).sup = (f 0 ⊔ Finset.univ.sup fun i : Fin _ ↦ f i.succ) := by simp [ih]
      _            = f 0 ⊔ Finset.sup {0}ᶜ f                          := by rw [h₂]
      _            = Finset.univ.sup f                                := by rw [h₁, Finset.sup_insert]; simp

end sup

lemma ofFn_get_eq_map_cast {n} (g : α → β) (as : List α) {h} :
    ofFn (fun i => g (as.get (i.cast h)) : Fin n → β) = as.map g := by
  ext i b; simp
  by_cases hi : i < n
  · simp [hi, List.getElem?_eq_getElem (h ▸ hi)]
  · simp [hi, List.getElem?_eq_none (le_of_not_gt $ h ▸ hi)]

variable {m : Type _ → Type _} {α : Type _} {β : Type _} [Monad m]

lemma append_subset_append {l₁ l₂ l : List α} (h : l₁ ⊆ l₂) : l₁ ++ l ⊆ l₂ ++ l :=
  List.append_subset.mpr ⟨List.subset_append_of_subset_left _ h, subset_append_right l₂ l⟩

lemma subset_of_eq {l₁ l₂ : List α} (e : l₁ = l₂) : l₁ ⊆ l₂ := by simp [e]

section remove

def remove [DecidableEq α] (a : α) : List α → List α := List.filter (· ≠ a)

variable [DecidableEq α]

@[simp]
lemma remove_nil (a : α) : [].remove a = [] := by simp [List.remove]

@[simp]
lemma eq_remove_cons {l : List α} : (ψ :: l).remove ψ = l.remove ψ := by induction l <;> simp_all [List.remove];

@[simp]
lemma remove_singleton_of_ne {φ ψ : α} (h : φ ≠ ψ) : [φ].remove ψ = [φ] := by simp_all [List.remove];

lemma mem_remove_iff {l : List α} : b ∈ l.remove a ↔ b ∈ l ∧ b ≠ a := by
  simp [List.remove]

lemma mem_of_mem_remove {a b : α} {l : List α} (h : b ∈ l.remove a) : b ∈ l := by
  rw [mem_remove_iff] at h; exact h.1

@[simp] lemma remove_cons_self (l : List α) (a) :
  (a :: l).remove a = l.remove a := by simp [remove]

lemma remove_cons_of_ne (l : List α) {a b} (ne : a ≠ b) :
  (a :: l).remove b = a :: l.remove b := by simp_all [remove];

@[simp] lemma remove_subset (a) (l : List α) :
    l.remove a ⊆ l := by
  simp only [subset_def, mem_remove_iff, ne_eq, and_imp]
  intros; simp [*]

@[simp] lemma subset_cons_remove (a) (l : List α) :
    l ⊆ a :: l.remove a := by
  simp only [subset_def, mem_cons, mem_remove_iff, ne_eq]
  intro b; tauto

lemma remove_subset_remove (a) {l₁ l₂ : List α} (h : l₁ ⊆ l₂) :
    l₁.remove a ⊆ l₂.remove a := by
  simp only [subset_def, mem_remove_iff, ne_eq, and_imp]
  intros
  simpa [*] using h (by assumption)

lemma remove_cons_subset_cons_remove (a b) (l : List α) :
    (a :: l).remove b ⊆ a :: l.remove b := by
  intro x
  simp only [mem_remove_iff, mem_cons, ne_eq, and_imp]
  rintro (rfl | hx) nex <;> simp [*]

lemma remove_map_substet_map_remove [DecidableEq β] (f : α → β) (l : List α) (a) :
    (l.map f).remove (f a) ⊆ (l.remove a).map f := by
  simp only [subset_def, mem_remove_iff, mem_map, ne_eq, and_imp, forall_exists_index,
    forall_apply_eq_imp_iff₂]
  intro b hb neb;
  exact ⟨b, ⟨hb, by rintro rfl; exact neb rfl⟩, rfl⟩

end remove

@[elab_as_elim]
lemma induction_with_singleton
  {motive : List F → Prop}
  (hnil : motive [])
  (hsingle : ∀ a, motive [a])
  (hcons : ∀ a as, as ≠ [] → motive as → motive (a :: as)) : ∀ as, motive as := by
  intro as;
  induction as with
  | nil => exact hnil;
  | cons a as ih => cases as with
    | nil => exact hsingle a;
    | cons b bs => exact hcons a (b :: bs) (by simp) ih;

@[elab_as_elim]
def induction_with_singleton'
  {motive : List α → Sort*}
  (hnil : motive [])
  (hsingle : ∀ a, motive [a])
  (hcons : ∀ a b as, motive (b :: as) → motive (a :: b :: as)) : ∀ as, motive as
  |           [] => hnil
  |          [a] => hsingle a
  | a :: b :: as => hcons a b as (induction_with_singleton' hnil hsingle hcons (b :: as))

instance Nodup.finite [Finite α] : Finite {l : List α // l.Nodup} := by
  haveI : Fintype α := Fintype.ofFinite α
  let N := Fintype.card α + 1
  have : Fintype ((i : Fin N) × Vector α i) := Sigma.instFintype
  let f : {l : List α // l.Nodup} → ((i : Fin N) × Vector α i) := fun l ↦
    ⟨⟨l.val.length, Nat.lt_add_one_of_le <| l.prop.length_le_card⟩, l, by simp⟩
  have : Function.Injective f := by
    intro ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ H
    simpa [f] using congrArg (fun p ↦ p.2.val) H
  exact Finite.of_injective f this

section suffix

lemma suffix_of_cons_suffix {l₁ l₂ : List α} {a} : a :: l₁ <:+ l₂ → l₁ <:+ l₂ := by rintro ⟨l₂, rfl⟩; exact ⟨l₂ ++ [a], by simp⟩

lemma suffix_cons_of {l₁ l₂ : List α} {a} : l₁ <:+ l₂ → l₁ <:+ a :: l₂ := fun h ↦ suffix_cons_iff.mpr <| Or.inr h

lemma exists_of_not_suffix (l₁ l₂ : List α) : ¬l₁ <:+ l₂ → ∃ l a, a :: l <:+ l₁ ∧ l <:+ l₂ ∧ ¬a :: l <:+ l₂ :=
  match l₁ with
  |      [] => by simp
  | a :: l₁ => by
    intro h
    by_cases h₁₂ : l₁ <:+ l₂
    · exact ⟨l₁, a, by simp_all⟩
    · rcases exists_of_not_suffix l₁ l₂ h₁₂ with ⟨l, b, hb, hll₂, nh⟩
      exact ⟨l, b, suffix_cons_of hb, hll₂, nh⟩

lemma IsSuffix.eq_or_cons_suffix : l₁ <:+ l₂ → l₁ = l₂ ∨ ∃ a, a :: l₁ <:+ l₂ := by
  rintro ⟨l, rfl⟩
  rcases eq_nil_or_concat' l with (rfl | ⟨l, a, rfl⟩)
  · simp
  · right; exact ⟨a, l, by simp⟩

lemma suffix_trichotomy {l₁ l₂ : List α} (h₁₂ : ¬l₁ <:+ l₂) (h₂₁ : ¬l₂ <:+ l₁) : ∃ l a b, a ≠ b ∧ a :: l <:+ l₁ ∧ b :: l <:+ l₂ := by
  rcases exists_of_not_suffix _ _ h₁₂ with ⟨l, a, ha, hkl, _⟩
  have : ∃ b, b :: l <:+ l₂ := by
    rcases hkl.eq_or_cons_suffix with (rfl | h)
    · have : l <:+ l₁ := suffix_of_cons_suffix ha
      contradiction
    exact h
  rcases this with ⟨b, hb⟩
  exact ⟨l, a, b, by rintro rfl; contradiction, ha, hb⟩

end suffix

namespace Vector

variable {α : Type*}

lemma get_mk_eq_get {n} (l : List α) (h : l.length = n) (i : Fin n) : List.Vector.get (⟨l, h⟩ : List.Vector α n) i = l.get (i.cast h.symm) := rfl

lemma get_one {α : Type*} {n} (v : Vector α (n + 2)) : v.get 1 = v.tail.head := by
  rw [←Vector.get_zero, Vector.get_tail_succ]; rfl

lemma ofFn_vecCons (a : α) (v : Fin n → α) :
    ofFn (a :> v) = a ::ᵥ ofFn v := by
  ext i; cases i using Fin.cases <;> simp

lemma cons_get (a : α) (v : List.Vector α k) : (a ::ᵥ v).get = a :> v.get := by
  ext i; cases i using Fin.cases <;> simp

end Vector



lemma exists_of_not_nil (hl : l ≠ []) : ∃ a, a ∈ l := by
  match l with
  | [] => tauto;
  | a :: l => use a; simp only [mem_cons, true_or];

lemma iff_nil_forall : (l = []) ↔ (∀ a ∈ l, a ∈ []) := by
  constructor;
  . intro h;
    subst h;
    tauto;
  . contrapose!;
    rintro h;
    obtain ⟨a, ha⟩ := exists_of_not_nil h;
    use a;
    tauto;

/-- getElem version of `List.nodup_iff_getElem?_ne_getElem?` -/
lemma nodup_iff_get_ne_get : l.Nodup ↔ ∀ i j : Fin l.length, i < j → l[i] ≠ l[j] := by
  apply Iff.trans nodup_iff_getElem?_ne_getElem?;
  constructor;
  . rintro h ⟨i, _⟩ ⟨j, hj⟩ hij;
    have := h i j (by omega) hj;
    simp_all;
  . rintro h i j hij hj;
    rw [getElem?_eq_getElem, getElem?_eq_getElem];
    simpa [Option.some.injEq] using h ⟨i, by omega⟩ ⟨j, by omega⟩ hij;


lemma Nodup.infinite_of_infinite : Infinite {l : List α // l.Nodup} → Infinite α := by
  contrapose!;
  intro _;
  exact List.Nodup.finite;

lemma exists_of_range (h : a ∈ List.map f (List.range n)) : ∃ i < n, a = f i := by
  obtain ⟨i, ⟨hi, rfl⟩⟩ := List.exists_of_mem_map h;
  use i;
  constructor;
  . simpa using hi;
  . simp;

lemma single_suffix_uniq {l : List α} (ha : [a] <:+ l) (hb : [b] <:+ l) : a = b := by
  rcases ha with ⟨la, rfl⟩
  rcases hb with ⟨lb, e⟩
  exact Eq.symm (List.concat_inj.mp <| by { simpa using e }).2

end List

end
