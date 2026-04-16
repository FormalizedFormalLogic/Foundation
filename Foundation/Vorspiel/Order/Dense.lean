module

public import Mathlib.Order.PFilter
public import Mathlib.Data.Set.Countable

@[expose] public section

namespace Nat

lemma monotone_of_succ_monotone {r : ℕ → ℕ → Prop} (rfx : Reflexive r) (tr : IsTrans ℕ r)
    (succ : ∀ n, r n (n + 1)) : n ≤ m → r n m := by
  revert n m
  suffices ∀ n d, r n (n + d) by
    intro n m hnm
    have := this n (m - n)
    grind
  intro n d
  induction d
  case zero => simp [rfx n]
  case succ d ih =>
    simpa using tr.trans _ _ _ ih (succ (n + d))

end Nat

namespace DirectedOn

variable {α : Type*} {r : α → α → Prop}

private lemma vector_le (tr : IsTrans α r) {s : Set α} (hs : s.Nonempty) (h : DirectedOn r s) (v : Fin n → α) (hv : ∀ i, v i ∈ s) :
    ∃ z ∈ s, ∀ i, r (v i) z :=
  match n with
  | 0     => by
    rcases hs with ⟨x, hx⟩; exact ⟨x, hx, fun i ↦ IsEmpty.elim inferInstance i⟩
  | n + 1 => by
    have : ∃ z ∈ s, ∀ i : Fin n, r (v i.succ) z := h.vector_le tr hs (n := n) (fun i ↦ v i.succ) fun i ↦ hv i.succ
    rcases this with ⟨x, hx, hr⟩
    have : ∃ z ∈ s, r x z ∧ r (v 0) z := h x hx (v 0) (hv 0)
    rcases this with ⟨z, hz, hrxz, hrz⟩
    refine ⟨z, hz, ?_⟩
    intro i
    cases i using Fin.cases
    case zero => assumption
    case succ i =>
      exact tr.trans _ _ _ (hr i) hrxz

lemma fintype_colimit [Fintype ι] (tr : IsTrans α r)
    {s : Set α} (hs : s.Nonempty) (h : DirectedOn r s) (v : ι → α) (hv : ∀ i, v i ∈ s) :
    ∃ z ∈ s, ∀ i, r (v i) z := by
  let f : Fin (Fintype.card ι) → α := fun x ↦ v ((Fintype.equivFin ι).symm x)
  rcases DirectedOn.vector_le tr hs h f (by intro; simp [f, hv]) with ⟨z, hzs, hz⟩
  exact ⟨z, hzs, fun i ↦ by simpa [f] using hz ((Fintype.equivFin ι) i)⟩

end DirectedOn

namespace Order

variable {α : Type*} [Preorder α]

def IsDense (s : Set α) : Prop := ∀ p, ∃ q ≤ p, q ∈ s

def IsDenseBelow (s : Set α) (a : α) : Prop := ∀ p ≤ a, ∃ q ≤ p, q ∈ s

variable (α)

@[ext] structure DenseSet where
  set : Set α
  is_dense : IsDense set

variable {α}

namespace DenseSet

instance : SetLike (DenseSet α) α where
  coe s := s.set
  coe_injective' s t e := by ext; simp_all

noncomputable def choose (d : DenseSet α) (a : α) : α := (d.is_dense a).choose

@[simp] lemma choose_le (d : DenseSet α) (a : α) : d.choose a ≤ a := (d.is_dense a).choose_spec.1

@[simp] lemma choose_mem (d : DenseSet α) (a : α) : d.choose a ∈ d := (d.is_dense a).choose_spec.2

end DenseSet

namespace PFilter

def ofDescendingChain (s : ℕ → α) (hs : ∀ i j, i ≤ j → s i ≥ s j) : PFilter α :=
  IsPFilter.toPFilter <| Order.IsPFilter.of_def (F := {x | ∃ i, s i ≤ x})
    ⟨s 0, 0, by rfl⟩
    (by rintro x₁ ⟨i₁, h₁⟩ x₂ ⟨i₂, h₂⟩
        wlog hi : i₁ ≤ i₂
        · have z : i₂ ≤ i₁ := by exact Nat.le_of_not_ge hi
          rcases this s hs x₂ i₂ h₂ x₁ i₁ h₁ (Nat.le_of_not_ge hi) with ⟨z, hz⟩
          exact ⟨z, hz.1, hz.2.2, hz.2.1⟩
        exact ⟨s i₂, ⟨i₂, by rfl⟩, le_trans (hs i₁ i₂ hi) h₁, by simp [h₂]⟩)
    (by rintro x y hxy ⟨i, hix⟩
        exact ⟨i, le_trans hix hxy⟩)

@[simp] lemma mem_descendingChain_iff (s : ℕ → α) (hs : ∀ i j, i ≤ j → s i ≥ s j) :
    x ∈ ofDescendingChain s hs ↔ ∃ i, s i ≤ x := by rfl

class IsGeneric (F : PFilter α) (𝓓 : Set (DenseSet α)) where
  isGeneric : ∀ d ∈ 𝓓, ∃ a ∈ F, a ∈ d

@[simp] instance IsGeneric.empty (F : PFilter α) : F.IsGeneric ∅ := ⟨by simp⟩

theorem countable_isGeneric (𝓓 : Set (DenseSet α)) (ctb : Set.Countable 𝓓) (a : α) :
    ∃ G : PFilter α, G.IsGeneric 𝓓 ∧ a ∈ G := by
  by_cases emp : 𝓓.Nonempty
  case neg => exact ⟨principal a, by simp [Set.not_nonempty_iff_eq_empty.mp emp]⟩
  have : ∃ D : ℕ → 𝓓, Function.Surjective D := ctb.exists_surjective emp
  rcases this with ⟨D, hD⟩
  let s (n : ℕ) : α := n.rec a fun i ↦ (D i).val.choose
  have hs : ∀ i j, i ≤ j → s i ≥ s j := fun i j hij ↦
    Nat.monotone_of_succ_monotone (r := fun i j ↦ s i ≥ s j)
      (fun _ ↦ le_refl _)
      ⟨fun _ _ _ ↦ ge_trans⟩
      (by simp [s]) hij
  refine ⟨ofDescendingChain s hs, ⟨?_⟩, ?_⟩
  · intro d hd
    rcases show ∃ i, D i = ⟨d, hd⟩ from hD ⟨d, hd⟩ with ⟨i, hi⟩
    refine ⟨s (i + 1), ?_, ?_⟩
    · simp only [mem_descendingChain_iff]
      exact ⟨i + 1, by rfl⟩
    · simp [s, hi]
  · suffices ∃ i, s i ≤ a by simpa
    refine ⟨0, by simp [s]⟩

end Order.PFilter

end
