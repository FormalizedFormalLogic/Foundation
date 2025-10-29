import Foundation.Vorspiel.Vorspiel

namespace Order

inductive Point where | point

namespace Point

instance : Subsingleton Point := ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩

instance : Fintype Point := Fintype.ofSubsingleton .point

instance : DecidableEq Point := fun a b ↦
  match a, b with
  | ⟨⟩, ⟨⟩ => .isTrue rfl

instance : LinearOrder Point where
  le a b := True
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial
  le_antisymm := by rintro ⟨⟩ ⟨⟩ _ _; rfl
  le_total _ _ := by simp
  toDecidableLE := fun a b ↦ .isTrue trivial

instance : CompleteLattice Point where
  top := .point
  bot := .point
  sSup _ := .point
  sInf _ := .point
  le_top _ := trivial
  bot_le _ := trivial
  le_sSup _ _ _ := trivial
  sSup_le _ _ _ := trivial
  sInf_le _ _ _ := trivial
  le_sInf _ _ _ := trivial

@[simp] lemma eq_point (a : Point) : a = point := by rcases a; rfl

@[simp] lemma le (a b : Point) : a ≤ b := trivial

@[simp] lemma not_lt (a b : Point) : ¬a < b := by rintro ⟨⟩; simp_all

end Point

end Order

variable {α : Type*} {r : α → α → Prop}

private lemma DirectedOn.vector_le (tr : Transitive r) {s : Set α} (hs : s.Nonempty) (h : DirectedOn r s) (v : Fin n → α) (hv : ∀ i, v i ∈ s) :
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
      exact tr (hr i) hrxz

open Fintype

lemma DirectedOn.fintype_colimit [Fintype ι] (tr : Transitive r)
    {s : Set α} (hs : s.Nonempty) (h : DirectedOn r s) (v : ι → α) (hv : ∀ i, v i ∈ s) :
    ∃ z ∈ s, ∀ i, r (v i) z := by
  let f : Fin (card ι) → α := fun x ↦ v ((Fintype.equivFin ι).symm x)
  rcases DirectedOn.vector_le tr hs h f (by intro; simp [f, hv]) with ⟨z, hzs, hz⟩
  exact ⟨z, hzs, fun i ↦ by simpa [f] using hz ((Fintype.equivFin ι) i)⟩
