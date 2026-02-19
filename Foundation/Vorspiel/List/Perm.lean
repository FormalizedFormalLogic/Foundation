module

public import Foundation.Vorspiel.List.Basic

@[expose]
public section

namespace List

variable {α : Type*}

lemma Perm.two_iff {a b : α} {l : List α} :
    l ~ [a, b] ↔ l = [a, b] ∨ l = [b, a] := by
  constructor
  · intro h
    have hlen : l.length = 2 := List.Perm.length_eq h
    rcases List.length_eq_two.mp hlen with ⟨x, y, rfl⟩
    have ha : a = x ∨ a = y := by
      have : a ∈ [x, y] := (List.Perm.mem_iff h.symm).mp (by simp)
      simpa using this
    have hb : b = x ∨ b = y := by
      have : b ∈ [x, y] := (List.Perm.mem_iff h.symm).mp (by simp)
      simpa using this
    rcases ha with (rfl | rfl) <;> rcases hb with (rfl | rfl)
    · have : b = y := by simpa using replicate_perm (n := 2) (a := b) |>.mp h.symm
      simp_all
    · simp
    · simp
    · have : b = x := by simpa using List.replicate_perm (n := 2) (a := b) |>.mp h.symm
      simp_all
  · intro h
    rcases h with (rfl | rfl)
    · simp
    · exact swap _ _ []

inductive CompSubset : List α → List α → Type _
  | refl (l) : CompSubset l l
  | perm : CompSubset l₁ l₂ → l₂ ~ l₃ → CompSubset l₁ l₃
  | add (a : α) :
    CompSubset l₁ l₂ → CompSubset l₁ (a :: l₂)
  | double {a : α} :
    CompSubset l₁ (a :: a :: l₂) → CompSubset l₁ (a :: l₂)

variable [DecidableEq α]

lemma remove_def (a b : α) (l : List α) : remove a (b :: l) = if a = b then remove a l else b :: remove a l := by
  simp [remove, List.filter]; grind

lemma count_def (a b : α) (l : List α) : count a (b :: l) = if a = b then count a l + 1 else count a l := by
  simp [count]; grind

lemma perm_normalize (l : List α) (a : α) : l ~ replicate (l.count a) a ++ l.remove a :=
  match l with
  |     [] => by simp
  | b :: l => by
    by_cases h : a = b
    · simp [h, List.replicate, perm_normalize l]
    · suffices b :: l ~ replicate (count a l) a ++ b :: remove a l by simpa [h, remove_def, count_def]
      calc
        b :: l ~ b :: (replicate (l.count a) a ++ l.remove a) := by simp [perm_normalize l]
             _ ~ replicate (count a l) a ++ b :: remove a l   := Perm.symm perm_middle

namespace CompSubset

def iterated_double {l₁ l₂ : List α} {a : α} (h : k > 0)
    (c : l₁.CompSubset (replicate k a ++ l₂)) : l₁.CompSubset (a :: l₂) :=
  match k with
  |     1 => c
  | k + 2 => iterated_double (k := k + 1) (by simp) c.double

def trans {l₁ l₂ l₃ : List α} (c₁ : l₁.CompSubset l₂) (c₂ : l₂.CompSubset l₃) : l₁.CompSubset l₃ :=
  match c₂ with
  |     refl _ => c₁
  | perm c₂ hp => (c₁.trans c₂).perm hp
  |   add b c₂ => (c₁.trans c₂).add b
  |  double c₂ => (c₁.trans c₂).double

def cons {l₁ l₂ : List α} (c : l₁.CompSubset l₂) (a) : (a :: l₁).CompSubset (a :: l₂) :=
  match c with
  |     refl _ => CompSubset.refl _
  | perm c₂ hp => (CompSubset.cons c₂ a).perm (by simp [hp])
  |   add b c₂ => ((c₂.cons a).add b).perm (Perm.swap a b _)
  |  double (a := b) (l₂ := l₂) c₂ =>
    have : (a :: l₁).CompSubset (b :: b :: a :: l₂) := (c₂.cons a).perm (by grind)
    this.double.perm (Perm.swap a b l₂)

end CompSubset

def Subset.toCompSubst {l₁ l₂ : List α} (h : l₁ ⊆ l₂) : l₁.CompSubset l₂ :=
  match l₂ with
  |      [] =>
    have : l₁ = [] := by simpa using h
    this ▸ CompSubset.refl []
  | a :: l₂ =>
    if ha : a ∈ l₁ then
      have : l₁.CompSubset (replicate (l₁.count a) a ++ l₁.remove a) := (CompSubset.refl l₁).perm (perm_normalize l₁ a)
      have c₁ : l₁.CompSubset (a :: remove a l₁) := this.iterated_double (count_pos_iff.mpr ha)
      have : remove a l₁ ⊆ l₂ := by grind only [= subset_def, usr eq_or_mem_of_mem_cons, mem_remove_iff]
      have c₂ : (remove a l₁).CompSubset l₂ := Subset.toCompSubst this
      c₁.trans (c₂.cons a)
    else
      have : l₁ ⊆ l₂ := by grind
      CompSubset.add _ (Subset.toCompSubst this)

end List
