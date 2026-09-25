module

public import Mathlib.Data.List.Basic

/-!
# Exactly one of a list of propositions

`l.ExactlyOne` states that exactly one of the propositions in `l` holds, in the style of
`List.TFAE`. The tactic `exactly_one` reduces a goal `[p₁, …, pₙ].ExactlyOne` to the disjunction
`p₁ ∨ ⋯ ∨ pₙ` and the exclusivity `¬(pᵢ ∧ pⱼ)` of each pair `i < j`.
-/

@[expose] public section

namespace List

/-- Exactly one of the propositions in `l` holds. -/
def ExactlyOne (l : List Prop) : Prop := (∃ p ∈ l, p) ∧ l.Pairwise fun p q ↦ ¬(p ∧ q)

variable {l : List Prop} {p : Prop}

lemma ExactlyOne.intro (h₁ : ∃ p ∈ l, p) (h₂ : l.Pairwise fun p q ↦ ¬(p ∧ q)) : l.ExactlyOne :=
  ⟨h₁, h₂⟩

lemma ExactlyOne.exists (h : l.ExactlyOne) : ∃ p ∈ l, p := h.1

@[simp] lemma not_exactlyOne_nil : ¬[].ExactlyOne := by simp [ExactlyOne]

lemma exactlyOne_cons : (p :: l).ExactlyOne ↔ p ∧ (∀ q ∈ l, ¬q) ∨ ¬p ∧ l.ExactlyOne := by
  by_cases hp : p;
  · suffices (p :: l).ExactlyOne ↔ ∀ q ∈ l, ¬q by simpa [hp];
    constructor;
    · exact fun h q hq hq' ↦ (pairwise_cons.mp h.2).1 q hq ⟨hp, hq'⟩;
    · exact fun h ↦ ⟨⟨p, by simp, hp⟩, pairwise_cons.mpr
        ⟨fun q hq hpq ↦ h q hq hpq.2, pairwise_of_forall_mem_list fun q hq _ _ hqr ↦ h q hq hqr.1⟩⟩;
  · rw [ExactlyOne, ExactlyOne, exists_mem_cons_iff, pairwise_cons];
    simp [hp]

lemma ExactlyOne.not_getElem (h : l.ExactlyOne) {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (hij : i ≠ j) (hpi : l[i]) : ¬l[j] := fun hpj ↦ by
  rcases Nat.lt_or_gt_of_ne hij with hij | hij;
  · exact h.2.rel_getElem_of_lt hi hj hij ⟨hpi, hpj⟩;
  · exact h.2.rel_getElem_of_lt hj hi hij ⟨hpj, hpi⟩;

lemma exactlyOne_iff_existsUnique : l.ExactlyOne ↔ ∃! i : Fin l.length, l[i] := by
  constructor;
  · intro h;
    obtain ⟨p, hp, hpt⟩ := h.exists;
    obtain ⟨i, hi, rfl⟩ := getElem_of_mem hp;
    exact ⟨⟨i, hi⟩, hpt, fun j hj ↦ Fin.ext <| by_contra fun hji ↦
      h.not_getElem hi j.2 (Ne.symm hji) hpt hj⟩;
  · rintro ⟨i, hi, hu⟩;
    exact ⟨⟨_, getElem_mem _, hi⟩, pairwise_iff_getElem.mpr fun j k hj hk hjk ⟨hpj, hpk⟩ ↦
      Nat.ne_of_lt hjk <| congrArg Fin.val <| (hu ⟨j, hj⟩ hpj).trans (hu ⟨k, hk⟩ hpk).symm⟩;

end List

/-- `exactly_one` reduces a goal `[p₁, …, pₙ].ExactlyOne` to the disjunction `p₁ ∨ ⋯ ∨ pₙ` and
the exclusivity `¬(pᵢ ∧ pⱼ)` of each pair `i < j`, in this order. -/
macro "exactly_one" : tactic => `(tactic| (
  apply List.ExactlyOne.intro
  on_goal 2 =>
    simp only [List.pairwise_cons, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
      implies_true, List.Pairwise.nil, and_true]
    and_intros
  on_goal 1 =>
    simp only [List.exists_mem_cons_iff, List.not_mem_nil, false_and, exists_false, or_false]))

end
