module

public import Foundation.FirstOrder.SetTheory.Recursion.Seq
public import Foundation.FirstOrder.SetTheory.Recursion

@[expose] public section
/-!

# Blueprint for the recursion theorem in $\mathsf{ZF}$

-/

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace PR

structure Blueprint (k : ℕ) where
  graph : SetTheorySemisentence (k + 2)

def Blueprint.isAttempt_dfn (p : Blueprint k) : SetTheorySemisentence (k + 2) :=
  f“α f.
    !IsOrdinal.dfn α ∧ !IsFunction.dfn f ∧ !domain.dfn f = α ∧
    ∀ β ∈ α, ∀ y, !kpair.dfn β y ∈ f ↔ y = !p.graph (!restrict.dfn f β) ⋯”

#check fun (φ : Semisentence ℒₒᵣ 3) ↦ (⤫term(faf)[ α x y |   | !φ α x ⋯ ] : Semisentence ℒₒᵣ 3)

def Blueprint.result.dfn {k} (p : Blueprint k) : SetTheorySemisentence (k + 2) :=
  “x y. ∃ α, ∃ f, !p.isAttempt_dfn α f ⋯ ∧ x ∼[f] y”

/- TODO: Once the Lévy hierarchy has been added, add a `Δ` version. -/
-- def Blueprint.resultDeltaDef (p : Blueprint k) : SetTheorySemisentence (k + 2) := p.result.dfn.graphDelta

variable (V)

structure Construction {k : ℕ} (p : Blueprint k) where
  core : (Fin k → V) → V → V
  core_defined : DefinedFunction (fun v ↦ core (v ·.succ) (v 0)) p.graph

variable {V}

namespace Construction

variable {k : ℕ} {p : Blueprint k} (c : Construction V p) (v : Fin k → V)

def IsAttempt (α f : V) : Prop :=
  SetTheory.IsAttempt (c.core v) f α

lemma attempt_defined : Defined (fun v ↦ c.IsAttempt (v ·.succ.succ) (v 1) (v 0) : (Fin (k + 2) → V) → Prop) p.isAttempt_dfn := .mk fun v ↦ by
  simp_all [SetTheory.IsAttempt, Construction.IsAttempt, Blueprint.isAttempt_dfn]
  intro h₁ h₂ h₃
  sorry

@[simp] lemma attempt_defined_iff (v : Fin (k + 2) → V) :
    p.isAttempt_dfn.Evalb (v ·.succ.succ) (v 0) ↔ c.IsAttempt (v ·.succ.succ) (v 1) (v 0) := c.attempt_defined.iff

variable {c v}

namespace IsAttempt

variable {f : V}

lemma seq (h : c.IsAttempt v f) : Seq s := h.1

lemma zero (h : c.IsAttempt v f) : ⟨0, c.zero v⟩ₖ ∈ s := h.2.1

lemma succ (h : c.IsAttempt v f) : ∀ α, SetTheory.succ α ∈ lh s → ∀ z, ⟨α, z⟩ₖ ∈ s → ⟨SetTheory.succ α, c.core v z⟩ₖ ∈ s := h.2.2

lemma unique {f g α β : V} (H₁ : c.IsAttempt v α f) (H₂ : c.IsAttempt v β g) (h₁₂ : α ⊆ β) {x} (hi : x ∈ α) {y₁ y₂} :
    ⟨x, y₁⟩ₖ ∈ f → ⟨x, y₂⟩ₖ ∈ g → y₁ = y₂ := by
  #check SetTheory.IsAttempt.isAttempt_unique H₁
  #check fun (hy₁ : ⟨x, y₁⟩ₖ ∈ f) (hy₂ : ⟨x, y₂⟩ₖ ∈ g) ↦ H₁.2.1.unique hy₁ hy₂
  sorry
  -- revert z₁ z₂
  -- suffices ∀ z₁ < s₁, ∀ z₂ < s₂, ⟪i, z₁⟫ ∈ s₁ → ⟪i, z₂⟫ ∈ s₂ → z₁ = z₂
  -- by intro z₁ z₂ hz₁ hz₂; exact this z₁ (lt_of_mem_rng hz₁) z₂ (lt_of_mem_rng hz₂) hz₁ hz₂
  -- intro z₁ hz₁ z₂ hz₂ h₁ h₂
  -- induction i using ISigma1.sigma1_succ_induction generalizing z₁ z₂
  -- · definability
  -- case zero =>
  --   have : z₁ = c.zero v := H₁.seq.isMapping.uniq h₁ H₁.zero
  --   have : z₂ = c.zero v := H₂.seq.isMapping.uniq h₂ H₂.zero
  --   simp_all
  -- case succ i ih =>
  --   have hi' : i < lh s₁ := lt_of_le_of_lt (by simp) hi
  --   let z' := H₁.seq.nth hi'
  --   have ih₁ : ⟪i, z'⟫ ∈ s₁ := H₁.seq.nth_mem hi'
  --   have ih₂ : ⟪i, z'⟫ ∈ s₂ := by
  --     have : z' = H₂.seq.nth (lt_of_lt_of_le hi' h₁₂) :=
  --       ih hi' z' (by simp [z']) (H₂.seq.nth (lt_of_lt_of_le hi' h₁₂)) (by simp) (by simp [z']) (by simp)
  --     simp [this]
  --   have h₁' : ⟪i + 1, c.succ v i z'⟫ ∈ s₁ := H₁.succ i (by simp [lt_tsub_iff_right, hi]) z' ih₁
  --   have h₂' : ⟪i + 1, c.succ v i z'⟫ ∈ s₂ :=
  --     H₂.succ i (by simpa [lt_tsub_iff_right] using lt_of_lt_of_le hi h₁₂) z' ih₂
  --   have e₁ : z₁ = c.succ v i z' := H₁.seq.isMapping.uniq h₁ h₁'
  --   have e₂ : z₂ = c.succ v i z' := H₂.seq.isMapping.uniq h₂ h₂'
  --   simp [e₁, e₂]

end IsAttempt

lemma IsAttempt.initial : c.IsAttempt v !⟦c.zero v⟧ :=
  ⟨by simp, by simp [seqCons], by simp⟩

lemma IsAttempt.successor {s l z : V} (Hs : c.IsAttempt v s) (hl : l + 1 = lh s) (hz : ⟪l, z⟫ ∈ s) :
    c.IsAttempt v (s ⁀' c.succ v l z) :=
  ⟨ Hs.seq.seqCons _, by simp [seqCons, Hs.zero], by
    simp only [Hs.seq.lh_seqCons, add_tsub_cancel_right]
    intro i hi w hiw
    have hiws : ⟪i, w⟫ ∈ s := by
      rcases show i = lh s ∧ w = c.succ v l z ∨ ⟪i, w⟫ ∈ s by
        simpa [mem_seqCons_iff] using hiw with (⟨rfl, rfl⟩ | h)
      · simp at hi
      · assumption
    have : i ≤ l := by simpa [←hl, lt_succ_iff_le] using hi
    rcases this with (rfl | hil)
    · have : w = z := Hs.seq.isMapping.uniq hiws hz
      simp [this, hl]
    · simp only [mem_seqCons_iff]; right
      exact Hs.succ i (by simp [←hl, hil]) w hiws ⟩

variable (c v)

open Classical in
lemma IsAttempt.exists (l : V) : ∃ s, c.IsAttempt v s ∧ l + 1 = lh s := by
  induction l using ISigma1.sigma1_succ_induction
  · apply HierarchySymbol.Definable.exs
    apply HierarchySymbol.Definable.and
    · exact ⟨p.IsAttemptDef.rew (Rew.embSubsts <| #0 :> fun i ↦ &(v i)), by
         intro w; simpa [Matrix.comp_vecCons''] using! c.attempt_defined_iff (w 0 :> v)⟩
    · definability
  case zero =>
    exact ⟨!⟦c.zero v⟧, IsAttempt.initial, by simp⟩
  case succ l ih =>
    rcases ih with ⟨s, Hs, hls⟩
    have hl : l < lh s := by simp [←hls]
    have : ∃ z, ⟪l, z⟫ ∈ s := Hs.seq.exists hl
    rcases this with ⟨z, hz⟩
    exact ⟨s ⁀' c.succ v l z, Hs.successor hls hz, by simp [Hs.seq, hls]⟩

lemma attempt_result_existsUnique (l : V) : ∃! z, ∃ s, c.IsAttempt v s ∧ l + 1 = lh s ∧ ⟪l, z⟫ ∈ s := by
  rcases IsAttempt.exists c v l with ⟨s, Hs, h⟩
  have : ∃ z, ⟪l, z⟫ ∈ s := Hs.seq.exists (show l < lh s from by simp [←h])
  rcases this with ⟨z, hz⟩
  exact ExistsUnique.intro z ⟨s, Hs, h, hz⟩ (by
    rintro z' ⟨s', Hs', h', hz'⟩
    exact Eq.symm <| Hs.unique Hs' (by simp [←h, ←h']) (show l < lh s from by simp [←h]) hz hz')

noncomputable def result (u : V) : V := Classical.choose! (c.attempt_result_existsUnique v u)

lemma result_spec (u : V) : ∃ s, c.IsAttempt v s ∧ u + 1 = lh s ∧ ⟪u, c.result v u⟫ ∈ s :=
  Classical.choose!_spec (c.attempt_result_existsUnique v u)

@[simp] theorem result_zero : c.result v 0 = c.zero v := by
  rcases c.result_spec v 0 with ⟨s, Hs, _, h0⟩
  exact Hs.seq.isMapping.uniq h0 Hs.zero

@[simp] theorem result_succ (u : V) : c.result v (u + 1) = c.succ v u (c.result v u) := by
  rcases c.result_spec v u with ⟨s, Hs, hk, h⟩
  have : IsAttempt c v (s ⁀' c.succ v u (result c v u) ) := Hs.successor hk h
  exact Eq.symm
    <| Classical.choose_uniq (c.attempt_result_existsUnique v (u + 1))
    ⟨_, this, by simp [Hs.seq, hk], by simp [hk]⟩

lemma result_graph (z u : V) : z = c.result v u ↔ ∃ s, c.IsAttempt v s ∧ ⟪u, z⟫ ∈ s :=
  ⟨by rintro rfl
      rcases c.result_spec v u with ⟨s, Hs, _, h⟩
      exact ⟨s, Hs, h⟩,
   by rintro ⟨s, Hs, h⟩
      rcases c.result_spec v u with ⟨s', Hs', hu, h'⟩
      exact Eq.symm <| Hs'.unique Hs
        (by simpa [←hu, succ_le_iff_lt] using Hs.seq.lt_lh_iff.mpr (mem_domain_of_pair_mem h))
        (by simp [←hu]) h' h⟩

set_option linter.flexible false in
lemma result_defined : DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → V) → V) p.resultDef := .mk fun v ↦ by
  simp [Blueprint.resultDef, result_graph]
  apply exists_congr; intro x
  simp [c.attempt_defined_iff]

lemma result_defined_delta : DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → V) → V) p.resultDeltaDef :=
  c.result_defined.graph_delta

@[simp] lemma result_defined_iff (v : Fin (k + 2) → V) :
    p.resultDef.val.Evalb v ↔ v 0 = c.result (v ·.succ.succ) (v 1) := c.result_defined.iff

instance result_definable : DefinableFunction (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → V) → V) :=
  c.result_defined.to_definable

/- TODO: Once the Lévy hierarchy has been added, add a `Δ₁` version. -/
/- instance result_definable_delta₁ : DefinableFunction (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → V) → V) :=
  c.result_defined_delta.to_definable -/

attribute [irreducible] Blueprint.resultDef

end Construction

end PR

end LO.FirstOrder.SetTheory
