import Arithmetization.ISigmaOne.HFS

/-!

# Primitive Recursive Functions in $\mathsf{I} \Sigma_1$

-/

noncomputable section

namespace LO.FirstOrder.Arith.Model

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

namespace PR

structure Formulae (k : ℕ) where
  zero : HSemisentence ℒₒᵣ (k + 1) 𝚺₁
  succ : HSemisentence ℒₒᵣ (k + 3) 𝚺₁

def Formulae.cseqDef (p : Formulae k) : HSemisentence ℒₒᵣ (k + 1) 𝚺₁ := .mkSigma
  “!seqDef.val [#0] ∧
    (∃[#0 < #1] (!(Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.zero.val) ∧ 0 ~[#1] #0)) ∧
    ∀[#0 < 2 * #1] (
      (∃[#0 < 2 * #2 + 1] (!lhDef.val [#0, #2] ∧ #1 + 1 < #0)) →
      ∀[#0 < #2] (#1 ~[#2] #0 →
        ∃[#0 < #3] (!(Rew.substs (#0 :> #1 :> #2 :> (#·.succ.succ.succ.succ)) |>.hom p.succ.val) ∧ #2 + 1 ~[#3] #0)))” (by simp)

def Formulae.resultDef (p : Formulae k) : HSemisentence ℒₒᵣ (k + 2) 𝚺₁ := .mkSigma
  (∃' ((Rew.substs (#0 :> (#·.succ.succ.succ)) |>.hom p.cseqDef.val) ⋏ “#2 ~[#0] #1”)) (by simp)

def Formulae.resultDeltaDef (p : Formulae k) : HSemisentence ℒₒᵣ (k + 2) 𝚫₁ := p.resultDef.graphDelta

variable (M)

structure Construction {k : ℕ} (p : Formulae k) where
  zero : (Fin k → M) → M
  succ : (Fin k → M) → M → M → M
  zero_defined : DefinedFunction ℒₒᵣ 𝚺₁ zero p.zero
  succ_defined : DefinedFunction ℒₒᵣ 𝚺₁ (fun v ↦ succ (v ·.succ.succ) (v 1) (v 0)) p.succ

variable {M}

namespace Construction

variable {k : ℕ} {p : Formulae k} (c : Construction M p) (v : Fin k → M)

def CSeq (s : M) : Prop := Seq s ∧ ⟪0, c.zero v⟫ ∈ s ∧ ∀ i < lh s - 1, ∀ z, ⟪i, z⟫ ∈ s → ⟪i + 1, c.succ v i z⟫ ∈ s

private lemma cseq_iff (s : M) : c.CSeq v s ↔
    Seq s
    ∧ (∃ z < s, z = c.zero v ∧ ⟪0, z⟫ ∈ s)
    ∧ (∀ i < 2 * s,
      (∃ l < 2 * s + 1, l = lh s ∧ i + 1 < l) → ∀ z < s, ⟪i, z⟫ ∈ s → ∃ u < s, u = c.succ v i z ∧ ⟪i + 1, u⟫ ∈ s) :=
  ⟨by rintro ⟨Hs, hz, hs⟩
      exact ⟨Hs, ⟨c.zero v, lt_of_mem_rng hz, rfl, hz⟩, fun i _ hi z _ hiz ↦
      ⟨c.succ v i z, by
        have := hs i (by rcases hi with ⟨l, _, rfl, hl⟩; simp [lt_tsub_iff_right, hl]) z hiz
        exact ⟨lt_of_mem_rng this, rfl, this⟩⟩⟩,
   by rintro ⟨Hs, ⟨z, _, rfl, hz⟩, h⟩
      exact ⟨Hs, hz, fun i hi z hiz ↦ by
        rcases h i
          (lt_of_lt_of_le hi (by simp; exact le_trans (lh_bound _) (by simp)))
          ⟨lh s, by simp [lt_succ_iff_le], rfl, by simpa [lt_tsub_iff_right] using hi⟩ z (lt_of_mem_rng hiz) hiz with ⟨_, _, rfl, h⟩
        exact h⟩⟩

lemma cseq_defined : Model.Defined (fun v ↦ c.CSeq (v ·.succ) (v 0) : (Fin (k + 1) → M) → Prop) p.cseqDef := by
  intro v; simp [Formulae.cseqDef, cseq_iff, c.zero_defined.df.iff, c.succ_defined.df.iff]

@[simp] lemma cseq_defined_iff (v) :
    Semiformula.Evalbm M v p.cseqDef.val ↔ c.CSeq (v ·.succ) (v 0) := c.cseq_defined.df.iff v

variable {c v}

namespace CSeq

variable {s : M} (h : c.CSeq v s)

lemma seq : Seq s := h.1

lemma zero : ⟪0, c.zero v⟫ ∈ s := h.2.1

lemma succ : ∀ i < lh s - 1, ∀ z, ⟪i, z⟫ ∈ s → ⟪i + 1, c.succ v i z⟫ ∈ s := h.2.2

lemma unique {s₁ s₂ : M} (H₁ : c.CSeq v s₁) (H₂ : c.CSeq v s₂) (h₁₂ : lh s₁ ≤ lh s₂) {i} (hi : i < lh s₁) {z₁ z₂} :
    ⟪i, z₁⟫ ∈ s₁ → ⟪i, z₂⟫ ∈ s₂ → z₁ = z₂ := by
  revert z₁ z₂
  suffices ∀ z₁ < s₁, ∀ z₂ < s₂, ⟪i, z₁⟫ ∈ s₁ → ⟪i, z₂⟫ ∈ s₂ → z₁ = z₂
  by intro z₁ z₂ hz₁ hz₂; exact this z₁ (lt_of_mem_rng hz₁) z₂ (lt_of_mem_rng hz₂) hz₁ hz₂
  intro z₁ hz₁ z₂ hz₂ h₁ h₂
  induction i using induction_iSigmaOne generalizing z₁ z₂
  · definability
  case zero =>
    have : z₁ = c.zero v := H₁.seq.isMapping.uniq h₁ H₁.zero
    have : z₂ = c.zero v := H₂.seq.isMapping.uniq h₂ H₂.zero
    simp_all
  case succ i ih =>
    have hi' : i < lh s₁ := lt_of_le_of_lt (by simp) hi
    let z' := H₁.seq.nth hi'
    have ih₁ : ⟪i, z'⟫ ∈ s₁ := H₁.seq.nth_mem hi'
    have ih₂ : ⟪i, z'⟫ ∈ s₂ := by
      have : z' = H₂.seq.nth (lt_of_lt_of_le hi' h₁₂) :=
        ih hi' z' (by simp [z']) (H₂.seq.nth (lt_of_lt_of_le hi' h₁₂)) (by simp [z']) (by simp [z']) (by simp)
      simp [this]
    have h₁' : ⟪i + 1, c.succ v i z'⟫ ∈ s₁ := H₁.succ i (by simp [lt_tsub_iff_right, hi]) z' ih₁
    have h₂' : ⟪i + 1, c.succ v i z'⟫ ∈ s₂ := H₂.succ i (by simp [lt_tsub_iff_right]; exact lt_of_lt_of_le hi h₁₂) z' ih₂
    have e₁ : z₁ = c.succ v i z' := H₁.seq.isMapping.uniq h₁ h₁'
    have e₂ : z₂ = c.succ v i z' := H₂.seq.isMapping.uniq h₂ h₂'
    simp [e₁, e₂]

end CSeq

lemma CSeq.initial : c.CSeq v !⟨c.zero v⟩ :=
  ⟨by simp, by simp [seqCons], by simp⟩

lemma CSeq.successor {s l z : M} (Hs : c.CSeq v s) (hl : l + 1 = lh s) (hz : ⟪l, z⟫ ∈ s) :
    c.CSeq v (s ⁀' c.succ v l z) :=
  ⟨ Hs.seq.seqCons _, by simp [seqCons, Hs.zero], by
    simp [Hs.seq.lh_seqCons]
    intro i hi w hiw
    have hiws : ⟪i, w⟫ ∈ s := by
      simp [mem_seqCons_iff] at hiw; rcases hiw with (⟨rfl, rfl⟩ | h)
      · simp at hi
      · assumption
    have : i ≤ l := by simpa [←hl, lt_succ_iff_le] using hi
    rcases this with (rfl | hil)
    · have : w = z := Hs.seq.isMapping.uniq hiws hz
      simp [this, hl]
    · simp [mem_seqCons_iff]; right
      exact Hs.succ i (by simp [←hl, hil]) w hiws ⟩

variable (c v)

lemma CSeq.exists (l : M) : ∃ s, c.CSeq v s ∧ l + 1 = lh s := by
  induction l using induction_iSigmaOne
  · apply Definable.ex
    apply Definable.and
    · exact ⟨p.cseqDef.rew (Rew.embSubsts <| #0 :> fun i ↦ &(v i)), by
        intro w; simpa using c.cseq_defined_iff (w 0 :> v) |>.symm⟩
    · definability
  case zero =>
    exact ⟨!⟨c.zero v⟩, CSeq.initial, by simp⟩
  case succ l ih =>
    rcases ih with ⟨s, Hs, hls⟩
    have hl : l < lh s := by simp [←hls]
    have : ∃ z, ⟪l, z⟫ ∈ s := Hs.seq.exists hl
    rcases this with ⟨z, hz⟩
    exact ⟨s ⁀' c.succ v l z, Hs.successor hls hz, by simp [Hs.seq, hls]⟩

lemma cSeq_result_existsUnique (l : M) : ∃! z, ∃ s, c.CSeq v s ∧ l + 1 = lh s ∧ ⟪l, z⟫ ∈ s := by
  rcases CSeq.exists c v l with ⟨s, Hs, h⟩
  have : ∃ z, ⟪l, z⟫ ∈ s := Hs.seq.exists (show l < lh s from by simp [←h])
  rcases this with ⟨z, hz⟩
  exact ExistsUnique.intro z ⟨s, Hs, h, hz⟩ (by
    rintro z' ⟨s', Hs', h', hz'⟩
    exact Eq.symm <| Hs.unique Hs' (by simp [←h, ←h']) (show l < lh s from by simp [←h]) hz hz')

def result (u : M) : M := Classical.choose! (c.cSeq_result_existsUnique v u)

lemma result_spec (u : M) : ∃ s, c.CSeq v s ∧ u + 1 = lh s ∧ ⟪u, c.result v u⟫ ∈ s :=
  Classical.choose!_spec (c.cSeq_result_existsUnique v u)

@[simp] theorem result_zero : c.result v 0 = c.zero v := by
  rcases c.result_spec v 0 with ⟨s, Hs, _, h0⟩
  exact Hs.seq.isMapping.uniq h0 Hs.zero

@[simp] theorem result_succ (u : M) : c.result v (u + 1) = c.succ v u (c.result v u) := by
  rcases c.result_spec v u with ⟨s, Hs, hk, h⟩
  have : CSeq c v (s ⁀' c.succ v u (result c v u) ) := Hs.successor hk h
  exact Eq.symm
    <| Classical.choose_uniq (c.cSeq_result_existsUnique v (u + 1))
    ⟨_, this, by simp [Hs.seq, hk], by simp [hk]⟩

lemma result_graph (z u : M) : z = c.result v u ↔ ∃ s, c.CSeq v s ∧ ⟪u, z⟫ ∈ s :=
  ⟨by rintro rfl
      rcases c.result_spec v u with ⟨s, Hs, _, h⟩
      exact ⟨s, Hs, h⟩,
   by rintro ⟨s, Hs, h⟩
      rcases c.result_spec v u with ⟨s', Hs', hu, h'⟩
      exact Eq.symm <| Hs'.unique Hs
        (by simp [←hu, succ_le_iff_lt]; exact Hs.seq.lt_lh_iff.mpr (mem_domain_of_pair_mem h))
        (by simp [←hu]) h' h⟩

lemma result_defined : Model.DefinedFunction ℒₒᵣ 𝚺₁ (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → M) → M) p.resultDef := by
  intro v; simp [Formulae.resultDef, result_graph]
  apply exists_congr; intro x
  simp [c.cseq_defined_iff]

lemma result_defined_delta : Model.DefinedFunction ℒₒᵣ 𝚫₁ (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → M) → M) p.resultDeltaDef :=
  c.result_defined.graph_delta

@[simp] lemma result_defined_iff (v) :
    Semiformula.Evalbm M v p.resultDef.val ↔ v 0 = c.result (v ·.succ.succ) (v 1) := c.result_defined.df.iff v

instance result_definable : DefinableFunction ℒₒᵣ 𝚺₁ (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → M) → M) :=
  Defined.to_definable _ c.result_defined

instance result_definable_delta₁ : DefinableFunction ℒₒᵣ 𝚫₁ (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → M) → M) :=
  Defined.to_definable _ c.result_defined_delta

end Construction

end PR

section seqExp

lemma seqCons_le {x y s t : M} (hxy : x ≤ y) (hst : s ≤ t) :
    s ⁀' x ≤ t + exp ((2 * t + y + 1)^2) := by
  have : s ⁀' x ≤ t + exp ⟪2 * t, y⟫ := by
    simp [seqCons]; exact insert_le_of_le_of_le (pair_le_pair (le_trans (lh_bound s) (by simp [hst])) hxy) hst
  exact le_trans this (by simp)

lemma seqProduct_exists_unique (s a : M) : ∃! t : M, ∀ x, x ∈ t ↔ ∃ v ∈ s, ∃ u ∈ a, x = v ⁀' u := by
  have : 𝚺₁-Predicate fun x ↦ ∃ v ∈ s, ∃ u ∈ a, x = v ⁀' u := by definability
  exact finite_comprehension₁! this ⟨log s + exp ((2 * log s + log a + 1)^2) + 1, by
    rintro x ⟨v, hv, u, hu, rfl⟩
    exact lt_succ_iff_le.mpr <| seqCons_le (le_log_of_mem hu) (le_log_of_mem hv)⟩

def seqProduct (a s : M) : M := Classical.choose! (seqProduct_exists_unique a s)

infixl:60 " ×ˢ " => seqProduct

lemma mem_seqProduct_iff {x s a : M} : x ∈ s ×ˢ a ↔ ∃ v ∈ s, ∃ u ∈ a, x = v ⁀' u :=
  Classical.choose!_spec (seqProduct_exists_unique s a) x

lemma mem_seqProduct_iff' {u v a s : M} (Hv : Seq v) (Hs : ∀ w ∈ s, Seq w) :
    v ⁀' u ∈ s ×ˢ a ↔ v ∈ s ∧ u ∈ a :=
  ⟨by intro h
      rcases mem_seqProduct_iff.mp h with ⟨v', hv', u', hu', e⟩
      have : u = u' ∧ v = v' := by simpa [Hv, Hs v' hv'] using e
      rcases this with ⟨rfl, rfl⟩
      constructor <;> assumption,
   by rintro ⟨hv, hu⟩
      exact mem_seqProduct_iff.mpr ⟨v, hv, u, hu, rfl⟩⟩

lemma mem_seqProduct_bound {x s a : M} (h : x ∈ s ×ˢ a) : x ≤ s + exp ((2 * s + a + 1)^2) := by
  rcases mem_seqProduct_iff.mp h with ⟨v, hv, u, hu, rfl⟩
  exact seqCons_le (le_of_lt <| lt_of_mem hu) (le_of_lt <| lt_of_mem hv)

private lemma seqProduct_graph (t s a : M) : t = s ×ˢ a ↔ ∃ e, e = exp ((2 * s + a + 1)^2) ∧ ∀ x < t + s + e + 1, x ∈ t ↔ ∃ v ∈ s, ∃ u ∈ a, x = v ⁀' u :=
⟨by rintro rfl; exact ⟨exp ((2 * s + a + 1)^2), rfl, by intro x _; simp [mem_seqProduct_iff]⟩,
 by rintro ⟨_, rfl, h⟩
    apply mem_ext; intro x
    constructor
    · intro hx;
      exact mem_seqProduct_iff.mpr
        <| h x (lt_of_lt_of_le (lt_of_mem hx) (by simp [add_assoc])) |>.mp hx
    · intro hx
      exact h x (lt_succ_iff_le.mpr <| le_trans (mem_seqProduct_bound hx) <| by simp [add_assoc])
        |>.mpr (mem_seqProduct_iff.mp hx)⟩

def _root_.LO.FirstOrder.Arith.seqProductDef : 𝚺₁-Semisentence 3 := .mkSigma
  “∃ (!expDef.val [#0, (2 * #2 + #3 + 1 ) ^' 2] ∧
    ∀[#0 < #2 + #3 + #1 + 1] ( #0 ∈ #2 ↔ [∃∈ #3] [∃∈ #5] !seqConsDef.val [#2, #1, #0] ) )”
  (by simp [Hierarchy.iff_iff])

lemma seqProduct_defined : 𝚺₁-Function₂ (seqProduct : M → M → M) via seqProductDef := by
  intro v; simp [seqProductDef, seqProduct_graph]

@[simp] lemma seqProduct_defined_iff (v) :
    Semiformula.Evalbm M v seqProductDef.val ↔ v 0 = v 1 ×ˢ v 2 := seqProduct_defined.df.iff v

instance seqProduct_definable : 𝚺₁-Function₂ (seqProduct : M → M → M) := Defined.to_definable _ seqProduct_defined

def seqExp.formulae : PR.Formulae 1 where
  zero := .mkSigma “#0 = 1” (by simp)
  succ := .mkSigma “!seqProductDef.val [#0, #1, #3]” (by simp)

def seqExp.construction : PR.Construction M seqExp.formulae where
  zero := fun _ ↦ {∅}
  succ := fun a _ s ↦ s ×ˢ a 0
  zero_defined := by intro v; simp [formulae, one_eq_singleton]
  succ_defined := by intro v; simp [formulae]; rfl

def seqExp (a k : M) : M := seqExp.construction.result ![a] k

infix:80 " ^ˢ " => seqExp

@[simp] lemma seqExp_zero (a : M) : a ^ˢ 0 = {∅} := by simp [seqExp, seqExp.construction]

@[simp] lemma seqExp_succ (a k : M) : a ^ˢ (k + 1) = (a ^ˢ k) ×ˢ a := by simp [seqExp, seqExp.construction]

def _root_.LO.FirstOrder.Arith.seqExpDef : 𝚫₁-Semisentence 3 := seqExp.formulae.resultDef |>.rew (Rew.substs ![#0, #2, #1]) |>.graphDelta

lemma seqExp_defined : 𝚫₁-Function₂ (seqExp : M → M → M) via seqExpDef := by
  apply DefinedFunction.graph_delta <| fun v ↦ by simp [seqExp.construction.result_defined_iff]; rfl

@[simp] lemma seqExp_defined_iff (v) :
    Semiformula.Evalbm M v seqExpDef.val ↔ v 0 = v 1 ^ˢ v 2 := seqExp_defined.df.iff v

instance seqExp_definable : 𝚫₁-Function₂ (seqExp : M → M → M) := Defined.to_definable _ seqExp_defined

@[simp, definability] instance seqExp_definable' (Γ) : (Γ, 1)-Function₂ (seqExp : M → M → M) := .of_delta seqExp_definable

attribute [definability] DefinableFunction₂.comp

lemma seq_of_mem_seqExp {s a k : M} (h : s ∈ seqExp a k) : Seq s := by
  induction k using induction_iSigmaOne generalizing s
  · sorry
  case zero =>
    have : s = ∅ := by simpa using h
    simp [this]
  case succ k ih =>
    have : ∃ v ∈ a ^ˢ k, ∃ u ∈ a, s = v ⁀' u := by simpa [mem_seqProduct_iff] using h
    rcases this with ⟨v, hv, u, hu, rfl⟩
    exact (ih hv).seqCons u

end seqExp

end LO.FirstOrder.Arith.Model

end
