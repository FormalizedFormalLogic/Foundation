import Arithmetization.ISigmaOne.HFS.PRF

/-!

# Sequence

-/

noncomputable section

namespace LO.FirstOrder.Arith.Model

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

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

lemma seqCons_mem_seqProduct {u v a s : M} (hv : v ∈ s) (hu : u ∈ a) : v ⁀' u ∈ s ×ˢ a :=
  mem_seqProduct_iff.mpr (⟨v, hv, u, hu, rfl⟩)

lemma mem_seqProduct_bound {x s a : M} (h : x ∈ s ×ˢ a) : x ≤ s + exp ((2 * s + a + 1)^2) := by
  rcases mem_seqProduct_iff.mp h with ⟨v, hv, u, hu, rfl⟩
  exact seqCons_le (le_of_lt <| lt_of_mem hu) (le_of_lt <| lt_of_mem hv)

section

private lemma seqProduct_graph (t s a : M) :
    t = s ×ˢ a ↔ ∃ e, e = exp ((2 * s + a + 1)^2) ∧ ∀ x ≤ t + s + e, x ∈ t ↔ ∃ v ∈ s, ∃ u ∈ a, x = v ⁀' u :=
⟨by rintro rfl; exact ⟨exp ((2 * s + a + 1)^2), rfl, by intro x _; simp [mem_seqProduct_iff]⟩,
 by rintro ⟨_, rfl, h⟩
    apply mem_ext; intro x
    constructor
    · intro hx;
      exact mem_seqProduct_iff.mpr
        <| h x (le_trans (le_of_lt <| lt_of_mem hx) (by simp [add_assoc])) |>.mp hx
    · intro hx
      exact h x (le_trans (mem_seqProduct_bound hx) <| by simp [add_assoc])
        |>.mpr (mem_seqProduct_iff.mp hx)⟩

def _root_.LO.FirstOrder.Arith.seqProductDef : 𝚺₁-Semisentence 3 := .mkSigma
  “t s a | ∃ e, !expDef e (2 * s + a + 1)² ∧ ∀ x <⁺ t + s + e, x ∈ t ↔ ∃ v ∈' s, ∃ u ∈' a, !seqConsDef x v u”
  (by simp [Hierarchy.iff_iff])

lemma seqProduct_defined : 𝚺₁-Function₂ (seqProduct : M → M → M) via seqProductDef := by
  intro v; simp [seqProductDef, seqProduct_graph]

@[simp] lemma seqProduct_defined_iff (v) :
    Semiformula.Evalbm M v seqProductDef.val ↔ v 0 = v 1 ×ˢ v 2 := seqProduct_defined.df.iff v

instance seqProduct_definable : 𝚺₁-Function₂ (seqProduct : M → M → M) := Defined.to_definable _ seqProduct_defined

end

def seqExp.formulae : PR.Formulae 1 where
  zero := .mkSigma “y x | y = 1” (by simp)
  succ := .mkSigma “y ih n x | !seqProductDef y ih x” (by simp)

def seqExp.construction : PR.Construction M seqExp.formulae where
  zero := fun _ ↦ {∅}
  succ := fun a _ s ↦ s ×ˢ a 0
  zero_defined := by intro v; simp [formulae, one_eq_singleton (M := M)]
  succ_defined := by intro v; simp [formulae]; rfl

def seqExp (a k : M) : M := seqExp.construction.result ![a] k

infix:80 " ^ˢ " => seqExp

@[simp] lemma seqExp_zero (a : M) : a ^ˢ 0 = {∅} := by simp [seqExp, seqExp.construction]

@[simp] lemma seqExp_succ (a k : M) : a ^ˢ (k + 1) = (a ^ˢ k) ×ˢ a := by simp [seqExp, seqExp.construction]

def _root_.LO.FirstOrder.Arith.seqExpDef : 𝚺₁-Semisentence 3 := seqExp.formulae.resultDef |>.rew (Rew.substs ![#0, #2, #1])

lemma seqExp_defined : 𝚺₁-Function₂ (seqExp : M → M → M) via seqExpDef :=
  fun v ↦ by simp [seqExp.construction.result_defined_iff, seqExpDef]; rfl

@[simp] lemma seqExp_defined_iff (v) :
    Semiformula.Evalbm M v seqExpDef.val ↔ v 0 = v 1 ^ˢ v 2 := seqExp_defined.df.iff v

instance seqExp_definable : 𝚺₁-Function₂ (seqExp : M → M → M) := Defined.to_definable _ seqExp_defined

@[simp, definability] instance seqExp_definable' (Γ) : (Γ, m + 1)-Function₂ (seqExp : M → M → M) :=
  .of_sigmaOne seqExp_definable _ _

@[simp] lemma zero_ne_add_one (a : M) : 0 ≠ a + 1 := ne_of_lt (by simp)

lemma mem_seqExp_iff {s a k : M} : s ∈ a ^ˢ k ↔ Seq s ∧ lh s = k ∧ (∀ i z, ⟪i, z⟫ ∈ s → z ∈ a) := by
  induction k using induction_iPiOne generalizing s
  · suffices 𝚷₁-Predicate fun {k} => ∀ {s : M}, s ∈ a ^ˢ k ↔ Seq s ∧ lh s = k ∧ ∀ i < s, ∀ z < s, ⟪i, z⟫ ∈ s → z ∈ a
    by exact this.of_iff (fun k ↦
      forall_congr' <| fun s ↦ iff_congr (by rfl) <| and_congr (by rfl) <| and_congr (by rfl)
      ⟨fun h i hi z _ hiz ↦ h i z hiz, fun h i z hiz ↦ h i (lt_of_mem_dom hiz) z (lt_of_mem_rng hiz) hiz⟩)
    definability
  case zero =>
    simp only [seqExp_zero, mem_singleton_iff]
    constructor
    · rintro rfl; simp
    · rintro ⟨H, hs, _⟩
      exact H.isempty_of_lh_eq_zero hs
  case succ k ih =>
    simp only [seqExp_succ]
    constructor
    · intro hs
      have : ∃ v ∈ a ^ˢ k, ∃ u ∈ a, s = v ⁀' u := by simpa [mem_seqProduct_iff] using hs
      rcases this with ⟨v, hv, u, hu, rfl⟩
      have : Seq v ∧ lh v = k ∧ ∀ i z, ⟪i, z⟫ ∈ v → z ∈ a := @ih v |>.mp hv
      rcases this with ⟨Hv, hvk, hv⟩
      exact ⟨Hv.seqCons u, by simp [Hv, hvk], by
        intro i z hiz
        have : i = k ∧ z = u ∨ ⟪i, z⟫ ∈ v := by simpa [hvk] using mem_seqCons_iff.mp hiz
        rcases this with (⟨_, rfl⟩ | hiz)
        · exact hu
        · exact hv i z hiz⟩
    · rintro ⟨Hs, hsk, hs⟩
      have : s = ∅ ∨ ∃ x s', Seq s' ∧ s = s' ⁀' x := Seq.cases_iff.mp Hs
      rcases this with (rfl | ⟨x, s, Hs', rfl⟩)
      · simp [eq_comm] at hsk
      · have hsk : lh s = k := by simpa [Hs'] using hsk
        have hx : x ∈ a := hs k x (by simp [←hsk])
        have hs : s ∈ a ^ˢ k := @ih s |>.mpr ⟨Hs', hsk, fun i z hiz ↦ hs i z (Seq.subset_seqCons s x hiz)⟩
        exact seqCons_mem_seqProduct hs hx

lemma seq_of_mem_seqExp {s a k : M} (h : s ∈ a ^ˢ k) : Seq s := (mem_seqExp_iff.mp h).1

lemma lh_of_mem_seqExp {s a k : M} (h : s ∈ a ^ˢ k) : lh s = k := (mem_seqExp_iff.mp h).2.1

lemma pair_mem_mem_seqExp {s a k : M} (h : s ∈ a ^ˢ k) {i z} (hiz : ⟪i, z⟫ ∈ s) : z ∈ a := (mem_seqExp_iff.mp h).2.2 i z hiz

end seqExp

end LO.FirstOrder.Arith.Model

end
