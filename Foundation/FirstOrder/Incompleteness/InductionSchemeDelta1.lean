module

public import Foundation.FirstOrder.Incompleteness.First
public import Foundation.FirstOrder.Incompleteness.Second

/-!
# $\Delta_1$-definability of the induction schemata, and of `𝗜𝚺₁` and `𝗣𝗔`

This file discharges the two `axiom`s that previously sat in `Examples.lean`:
`PA_delta1Definable : 𝗣𝗔.Δ₁` and `ISigma1_delta1Definable : 𝗜𝚺₁.Δ₁`.

The route:

```
𝗣𝗔  = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ
𝗜𝚺₁ = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ (Arithmetic.Hierarchy 𝚺 1)
```

`𝗣𝗔⁻` is a finite set of sentences, so `Theory.Δ₁.ofFinite` gives `𝗣𝗔⁻.Δ₁`.
`Theory.Δ₁.add`/`.ofEq` then reduce both headline instances to the single obligation
`(InductionScheme ℒₒᵣ C).Δ₁`, which is the mathematical content of this file.
-/

@[expose] public section

-- #794 removed the formula-level `SyntacticSemiformula`/`SyntacticFormula` aliases, so this file
-- uses the expanded `_root_.LO.FirstOrder.Semiformula L ℕ n` spelling instead of re-exporting those names.

namespace LO.FirstOrder.Arithmetic.Bootstrapping

/-! ## Internal iterated universal quantifier `qqAlls`

`qqAlls p k = ^∀ ^∀ … ^∀ p` (`k` quantifiers), the internal counterpart of the meta universal
closure `∀⁰*`. This is part (a) of arithmetizing `univCl` (part (b), the free→bound `fixitr`
rewrite, is still open). The headline of this section is `quote_allClosure`:
`⌜∀⁰* φ⌝ = qqAlls ⌜φ⌝ n`. -/

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section qqAlls

def qqAlls.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. !qqAllDef y ih”

noncomputable def qqAlls.construction : PR.Construction V qqAlls.blueprint where
  zero := fun x ↦ x 0
  succ := fun _ _ ih ↦ ^∀ ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, qqAll]

/-- `qqAlls p k = ^∀ ^∀ ... ^∀ p` (`k` universal quantifiers). -/
noncomputable def qqAlls (p k : V) : V := qqAlls.construction.result ![p] k

@[simp] lemma qqAlls_zero (p : V) : qqAlls p 0 = p := by simp [qqAlls, qqAlls.construction]

@[simp] lemma qqAlls_succ (p k : V) : qqAlls p (k + 1) = ^∀ (qqAlls p k) := by
  simp [qqAlls, qqAlls.construction]

section

def _root_.LO.FirstOrder.Arithmetic.qqAllsDef : 𝚺₁.Semisentence 3 :=
  qqAlls.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance qqAlls_defined : 𝚺₁-Function₂ (qqAlls : V → V → V) via qqAllsDef := .mk
  fun v ↦ by simp [qqAlls.construction.result_defined_iff, qqAllsDef]; rfl

instance qqAlls_definable : 𝚺₁-Function₂ (qqAlls : V → V → V) := qqAlls_defined.to_definable

instance qqAlls_definable' (Γ) : Γ-[m + 1]-Function₂ (qqAlls : V → V → V) := qqAlls_definable.of_sigmaOne

end

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma le_qqAll (p : V) : p ≤ ^∀ p := by
  simp only [qqAll]; exact le_trans (le_pair_right _ _) le_self_add

/-- `^∀` commutes through the closure -/
lemma qqAlls_all (p k : V) : qqAlls (^∀ p) k = ^∀ (qqAlls p k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqAlls_succ, ih, qqAlls_succ]

/-- pushing one more `^∀` onto the body equals one more layer of closure -/
lemma qqAlls_succ' (p k : V) : qqAlls p (k + 1) = qqAlls (^∀ p) k := by
  rw [qqAlls_succ, qqAlls_all]

@[simp] lemma le_qqAlls (p k : V) : p ≤ qqAlls p k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    refine le_trans ih ?_
    rw [qqAlls_succ]
    exact le_qqAll _

lemma succ_le_qqAll (p : V) : p + 1 ≤ ^∀ p := by
  simp only [qqAll]; exact add_le_add (le_pair_right _ _) (le_refl 1)

/-- the number of quantifiers is bounded by the closure code (bounds `∃ m ≤ p`) -/
@[simp] lemma index_le_qqAlls (p k : V) : k ≤ qqAlls p k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    rw [qqAlls_succ]
    exact le_trans (add_le_add ih (le_refl 1)) (succ_le_qqAll _)

@[simp] lemma isUFormula_qqAlls {p k : V} : IsUFormula L (qqAlls p k) ↔ IsUFormula L p := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqAlls_succ, IsUFormula.all, ih]

lemma bv_qqAlls {p k : V} (hp : IsUFormula L p) : bv L (qqAlls p k) = bv L p - k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    rw [qqAlls_succ, bv_all (isUFormula_qqAlls.mpr hp), ih, Arithmetic.sub_sub]

/-- closing `k` variables of an `(n+k)`-formula yields an `n`-formula -/
lemma IsSemiformula.qqAlls {n k p : V} (h : IsSemiformula L (n + k) p) :
    IsSemiformula L n (qqAlls p k) := by
  rw [isSemiformula_iff] at h ⊢
  obtain ⟨hu, hbv⟩ := h
  refine ⟨isUFormula_qqAlls.mpr hu, ?_⟩
  rw [bv_qqAlls hu, tsub_le_iff_right]
  exact hbv

/-- The internal iterated-`^∀` computes the universal-closure code:
`⌜∀⁰* φ⌝ = qqAlls ⌜φ⌝ n`. -/
lemma quote_allClosure {n : ℕ} (φ : _root_.LO.FirstOrder.Semiformula L ℕ n) :
    (⌜(∀⁰* φ : _root_.LO.FirstOrder.Semiformula L ℕ 0)⌝ : V) = qqAlls (⌜φ⌝ : V) (n : V) := by
  induction n
  case zero => simp
  case succ n ih =>
    rw [show (∀⁰* φ : _root_.LO.FirstOrder.Semiformula L ℕ 0) = ∀⁰* (∀⁰ φ) from rfl]
    have := ih (∀⁰ φ)
    rw [Semiformula.quote_all] at this
    rw [this, Nat.cast_succ, qqAlls_succ']

/-- The Gödel code of a sentence `univCl ψ` agrees with that of its 0-ary semiformula
unfolding `univCl' ψ` (which prepends `fvSup ψ` universals to the `fixitr`-rewritten body). -/
lemma quote_univCl (ψ : _root_.LO.FirstOrder.Semiformula L ℕ 0) :
    (⌜Semiformula.univCl ψ⌝ : V) = (⌜Semiformula.univCl' ψ⌝ : V) := by
  show (⌜(Rewriting.emb (Semiformula.univCl ψ) : _root_.LO.FirstOrder.Semiformula L ℕ 0)⌝ : V) = ⌜Semiformula.univCl' ψ⌝
  congr 1
  simp [Semiformula.univCl]

/-- `⌜univCl' ψ⌝ = qqAlls ⌜fixitr 0 (fvSup ψ) ▹ ψ⌝ (fvSup ψ)`: the universal closure is the
internal iterated-`^∀` applied to the freevar-free `fixitr`-image of `ψ`. -/
lemma quote_univCl' (ψ : _root_.LO.FirstOrder.Semiformula L ℕ 0) :
    (⌜Semiformula.univCl' ψ⌝ : V)
      = qqAlls (⌜(Rew.fixitr 0 ψ.fvSup ▹ ψ : _root_.LO.FirstOrder.Semiformula L ℕ (0 + ψ.fvSup))⌝ : V)
          ((0 + ψ.fvSup : ℕ) : V) := by
  rw [Semiformula.univCl']; exact quote_allClosure _

/-- Combined: the code of the universal closure of `ψ`. -/
lemma quote_univCl_eq (ψ : _root_.LO.FirstOrder.Semiformula L ℕ 0) :
    (⌜Semiformula.univCl ψ⌝ : V)
      = qqAlls (⌜(Rew.fixitr 0 ψ.fvSup ▹ ψ : _root_.LO.FirstOrder.Semiformula L ℕ (0 + ψ.fvSup))⌝ : V)
          ((0 + ψ.fvSup : ℕ) : V) := by
  rw [quote_univCl, quote_univCl']

/-- **Closure inversion at the code level.** Substituting the free-variable atoms `&0 … &(m-1)`
back into the `fixitr`-image recovers `⌜φ⌝`. This is the DECODE direction: the recognizer can
recover `⌜succInd ψ⌝` (hence `ψ`) from the freevar-free closure body using the *already-proven*
internal `subst`, with no need for an internal `fixitr`. Meta witness: `subst_comp_fixitr`. -/
lemma quote_subst_fvar_fixitr (φ : _root_.LO.FirstOrder.Semiformula L ℕ 0) :
    (⌜(Rew.fixitr 0 φ.fvSup ▹ φ : _root_.LO.FirstOrder.Semiformula L ℕ (0 + φ.fvSup))
        ⇜ (fun x : Fin (0 + φ.fvSup) ↦ (&↑x : SyntacticTerm L))⌝ : V) = ⌜φ⌝ := by
  rw [show (Rew.fixitr 0 φ.fvSup ▹ φ : _root_.LO.FirstOrder.Semiformula L ℕ (0 + φ.fvSup))
        ⇜ (fun x : Fin (0 + φ.fvSup) ↦ (&↑x : SyntacticTerm L)) = φ from by
    have := Semiformula.subst_comp_fixitr (L := L) φ
    convert this using 2]

end qqAlls

/-- **Sup attained.** The largest free-variable index of `φ` is `fvSup φ - 1` (when `φ` has free
variables). Together with `lt_fvSup_of_fvar?` this pins `fvSup` as exactly the count of universals
in `univCl'`, and is what the recognizer's `bv b = m` clause checks (no over-recognition by padding
leading `∀`s). -/
lemma _root_.LO.FirstOrder.Semiformula.fvar?_fvSup_pred {L : Language} {n : ℕ}
    (φ : _root_.LO.FirstOrder.Semiformula L ℕ n) (h : 0 < φ.fvSup) : φ.FVar? (φ.fvSup - 1) := by
  by_cases he : φ.freeVariables = ∅
  · simp [Semiformula.fvSup, he] at h
  · obtain ⟨k, hk⟩ := Finset.max_of_nonempty (Finset.nonempty_iff_ne_empty.mpr he)
    rw [show φ.fvSup = k + 1 from by simp [Semiformula.fvSup, hk]]
    simpa using Finset.mem_of_max hk

/-! ## `castLE`-invariance of the Gödel code and free variables

Raising the de Bruijn level of a (semi)term/(semi)formula by `Rew.castLE` changes neither its raw
Gödel code (the underlying variable indices are preserved) nor its set of free variables. These are
the bookkeeping lemmas behind the `bv`-pin bridge below: an `IsSemiformula j`-witness of a code that
"really" sits at level `n ≥ j` factors through `castLE`, letting us read off the free-variable
budget. -/

section castLE

variable {L : Language} [L.Encodable] [L.LORDefinable]

private lemma semitermVec_val_congr {k m m' : ℕ}
    (g : Fin k → Bootstrapping.Semiterm V L m) (g' : Fin k → Bootstrapping.Semiterm V L m')
    (h : ∀ i, (g i).val = (g' i).val) :
    Bootstrapping.SemitermVec.val g = Bootstrapping.SemitermVec.val g' := by
  unfold Bootstrapping.SemitermVec.val
  congr 1
  funext i
  exact h i

lemma _root_.LO.FirstOrder.Semiterm.quote_castLE {n : ℕ} (t : SyntacticSemiterm L n) :
    ∀ {n' : ℕ} (h : n ≤ n'), (⌜(Rew.castLE h t : SyntacticSemiterm L n')⌝ : V) = ⌜t⌝ := by
  induction t with
  | bvar x => intro n' h; simp
  | fvar x => intro n' h; simp
  | func f v ih =>
      intro n' h
      simp only [Rew.func, Semiterm.quote_func, Function.comp_apply]
      rw [semitermVec_val_congr (fun i ↦ ⌜Rew.castLE h (v i)⌝) (fun i ↦ ⌜v i⌝)
        (fun i ↦ by rw [← Semiterm.quote_def, ← Semiterm.quote_def]; exact ih i h)]

omit [L.Encodable] [L.LORDefinable] in
lemma _root_.LO.FirstOrder.Semiterm.freeVariables_castLE {n : ℕ} (t : SyntacticSemiterm L n) :
    ∀ {n' : ℕ} (h : n ≤ n'), (Rew.castLE h t : SyntacticSemiterm L n').freeVariables = t.freeVariables := by
  induction t with
  | bvar x => intro n' h; simp
  | fvar x => intro n' h; simp
  | func f v ih =>
      intro n' h
      simp only [Rew.func, Semiterm.freeVariables_func]
      apply Finset.biUnion_congr rfl
      intro i _; exact ih i h

lemma _root_.LO.FirstOrder.Semiformula.quote_castLE {n : ℕ} (φ : _root_.LO.FirstOrder.Semiformula L ℕ n) :
    ∀ {n' : ℕ} (h : n ≤ n'), (⌜(Rew.castLE h ▹ φ : _root_.LO.FirstOrder.Semiformula L ℕ n')⌝ : V) = ⌜φ⌝ := by
  induction φ using Semiformula.rec' with
  | hverum => intro n' h; simp
  | hfalsum => intro n' h; simp
  | hrel r v =>
      intro n' h
      simp only [Semiformula.rew_rel, Semiformula.quote_rel]
      rw [semitermVec_val_congr (fun i ↦ ⌜Rew.castLE h (v i)⌝) (fun i ↦ ⌜v i⌝)
        (fun i ↦ by rw [← Semiterm.quote_def, ← Semiterm.quote_def]; exact Semiterm.quote_castLE _ h)]
  | hnrel r v =>
      intro n' h
      simp only [Semiformula.rew_nrel, Semiformula.quote_nrel]
      rw [semitermVec_val_congr (fun i ↦ ⌜Rew.castLE h (v i)⌝) (fun i ↦ ⌜v i⌝)
        (fun i ↦ by rw [← Semiterm.quote_def, ← Semiterm.quote_def]; exact Semiterm.quote_castLE _ h)]
  | hand φ ψ ihp ihq => intro n' h; simp only [LogicalConnective.HomClass.map_and, Semiformula.quote_and, ihp h, ihq h]
  | hor φ ψ ihp ihq => intro n' h; simp only [LogicalConnective.HomClass.map_or, Semiformula.quote_or, ihp h, ihq h]
  | hall φ ih => intro n' h; rw [Rewriting.app_all, Semiformula.quote_all, Rew.q_castLE, ih, Semiformula.quote_all]
  | hexs φ ih => intro n' h; rw [Rewriting.app_exs, Semiformula.quote_ex, Rew.q_castLE, ih, Semiformula.quote_ex]

omit [L.Encodable] [L.LORDefinable] in
lemma _root_.LO.FirstOrder.Semiformula.freeVariables_castLE {n : ℕ} (φ : _root_.LO.FirstOrder.Semiformula L ℕ n) :
    ∀ {n' : ℕ} (h : n ≤ n'), (Rew.castLE h ▹ φ : _root_.LO.FirstOrder.Semiformula L ℕ n').freeVariables = φ.freeVariables := by
  induction φ using Semiformula.rec' with
  | hverum => intro n' h; simp
  | hfalsum => intro n' h; simp
  | hrel r v =>
      intro n' h
      simp only [Semiformula.rew_rel, Semiformula.freeVariables_rel]
      apply Finset.biUnion_congr rfl; intro i _; exact Semiterm.freeVariables_castLE _ h
  | hnrel r v =>
      intro n' h
      simp only [Semiformula.rew_nrel, Semiformula.freeVariables_nrel]
      apply Finset.biUnion_congr rfl; intro i _; exact Semiterm.freeVariables_castLE _ h
  | hand φ ψ ihp ihq => intro n' h; simp only [LogicalConnective.HomClass.map_and, Semiformula.freeVariables_and, ihp h, ihq h]
  | hor φ ψ ihp ihq => intro n' h; simp only [LogicalConnective.HomClass.map_or, Semiformula.freeVariables_or, ihp h, ihq h]
  | hall φ ih => intro n' h; simp only [Rewriting.app_all, Semiformula.freeVariables_all, Rew.q_castLE, ih]
  | hexs φ ih => intro n' h; simp only [Rewriting.app_exs, Semiformula.freeVariables_exs, Rew.q_castLE, ih]

end castLE

/-! ## The `bv`-pin bridge

The recognizer pins the number of leading universals `m` to `fvSup` of the core formula via a clause
forcing `bv b = m`. Soundness of that pin rests on the bridge below: the freevar-free universal-closure
body uses *exactly* `fvSup χ` bound slots, so closing fewer than `fvSup χ` quantifiers cannot reach a
sentence — forbidding over-recognition by vacuous leading `∀`s. -/

section bvPin

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- **`bv`-pin bridge** (over ℕ): `bv ⌜fixitr 0 (fvSup χ) ▹ χ⌝ = fvSup χ`.
- `≤` is immediate from `quote_univCl_eq` + `bv_qqAlls` (closing `fvSup` quantifiers reaches a
  sentence, whose `bv` is `0`).
- `≥` is by level-factoring: were the body an `IsSemiformula j` for some `j < fvSup`, `IsSemiformula.sound`
  + `castLE`-invariance would re-express `χ` as `γ ⇜ ![&0, …, &(j-1)]` with `γ` free-variable-free,
  forcing `fvSup χ ≤ j < fvSup χ`. -/
lemma bv_quote_fixitr (χ : _root_.LO.FirstOrder.Semiformula L ℕ 0) :
    bv (V := ℕ) L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.Semiformula L ℕ (0 + χ.fvSup))⌝ : ℕ)
      = χ.fvSup := by
  -- the freevar-free closure body
  have not_fvar_body : ∀ x, ¬(Rew.fixitr 0 χ.fvSup ▹ χ).FVar? x := by
    intro x
    rw [Rew.eq_bind (Rew.fixitr 0 χ.fvSup)]
    simp only [Function.comp_def, Rew.fixitr_bvar, Rew.fixitr_fvar, Fin.natAdd_mk, zero_add]
    intro hh
    rcases Semiformula.fvar?_rew hh with (⟨z, hz⟩ | ⟨z, hz, hx⟩)
    · simp at hz
    · have : z < χ.fvSup := Semiformula.lt_fvSup_of_fvar? hz
      simp [this] at hx
  have hbsemi := Semiformula.quote_isSemiformula (V := ℕ)
    (Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.Semiformula L ℕ (0 + χ.fvSup))
  have hbU : IsUFormula L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.Semiformula L ℕ (0 + χ.fvSup))⌝ : ℕ) :=
    hbsemi.isUFormula
  -- `≤` direction: the body has `0 + fvSup` bound slots, so `bv ≤ fvSup` (model order over ℕ).
  -- On ℕ the model cast is the identity (`natCast_nat`) and `<` is `Nat.lt`.
  have hle := hbsemi.bv_le
  simp only [Nat.zero_add, natCast_nat] at hle
  -- the model `≤` on ℕ unfolds to `= ∨ <` with `<` the standard `Nat.lt`
  rcases (hle : bv (V := ℕ) L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.Semiformula L ℕ (0 + χ.fvSup))⌝ : ℕ)
      = χ.fvSup ∨ bv (V := ℕ) L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.Semiformula L ℕ (0 + χ.fvSup))⌝ : ℕ)
      < χ.fvSup) with heq | hlt
  · exact heq
  -- `hlt : bv ⌜body⌝ < χ.fvSup` ; this case is impossible (forbids vacuous leading `∀`s)
  exfalso
  set j := bv (V := ℕ) L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.Semiformula L ℕ (0 + χ.fvSup))⌝ : ℕ) with hj
  have hpos : 0 < χ.fvSup := by omega
  have hsemi : IsSemiformula L j (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.Semiformula L ℕ (0 + χ.fvSup))⌝ : ℕ) := by
    have := IsUFormula.isSemiformula hbU; rwa [← hj] at this
  obtain ⟨γ, hγ⟩ := IsSemiformula.sound hsemi
  have hjle : j ≤ 0 + χ.fvSup := by omega
  -- codes agree across levels, hence the formulas agree
  have hcast : (Rew.castLE hjle ▹ γ : _root_.LO.FirstOrder.Semiformula L ℕ (0 + χ.fvSup))
      = (Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.Semiformula L ℕ (0 + χ.fvSup)) := by
    apply (Semiformula.quote_inj_iff (V := ℕ)).mp
    rw [Semiformula.quote_castLE, hγ]
  -- `γ` is free-variable-free
  have hγfree : γ.freeVariables = ∅ := by
    have hb : (Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.Semiformula L ℕ (0 + χ.fvSup)).freeVariables = ∅ :=
      Finset.eq_empty_of_forall_notMem fun x hx ↦ not_fvar_body x hx
    have := Semiformula.freeVariables_castLE γ hjle
    rw [hcast, hb] at this; exact this.symm
  -- invert the closure: `χ = γ ⇜ ![&0, …, &(j-1)]`
  have hχeq : χ = γ ⇜ (fun i : Fin j ↦ (&↑i : SyntacticTerm L)) := by
    have e1 : (Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.Semiformula L ℕ (0 + χ.fvSup))
        ⇜ (fun x : Fin (0 + χ.fvSup) ↦ (&↑x : SyntacticTerm L)) = χ := Semiformula.subst_comp_fixitr χ
    have hRewEq : (Rew.subst (fun x : Fin (0 + χ.fvSup) ↦ (&↑x : SyntacticTerm L))).comp (Rew.castLE hjle)
        = Rew.subst (fun i : Fin j ↦ (&↑i : SyntacticTerm L)) := by
      ext x <;> simp [Rew.comp_app]
    symm
    rw [← e1, ← hcast]
    unfold Rewriting.subst
    rw [← TransitiveRewriting.comp_app, hRewEq]
  -- contradiction: `&(fvSup-1)` occurs in `χ`, but the inversion bounds free vars by `j ≤ fvSup-1`
  have hfv : (γ ⇜ (fun i : Fin j ↦ (&↑i : SyntacticTerm L))).FVar? (χ.fvSup - 1) := by
    rw [← hχeq]; exact Semiformula.fvar?_fvSup_pred χ hpos
  unfold Rewriting.subst at hfv
  rcases Semiformula.fvar?_rew hfv with (⟨i, hi⟩ | ⟨z, hz, _⟩)
  · have hib : χ.fvSup - 1 = (i : ℕ) := by
      simpa [Rew.subst_bvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] using hi
    have hij := i.isLt
    omega
  · simp [Semiformula.FVar?, hγfree] at hz

end bvPin

/-! ## Internal free-variable vector `fvarVec`

`fvarVec k = ⟨^&0, ^&1, …, ^&(k-1)⟩`, the code of the substitution vector mapping bound var `#i`
to free var `&i`. The recognizer applies `subst (fvarVec m) ·` to invert the universal closure
(undo `fixitr`), recovering `⌜succInd ψ⌝` from the freevar-free body — see `quote_subst_fvar_fixitr`.
This is a `𝚺₁` vector recursion (`fvarVec (k+1) = concat (fvarVec k) (^&k)`). -/

section fvarVec

def fvarVec.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. y = 0”
  succ := .mkSigma “y ih n. ∃ f, !qqFvarDef f n ∧ !concatDef y ih f”

noncomputable def fvarVec.construction : PR.Construction V fvarVec.blueprint where
  zero := fun _ ↦ 0
  succ := fun _ n ih ↦ concat ih (^&n)
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

/-- `fvarVec k = ⟨^&0, …, ^&(k-1)⟩`. -/
noncomputable def fvarVec (k : V) : V := fvarVec.construction.result ![] k

@[simp] lemma fvarVec_zero : fvarVec (0 : V) = 0 := by simp [fvarVec, fvarVec.construction]

@[simp] lemma fvarVec_succ (k : V) : fvarVec (k + 1) = concat (fvarVec k) (^&k) := by
  simp [fvarVec, fvarVec.construction]

def _root_.LO.FirstOrder.Arithmetic.fvarVecDef : 𝚺₁.Semisentence 2 := fvarVec.blueprint.resultDef

instance fvarVec_defined : 𝚺₁-Function₁ (fvarVec : V → V) via fvarVecDef := .mk
  fun v ↦ by simp [fvarVec.construction.result_defined_iff, fvarVecDef]; rfl

instance fvarVec_definable : 𝚺₁-Function₁ (fvarVec : V → V) := fvarVec_defined.to_definable

instance fvarVec_definable' (Γ) : Γ-[m + 1]-Function₁ (fvarVec : V → V) := fvarVec_definable.of_sigmaOne

@[simp] lemma len_fvarVec (k : V) : len (fvarVec k) = k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => simp [ih]

/-- `fvarVec k` is the vector with `i`-th entry `^&i` for `i < k`. -/
lemma nth_fvarVec (k : V) : ∀ i < k, (fvarVec k).[i] = ^&i := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    intro i hi
    rcases (lt_succ_iff_le.mp hi).lt_or_eq with hlt | rfl
    · rw [fvarVec_succ, concat_nth_lt _ _ (by simpa using hlt)]; exact ih i hlt
    · rw [fvarVec_succ, concat_nth_len' _ _ (by simp)]

/-- `fvarVec` is the code of the typed substitution vector `fun i ↦ ^&i` (over a standard length). -/
lemma fvarVec_val_eq (m : ℕ) :
    fvarVec ((m : ℕ) : V)
      = SemitermVec.val (fun i : Fin m ↦ (Semiterm.fvar (↑(i : ℕ)) : Bootstrapping.Semiterm V ℒₒᵣ 0)) := by
  apply nth_ext (by simp)
  intro i hi
  rw [len_fvarVec] at hi
  obtain ⟨j, rfl⟩ := eq_nat_of_lt_nat hi
  have hj : j < m := by exact_mod_cast hi
  rw [nth_fvarVec _ _ hi, show ((j : ℕ) : V) = ((⟨j, hj⟩ : Fin m) : ℕ) from rfl]
  rw [SemitermVec.val_nth_eq (fun i : Fin m ↦ (Semiterm.fvar (↑(i : ℕ)) : Bootstrapping.Semiterm V ℒₒᵣ 0)) ⟨j, hj⟩]
  simp

/-- **Raw closure inversion.** `subst (fvarVec (fvSup φ)) ⌜fixitr 0 (fvSup φ) ▹ φ⌝ = ⌜φ⌝`: the
internal substitution by `fvarVec` undoes the universal-closure `fixitr` at the code level. This
is the recognizer's mechanism for recovering `⌜succInd ψ⌝` from the freevar-free closure body. -/
lemma subst_fvarVec_quote (φ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 0) :
    Bootstrapping.subst ℒₒᵣ (fvarVec ((0 + φ.fvSup : ℕ) : V))
        (⌜(Rew.fixitr 0 φ.fvSup ▹ φ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + φ.fvSup))⌝ : V)
      = (⌜φ⌝ : V) := by
  set Kt : Bootstrapping.Semiformula V ℒₒᵣ (0 + φ.fvSup) :=
    ⌜(Rew.fixitr 0 φ.fvSup ▹ φ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + φ.fvSup))⌝ with hKt
  set w : SemitermVec V ℒₒᵣ (0 + φ.fvSup) 0 :=
    (fun i : Fin (0 + φ.fvSup) ↦ (Semiterm.fvar (↑(i : ℕ)) : Bootstrapping.Semiterm V ℒₒᵣ 0)) with hw
  rw [fvarVec_val_eq,
    show (⌜(Rew.fixitr 0 φ.fvSup ▹ φ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + φ.fvSup))⌝ : V) = Kt.val from rfl,
    show Bootstrapping.subst ℒₒᵣ w.val Kt.val = (Kt.subst w).val from rfl,
    ← quote_subst_fvar_fixitr (V := V) φ]
  congr 1
  rw [hKt]
  simp only [FirstOrder.Semiformula.typed_quote_substs, hw, Semiterm.typed_quote_fvar]

/-- **Generalized free-ization.** For *any* `β : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ m`, substituting the
free-variable atoms `&0 … &(m-1)` for its `m` bound slots equals `⌜β ⇜ (&·)⌝`. This is the forward
recognizer's tool: once `IsSemiformula.sound` yields a `β` with `⌜β⌝ = b`, this computes
`subst (fvarVec m) b`. (Specializes to `subst_fvarVec_quote` when `β` is a `fixitr`-image.) -/
lemma subst_fvarVec_quote' {m : ℕ} (β : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ m) :
    Bootstrapping.subst ℒₒᵣ (fvarVec ((m : ℕ) : V)) (⌜β⌝ : V)
      = (⌜(β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)))⌝ : V) := by
  set Kt : Bootstrapping.Semiformula V ℒₒᵣ m := ⌜β⌝ with hKt
  set w : SemitermVec V ℒₒᵣ m 0 :=
    (fun i : Fin m ↦ (Semiterm.fvar (↑(i : ℕ)) : Bootstrapping.Semiterm V ℒₒᵣ 0)) with hw
  rw [fvarVec_val_eq,
    show (⌜β⌝ : V) = Kt.val from rfl,
    show Bootstrapping.subst ℒₒᵣ w.val Kt.val = (Kt.subst w).val from rfl]
  rw [show (⌜(β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)))⌝ : V)
      = (⌜(β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)))⌝ : Bootstrapping.Semiformula V ℒₒᵣ 0).val from rfl]
  congr 1
  rw [hKt]
  simp only [FirstOrder.Semiformula.typed_quote_substs, hw, Semiterm.typed_quote_fvar]

end fvarVec

/-! ## Σ₁ side condition: internal `IsSigma1` predicate (for `C = Hierarchy 𝚺 1`)

`IsSigma1 p` recognizes codes of `𝚺₁` formulas over `ℒₒᵣ`. By `Hierarchy.sigma₁_induction'`, over
`ℒₒᵣ` a formula is `𝚺₁` iff built from atoms (`=,≠,<,≮,⊤,⊥`) by `∧`, `∨`, (unbounded) `∃`, and
**bounded `∀`** `∀⁰[“#0 < !!(bShift t)”] φ`, whose body desugars to `(^#0 ^≮ u) ^⋎ φ` with
`u = termBShift t`. The recognizer is applied to a code already known to be a semiformula, so atoms
are matched purely structurally (no `IsUTermVec` guard). Positivity (`u` is a `bShift`-image) is
`Δ₁`: `termBShift` only grows codes (`le_termBShift`), so `∃ t < u+1, u = termBShift t` is a
*bounded* `∃` over the `Δ₁` graph `termBShiftGraph`. -/

section isSigma1

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- `termBShift` only grows codes: `t ≤ termBShift t` for well-formed terms. The `^#z → ^#(z+1)`
bvar shift grows, `^&x` is fixed, and functions recurse componentwise. Bounds the `∃ t` guard in
the bounded-`∀` clause. -/
lemma le_termBShift {t : V} (ht : IsUTerm L t) : t ≤ termBShift L t := by
  refine IsUTerm.induction 𝚺 (P := fun t ↦ t ≤ termBShift L t) ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z
    rw [termBShift_bvar]
    simp only [qqBvar]
    exact add_le_add (pair_le_pair_right (0 : V) le_self_add) (le_refl 1)
  · intro x; simp
  · intro k f v hf hv ih
    rw [termBShift_func hf hv]
    have hvle : v ≤ termBShiftVec L k v := by
      refine le_of_nth_le_nth ?_ ?_
      · rw [len_termBShiftVec hv]; exact hv.1.symm
      · intro i hi
        rw [← hv.1] at hi
        rw [nth_termBShiftVec hv hi]
        exact ih i hi
    simp only [qqFunc]
    exact add_le_add
      (pair_le_pair_right 2 (pair_le_pair_right k (pair_le_pair_right f hvle))) (le_refl 1)

lemma IsUTerm.termBShift {t : V} (ht : IsUTerm L t) : IsUTerm L (termBShift L t) :=
  (ht.isSemiterm.termBShift).isUTerm

lemma IsUTermVec.termBShiftVec {k v : V} (hv : IsUTermVec L k v) :
    IsUTermVec L k (termBShiftVec L k v) :=
  ⟨(len_termBShiftVec hv).symm, fun i hi => by
    rw [nth_termBShiftVec hv hi]; exact (hv.nth hi).termBShift⟩

/-- `termBShift` shifts the bound-variable depth up by exactly one (on well-formed terms): so `t` is
a level-`m` term iff `termBShift t` is level-`(m+1)`. The `←`-direction recovers the lowered arity,
which is how the bounded-`∀` bound (a `termBShift`-image) is recognized as a `bShift` of a real term
of the outer arity. -/
lemma termBV_termBShift_le {t : V} (ht : IsUTerm L t) (m : V) :
    termBV L (termBShift L t) ≤ m + 1 ↔ termBV L t ≤ m := by
  refine IsUTerm.induction 𝚺 (P := fun t ↦ termBV L (termBShift L t) ≤ m + 1 ↔ termBV L t ≤ m)
    ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp only [termBShift_bvar, termBV_bvar]; exact add_le_add_iff_right 1
  · intro x; simp only [termBShift_fvar, termBV_fvar]; exact iff_of_true zero_le zero_le
  · intro k f v hf hv ih
    rw [termBShift_func hf hv, termBV_func hf hv.termBShiftVec, termBV_func hf hv,
      listMaxss_le_iff, listMaxss_le_iff]
    constructor
    · intro H i hi
      rw [len_termBVVec hv] at hi
      rw [nth_termBVVec hv hi, ← ih i hi]
      have := H i (by rw [len_termBVVec hv.termBShiftVec]; exact hi)
      rwa [nth_termBVVec hv.termBShiftVec hi, nth_termBShiftVec hv hi] at this
    · intro H i hi
      rw [len_termBVVec hv.termBShiftVec] at hi
      rw [nth_termBVVec hv.termBShiftVec hi, nth_termBShiftVec hv hi, ih i hi]
      have := H i (by rw [len_termBVVec hv]; exact hi)
      rwa [nth_termBVVec hv hi] at this

/-- Internal bounded-`∀` code: `qqBall u q = ^∀ ((^#0 ^≮ u) ^⋎ q)`, the code of `∀⁰[“#0 < u”] q`.
Packaged as a single `𝚺₁`-function (mirroring `qqNLT`/`qqRel`) so the `IsSigma1` fixpoint clause is
flat. -/
noncomputable def qqBall (u q : V) : V := qqAll (qqOr (Arithmetic.qqNLT (qqBvar 0) u) q)

@[simp] lemma lt_q_qqBall (u q : V) : q < qqBall u q :=
  lt_trans (lt_or_right _ _) (lt_forall _)

@[simp] lemma lt_u_qqBall (u q : V) : u < qqBall u q :=
  lt_trans (Arithmetic.lt_qqNLT_right _ _) (lt_trans (lt_or_left _ _) (lt_forall _))

def _root_.LO.FirstOrder.Arithmetic.qqBallDef : 𝚺₁.Semisentence 3 := .mkSigma
  “p u q. ∃ bv, !qqBvarDef bv 0 ∧ ∃ nlt, !qqNLTDef nlt bv u ∧ ∃ g, !qqOrDef g nlt q ∧ !qqAllDef p g”

instance qqBall_defined : 𝚺₁-Function₂ (qqBall : V → V → V) via Arithmetic.qqBallDef := .mk fun v ↦ by
  simp [Arithmetic.qqBallDef, qqBall, (Arithmetic.qqNLT_defined (V := V)).df]

instance qqBall_definable (Γ m) : Γ-[m + 1]-Function₂ (qqBall : V → V → V) :=
  .of_sigmaOne qqBall_defined.to_definable

namespace IsSigma1F

/-- Single-step operator: `p` is `𝚺₁` given that its immediate subformulas in `C` are. Atoms carry
no well-formedness guard (the recognizer is applied to a code already known to be a semiformula);
the bounded-`∀` clause requires the bound `u` to be a `termBShift`-image of a well-formed term. -/
def Phi (C : Set V) (p : V) : Prop :=
  (p = ^⊤) ∨
  (p = ^⊥) ∨
  (∃ k r v, p = ^rel k r v) ∨
  (∃ k r v, p = ^nrel k r v) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
  (∃ p₁, p₁ ∈ C ∧ p = ^∃ p₁) ∨
  (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C ∧ p = qqBall u q)

private lemma phi_iff (C p : V) :
    Phi {x | x ∈ C} p ↔
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, p = ^rel k r v) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, p = ^nrel k r v) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ p = ^∃ p₁) ∨
    (∃ u < p, ∃ q < p, (∃ t < p, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C
        ∧ p = qqBall u q) where
  mp := by
    rintro (rfl | rfl | ⟨k, r, v, rfl⟩ | ⟨k, r, v, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩
      | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, hp, rfl⟩ | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩)
    · tauto
    · tauto
    · exact Or.inr (Or.inr (Or.inl ⟨k, by simp, r, by simp, v, by simp, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, by simp, r, by simp, v, by simp, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, by simp, p₂, by simp, hp, hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, by simp, p₂, by simp, hp, hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, by simp, hp, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨termBShift ℒₒᵣ t, lt_u_qqBall _ _, q, lt_q_qqBall _ _,
          ⟨t, lt_of_le_of_lt (le_termBShift ht) (lt_u_qqBall _ _), ht, rfl⟩, hq, rfl⟩))))))
  mpr := by
    unfold Phi
    rintro (rfl | rfl | ⟨k, _, r, _, v, _, rfl⟩ | ⟨k, _, r, _, v, _, rfl⟩
      | ⟨p₁, _, p₂, _, hp, hq, rfl⟩ | ⟨p₁, _, p₂, _, hp, hq, rfl⟩ | ⟨p₁, _, hp, rfl⟩
      | ⟨u, _, q, _, ⟨t, _, ht, rfl⟩, hq, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl ⟨k, r, v, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, r, v, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, p₂, hp, hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, p₂, hp, hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, hp, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨termBShift ℒₒᵣ t, q, ⟨t, ht, rfl⟩, hq, rfl⟩))))))

noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “p C.
    !qqVerumDef p ∨ !qqFalsumDef p ∨
    (∃ k < p, ∃ r < p, ∃ v < p, !qqRelDef p k r v) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, !qqNRelDef p k r v) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqAndDef p p₁ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqOrDef p p₁ p₂) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ !qqExsDef p p₁) ∨
    (∃ u < p, ∃ q < p,
       (∃ t < p, !(isUTerm ℒₒᵣ).sigma t ∧ !(termBShiftGraph ℒₒᵣ) u t) ∧ q ∈ C
       ∧ !qqBallDef p u q)”)
  (.mkPi “p C.
    !qqVerumDef p ∨ !qqFalsumDef p ∨
    (∃ k < p, ∃ r < p, ∃ v < p, !qqRelDef p k r v) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, !qqNRelDef p k r v) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqAndDef p p₁ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqOrDef p p₁ p₂) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ !qqExsDef p p₁) ∨
    (∃ u < p, ∃ q < p,
       (∃ t < p, !(isUTerm ℒₒᵣ).pi t ∧ ∀ u', !(termBShiftGraph ℒₒᵣ) u' t → u = u') ∧ q ∈ C
       ∧ ∀ p', !qqBallDef p' u q → p = p')”)⟩

def construction : Fixpoint.Construction V blueprint where
  Φ := fun _ ↦ Phi
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, HierarchySymbol.Semiformula.val_sigma, eq_comm,
        (termBShift.defined (L := ℒₒᵣ) (V := V)).df, (qqBall_defined (V := V)).df]
    · intro v
      symm
      simpa [blueprint, HierarchySymbol.Semiformula.val_sigma, eq_comm,
        (termBShift.defined (L := ℒₒᵣ) (V := V)).df, (qqBall_defined (V := V)).df]
        using phi_iff (V := V) _ _
  monotone := by
    unfold Phi
    rintro C C' hC _ x (h | h | h | h | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩
      | ⟨p₁, hp, rfl⟩ | ⟨u, q, ht, hq, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, p₂, hC hp, hC hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, p₂, hC hp, hC hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, hC hp, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨u, q, ht, hC hq, rfl⟩))))))

instance : construction.StrongFinite V where
  strong_finite := by
    unfold construction Phi
    rintro C _ x (h | h | h | h | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩
      | ⟨p₁, hp, rfl⟩ | ⟨u, q, ht, hq, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p₁, p₂, ⟨hp, by simp⟩, ⟨hq, by simp⟩, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p₁, p₂, ⟨hp, by simp⟩, ⟨hq, by simp⟩, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, ⟨hp, by simp⟩, rfl⟩))))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨u, q, ht, ⟨hq, ?_⟩, rfl⟩))))))
      exact lt_q_qqBall _ _

end IsSigma1F

/-- `IsSigma1 p`: `p` codes a `𝚺₁` formula over `ℒₒᵣ` (assuming `p` is a semiformula). -/
def IsSigma1 (p : V) : Prop := IsSigma1F.construction.Fixpoint ![] p

/-- Concrete `𝚫₁`-recognizer for `IsSigma1`. -/
noncomputable def isSigma1 : 𝚫₁.Semisentence 1 := IsSigma1F.blueprint.fixpointDefΔ₁

instance IsSigma1.defined : 𝚫₁-Predicate (IsSigma1 (V := V)) via isSigma1 :=
  IsSigma1F.construction.fixpoint_definedΔ₁

lemma IsSigma1.case_iff {p : V} :
    IsSigma1 p ↔
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ k r v, p = ^rel k r v) ∨
    (∃ k r v, p = ^nrel k r v) ∨
    (∃ p₁ p₂, IsSigma1 p₁ ∧ IsSigma1 p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, IsSigma1 p₁ ∧ IsSigma1 p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ p₁, IsSigma1 p₁ ∧ p = ^∃ p₁) ∨
    (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsSigma1 q
        ∧ p = qqBall u q) :=
  IsSigma1F.construction.case

alias ⟨IsSigma1.case, IsSigma1.mk⟩ := IsSigma1.case_iff

@[simp] lemma IsSigma1.verum : IsSigma1 (V := V) (^⊤) := IsSigma1.mk (Or.inl rfl)
@[simp] lemma IsSigma1.falsum : IsSigma1 (V := V) (^⊥) := IsSigma1.mk (Or.inr (Or.inl rfl))
@[simp] lemma IsSigma1.rel {k r v : V} : IsSigma1 (^rel k r v) :=
  IsSigma1.mk (Or.inr (Or.inr (Or.inl ⟨k, r, v, rfl⟩)))
@[simp] lemma IsSigma1.nrel {k r v : V} : IsSigma1 (^nrel k r v) :=
  IsSigma1.mk (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, r, v, rfl⟩))))

@[simp] lemma IsSigma1.and_iff {p q : V} : IsSigma1 (p ^⋏ q) ↔ IsSigma1 p ∧ IsSigma1 q := by
  constructor
  · intro h
    rcases h.case with (h | h | ⟨_,_,_,h⟩ | ⟨_,_,_,h⟩ | ⟨p₁,p₂,hp,hq,h⟩ | ⟨_,_,_,_,h⟩ | ⟨_,_,h⟩ | ⟨u,q',_,_,h⟩) <;>
      simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqExs, qqAll, qqBall] at h
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨hp, hq⟩
  · rintro ⟨hp, hq⟩
    exact IsSigma1.mk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, hp, hq, rfl⟩)))))

@[simp] lemma IsSigma1.or_iff {p q : V} : IsSigma1 (p ^⋎ q) ↔ IsSigma1 p ∧ IsSigma1 q := by
  constructor
  · intro h
    rcases h.case with (h | h | ⟨_,_,_,h⟩ | ⟨_,_,_,h⟩ | ⟨_,_,_,_,h⟩ | ⟨p₁,p₂,hp,hq,h⟩ | ⟨_,_,h⟩ | ⟨u,q',_,_,h⟩) <;>
      simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqExs, qqAll, qqBall] at h
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨hp, hq⟩
  · rintro ⟨hp, hq⟩
    exact IsSigma1.mk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, hp, hq, rfl⟩))))))

@[simp] lemma IsSigma1.ex_iff {p : V} : IsSigma1 (^∃ p) ↔ IsSigma1 p := by
  constructor
  · intro h
    rcases h.case with (h | h | ⟨_,_,_,h⟩ | ⟨_,_,_,h⟩ | ⟨_,_,_,_,h⟩ | ⟨_,_,_,_,h⟩ | ⟨p₁,hp,h⟩ | ⟨u,q',_,_,h⟩) <;>
      simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqExs, qqAll, qqBall] at h
    · obtain rfl := h; exact hp
  · rintro hp
    exact IsSigma1.mk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩)))))))

/-- Inversion of the bounded-`∀` clause: a `^∀`-headed `𝚺₁` code is a `qqBall`. -/
lemma IsSigma1.of_all {p : V} (h : IsSigma1 (^∀ p)) :
    ∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsSigma1 q
      ∧ p = qqOr (Arithmetic.qqNLT (qqBvar 0) u) q := by
  rcases h.case with (h | h | ⟨_,_,_,h⟩ | ⟨_,_,_,h⟩ | ⟨_,_,_,_,h⟩ | ⟨_,_,_,_,h⟩ | ⟨_,_,h⟩
    | ⟨u, q, hguard, hq, h⟩)
  · exact absurd h (by simp [qqAll, qqVerum])
  · exact absurd h (by simp [qqAll, qqFalsum])
  · exact absurd h (by simp [qqAll, qqRel])
  · exact absurd h (by simp [qqAll, qqNRel])
  · exact absurd h (by simp [qqAll, qqAnd])
  · exact absurd h (by simp [qqAll, qqOr])
  · exact absurd h (by simp [qqAll, qqExs])
  · rw [show qqBall u q = ^∀ (qqOr (Arithmetic.qqNLT (qqBvar 0) u) q) from rfl, qqAll_inj] at h
    exact ⟨u, q, hguard, hq, h⟩

end isSigma1

end LO.FirstOrder.Arithmetic.Bootstrapping

namespace LO.FirstOrder.Arithmetic

open LO.FirstOrder.Theory

/-! ## B1 — `𝗣𝗔⁻` is `Δ₁` (it is finite) -/

noncomputable instance PeanoMinus.delta1 : (𝗣𝗔⁻ : ArithmeticTheory).Δ₁ :=
  Theory.Δ₁.ofFinite _ PeanoMinus.finite

/-! ## Typed decomposition of `succInd`

The crux relates the code `⌜univCl (succInd φ)⌝` to internal primitives. The macro `!φ t` in
formula position desugars to `φ ⇜ ![t]` (`Rew.substs`, **not** `embSubsts` as an earlier handoff
claimed), so `⌜succInd φ⌝` collapses under the *already-present* `typed_quote_substs`/`map_imply`/
`LCWQIsoGödelQuote.all` simp set — no `typed_quote_embSubsts` bridge is needed. -/

section succInd

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `succInd φ`, simplified (the `∀ x, !φ x` instances are the identity substitution `φ ⇜ ![#0]`). -/
lemma succInd_eq (φ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 1) :
    succInd φ =
      ((φ ⇜ (![‘0’] : Fin 1 → ArithmeticSemiterm ℕ 0))
        🡒 ((∀⁰ (φ 🡒 (φ ⇜ (![‘#0 + 1’] : Fin 1 → ArithmeticSemiterm ℕ 1)))) 🡒 ∀⁰ φ)) := by
  unfold succInd; simp

/-- The typed Gödel code of the induction axiom body, built from the typed code `⌜φ⌝` purely with
the existing typed constructors (`subst`, `🡒`, `∀⁰`). -/
lemma typed_quote_succInd (φ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 1) :
    (⌜succInd φ⌝ : Bootstrapping.Semiformula V ℒₒᵣ 0) =
      (⌜φ ⇜ (![‘0’] : Fin 1 → ArithmeticSemiterm ℕ 0)⌝)
        🡒 ((∀⁰ (⌜φ⌝ 🡒 ⌜φ ⇜ (![‘#0 + 1’] : Fin 1 → ArithmeticSemiterm ℕ 1)⌝)) 🡒 ∀⁰ ⌜φ⌝) := by
  unfold succInd
  rw [show φ ⇜ (![#0] : Fin 1 → ArithmeticSemiterm ℕ 1) = φ from by simp]
  simp

/-- The typed `succInd` shape as a function of the (typed) core code `K = ⌜ψ⌝`. The recognizer
checks `subst (fvarVec m) b = (indBody K).val` to recover the core `K` and verify the body has
the induction-axiom shape. -/
noncomputable def indBody (K : Bootstrapping.Semiformula V ℒₒᵣ 1) : Bootstrapping.Semiformula V ℒₒᵣ 0 :=
  (K.subst ![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝])
    🡒 ((∀⁰ (K 🡒 K.subst ![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝])) 🡒 ∀⁰ K)

/-- `indBody ⌜ψ⌝ = ⌜succInd ψ⌝`: the typed reconstruction matches the actual code. -/
lemma indBody_quote (φ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 1) :
    indBody (⌜φ⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1) = ⌜succInd φ⌝ := by
  rw [typed_quote_succInd]; unfold indBody; simp [Matrix.constant_eq_singleton]

/-- The raw `V → V` form of `(indBody ·).val` — a composition of the `𝚺₁`-definable internal
operations `subst`, `imp` (`p ^→ q = ∼p ^⋎ q`), `^∀`. This is the function the recognizer's clause
`subst (fvarVec m) b = indBodyVal K` uses (`K` a code with `IsSemiformula ℒₒᵣ 1 K`); it is the
target of the eventual `𝚺₁`-graph for the `ch` assembly. -/
noncomputable def indBodyVal (k : V) : V :=
  Bootstrapping.imp ℒₒᵣ
    (Bootstrapping.subst ℒₒᵣ
      (Bootstrapping.SemitermVec.val (![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝] : Bootstrapping.SemitermVec V ℒₒᵣ 1 0)) k)
    (Bootstrapping.imp ℒₒᵣ
      (Bootstrapping.qqAll (Bootstrapping.imp ℒₒᵣ k
        (Bootstrapping.subst ℒₒᵣ
          (Bootstrapping.SemitermVec.val (![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝] : Bootstrapping.SemitermVec V ℒₒᵣ 1 1)) k)))
      (Bootstrapping.qqAll k))

/-- `indBodyVal K.val = (indBody K).val`: the raw function computes the typed `indBody`. -/
lemma indBodyVal_eq (K : Bootstrapping.Semiformula V ℒₒᵣ 1) : indBodyVal K.val = (indBody K).val := by
  simp only [indBodyVal, indBody, Bootstrapping.Semiformula.val_imp, Bootstrapping.Semiformula.val_all,
    Bootstrapping.Semiformula.val_substs]

/-- `k ≤ indBodyVal k`: the core `k` sits as the bound body of the `^∀ k` conclusion inside the
`succInd` shape, so its code is below the whole axiom's code. This is the *clean half* of the old
size race — it bounds the recovered core `K` by the (functionally pinned) `subst (fvarVec m) b`,
which equals `indBodyVal K`. -/
lemma le_indBodyVal (k : V) : k ≤ indBodyVal k := by
  unfold indBodyVal Bootstrapping.imp
  exact (Bootstrapping.le_qqAll _).trans
    (le_of_lt ((Bootstrapping.lt_or_right _ _).trans (Bootstrapping.lt_or_right _ _)))

/-- `indBodyVal ⌜γ⌝ = ⌜succInd γ⌝`: the raw recognizer body computes the `succInd` shape. -/
lemma indBodyVal_quote (γ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 1) : indBodyVal (⌜γ⌝ : ℕ) = (⌜succInd γ⌝ : ℕ) := by
  rw [show (⌜γ⌝ : ℕ) = (⌜γ⌝ : Bootstrapping.Semiformula ℕ ℒₒᵣ 1).val from rfl, indBodyVal_eq,
    indBody_quote]
  rfl

instance indBodyVal_definable : 𝚺₁-Function₁ (indBodyVal : V → V) := by
  unfold indBodyVal
  definability

/-! ### A concrete `𝚺₁`-graph for `indBodyVal`

The `definability` tactic above only gives a `Prop`-level `Definable` witness; the `ch` assembly
needs an *extractable* `𝚺₁.Semisentence` with a `via` correctness instance, mirroring `impGraph` /
`iffGraph`. The two substitution constants are the standard codes of the closed substitution
vectors `![⌜‘0’⌝]` and `![⌜‘#0+1’⌝]`; their absoluteness (`↑constant = SemitermVec.val …`) is
`LO.FirstOrder.Semiterm.quote_eq_encode'`. -/

/-- Standard `ℕ`-code of the substitution vector `![⌜‘0’⌝]` (the `ψ(0)` instance). -/
def indSubstConst0 : ℕ :=
  Matrix.vecToNat fun i : Fin 1 ↦ Encodable.encode ((![(‘0’ : ArithmeticSemiterm ℕ 0)]) i)

/-- Standard `ℕ`-code of the substitution vector `![⌜‘#0+1’⌝]` (the `ψ(x+1)` instance). -/
def indSubstConst1 : ℕ :=
  Matrix.vecToNat fun i : Fin 1 ↦ Encodable.encode ((![(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)]) i)

lemma val_indSubstConst0 :
    (↑indSubstConst0 : V)
      = Bootstrapping.SemitermVec.val (![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝] : Bootstrapping.SemitermVec V ℒₒᵣ 1 0) := by
  rw [indSubstConst0, ← LO.FirstOrder.Semiterm.quote_eq_encode' (V := V) (![(‘0’ : ArithmeticSemiterm ℕ 0)])]
  congr 1; funext i; simp [Matrix.cons_val_fin_one]

lemma val_indSubstConst1 :
    (↑indSubstConst1 : V)
      = Bootstrapping.SemitermVec.val (![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝] : Bootstrapping.SemitermVec V ℒₒᵣ 1 1) := by
  rw [indSubstConst1, ← LO.FirstOrder.Semiterm.quote_eq_encode' (V := V) (![(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)])]
  congr 1; funext i; simp [Matrix.cons_val_fin_one]

/-- Concrete `𝚺₁`-graph of `indBodyVal`, a chain of the `subst`/`imp`/`qqAll` graphs. -/
noncomputable def indBodyValGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y k.
    ∃ a, !(Bootstrapping.substsGraph ℒₒᵣ) a ↑indSubstConst0 k ∧
    ∃ s1, !(Bootstrapping.substsGraph ℒₒᵣ) s1 ↑indSubstConst1 k ∧
    ∃ i1, !(Bootstrapping.impGraph ℒₒᵣ) i1 k s1 ∧
    ∃ qa1, !qqAllDef qa1 i1 ∧
    ∃ qak, !qqAllDef qak k ∧
    ∃ i2, !(Bootstrapping.impGraph ℒₒᵣ) i2 qa1 qak ∧
    !(Bootstrapping.impGraph ℒₒᵣ) y a i2”

instance indBodyVal.defined : 𝚺₁-Function₁ (indBodyVal : V → V) via indBodyValGraph := .mk fun v ↦ by
  simp [indBodyValGraph, numeral_eq_natCast, val_indSubstConst0, val_indSubstConst1, indBodyVal]

end succInd

/-! ## The crux — the induction schema is `Δ₁`

We build a concrete recognizer `ch : 𝚫₁.Semisentence 1` whose ℕ-extension recognizes exactly the
codes `⌜univCl (succInd ψ)⌝`. The recognizer:
```
R(p) := ∃ m ≤ p, ∃ b ≤ p,
   p = qqAlls b m  ∧  IsUFormula b ∧ shift b = b  ∧  bv b = m
 ∧ ∃ K ≤ subst (fvarVec m) b, IsSemiformula 1 K
   ∧ subst (fvarVec m) b = indBodyVal K
```
`bv b = m` pins `m = fvSup`, forbidding over-recognition by padding leading `∀`s
(`bv_quote_fixitr`); the last clause recovers `⌜succInd ψ⌝` from the freevar-free body `b`. -/

section ch

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open Bootstrapping

/-- The recognizer predicate for `InductionScheme ℒₒᵣ Set.univ` over a model `V`. -/
def InductionUnivR (p : V) : Prop :=
  ∃ m ≤ p, ∃ b ≤ p,
    p = qqAlls b m ∧ IsUFormula ℒₒᵣ b ∧ shift ℒₒᵣ b = b ∧ bv ℒₒᵣ b = m
    ∧ ∃ K ≤ subst ℒₒᵣ (fvarVec m) b,
        IsSemiformula ℒₒᵣ 1 K ∧ subst ℒₒᵣ (fvarVec m) b = indBodyVal K

end ch

/-- Concrete `𝚫₁.Semisentence 1` recognizer for the universal induction scheme. -/
noncomputable def chUniv : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “p.
    ∃ m < p + 1, ∃ b < p + 1,
      !qqAllsDef p b m ∧ !(Bootstrapping.isUFormula ℒₒᵣ).sigma b
      ∧ !(Bootstrapping.shiftGraph ℒₒᵣ) b b ∧ !(Bootstrapping.bvGraph ℒₒᵣ) m b
      ∧ ∃ fv, !fvarVecDef fv m ∧ ∃ s, !(Bootstrapping.substsGraph ℒₒᵣ) s fv b
        ∧ ∃ K < s + 1, !(Bootstrapping.isSemiformula ℒₒᵣ).sigma 1 K ∧ !indBodyValGraph s K”)
  (.mkPi “p.
    ∃ m < p + 1, ∃ b < p + 1,
      (∀ y, !qqAllsDef y b m → y = p) ∧ !(Bootstrapping.isUFormula ℒₒᵣ).pi b
      ∧ (∀ y, !(Bootstrapping.shiftGraph ℒₒᵣ) y b → y = b) ∧ (∀ y, !(Bootstrapping.bvGraph ℒₒᵣ) y b → y = m)
      ∧ ∀ fv, !fvarVecDef fv m → ∀ s, !(Bootstrapping.substsGraph ℒₒᵣ) s fv b
        → ∃ K < s + 1, !(Bootstrapping.isSemiformula ℒₒᵣ).pi 1 K ∧ ∀ ib, !indBodyValGraph ib K → s = ib”)

section chDefined

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open Bootstrapping

instance InductionUnivR.defined : 𝚫₁-Predicate[V] (InductionUnivR : V → Prop) via chUniv := .mk <| by
  constructor
  · intro v; simp [chUniv, HierarchySymbol.Semiformula.val_sigma, eq_comm]
  · intro v
    simp [chUniv, HierarchySymbol.Semiformula.val_sigma, InductionUnivR,
      lt_succ_iff_le, eq_comm]

end chDefined

/-! ## The crux — the induction schema is `Δ₁` -/

/-- RHS of `chUniv_mem_iff` reduced to a clean `∃ψ` over the *syntactic* universal closure. -/
lemma mem_inductionScheme_univ_iff (φ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 0) :
    (∃ σ ∈ InductionScheme ℒₒᵣ Set.univ, φ = (σ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 0))
      ↔ ∃ ψ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 1, φ = (succInd ψ).univCl' := by
  simp only [InductionScheme, Set.mem_setOf_eq]
  constructor
  · rintro ⟨σ, ⟨ψ, -, rfl⟩, rfl⟩
    exact ⟨ψ, by simp [Semiformula.coe_univCl_eq_univCl']⟩
  · rintro ⟨ψ, rfl⟩
    exact ⟨Semiformula.univCl (succInd ψ), ⟨ψ, trivial, rfl⟩,
      by simp [Semiformula.coe_univCl_eq_univCl']⟩

/-- **Closure inversion (forward keystone).** A freevar-free level-`m` formula `β` whose internal
`bv` is `m` and which substitutes back to `succInd γ` is exactly the `fixitr`-image, so its
`m`-fold closure is `(succInd γ).univCl'`. Mirror of `bv_quote_fixitr`'s `≥`-direction inversion;
the genuine remaining math. -/
theorem closure_inversion {m : ℕ} (β : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ m) (γ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 1)
    (hfree : β.freeVariables = ∅) (hbv : Bootstrapping.bv (V := ℕ) ℒₒᵣ (⌜β⌝ : ℕ) = m)
    (hβγ : β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)) = succInd γ) :
    (∀⁰* β : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 0) = (succInd γ).univCl' := by
  set χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 0 := succInd γ with hχ
  -- (*) code-level: `⌜fixitr 0 m ▹ χ⌝ = ⌜β⌝` (rebind composite = castLE on freevar-free β; codes
  -- erase the level index, sidestepping the `0 + m` vs `m` cast)
  have hcodeβ : (⌜(Rew.fixitr 0 m ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + m))⌝ : ℕ) = ⌜β⌝ := by
    have hcompcast :
        ((Rew.fixitr 0 m).comp (Rew.subst (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)))) ▹ β
          = (Rew.castLE (Nat.le_add_left m 0) ▹ β : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + m)) := by
      apply Semiformula.rew_eq_of_funEqOn
      · intro x; simp [Rew.comp_app, Rew.fixitr_fvar, Fin.ext_iff]
      · intro x hx; rw [Semiformula.FVar?, hfree] at hx; simp at hx
    have heq : (Rew.fixitr 0 m ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + m))
        = (Rew.castLE (Nat.le_add_left m 0) ▹ β : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + m)) := by
      rw [← hcompcast, TransitiveRewriting.comp_app,
        show (Rew.subst (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)) ▹ β) = χ from hβγ]
    rw [heq, Semiformula.quote_castLE (V := ℕ) β (Nat.le_add_left m 0)]
  -- free vars of `χ = β ⇜ (&·)` are all `< m`, so `χ.fvSup ≤ m`
  have hfvbound : ∀ x, χ.FVar? x → x < m := by
    intro x hx
    rw [show χ = β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)) from hβγ.symm] at hx
    rcases Semiformula.fvar?_rew hx with (⟨i, hi⟩ | ⟨z, hz, _⟩)
    · have : x = (↑i : ℕ) := by
        simpa [Rew.subst_bvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] using hi
      rw [this]; exact i.isLt
    · rw [Semiformula.FVar?, hfree] at hz; simp at hz
  have hfvle : χ.fvSup ≤ m := by
    rcases Nat.eq_zero_or_pos χ.fvSup with h0 | hpos
    · omega
    · have := hfvbound (χ.fvSup - 1) (Semiformula.fvar?_fvSup_pred χ hpos); omega
  -- (A) `m = χ.fvSup`: `fixitr 0 m ▹ χ` shares the *code* of `fixitr 0 χ.fvSup ▹ χ` (castLE), whose
  -- `bv` is `χ.fvSup` (bv_quote_fixitr); but `bv ⌜β⌝ = m` (hbv), and `⌜β⌝ = ⌜fixitr 0 m ▹ χ⌝`.
  have hcast_eq : (Rew.fixitr 0 m ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + m))
      = (Rew.castLE (by omega : (0 + χ.fvSup) ≤ (0 + m))
          ▹ (Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + χ.fvSup))) := by
    rw [← TransitiveRewriting.comp_app]
    apply Semiformula.rew_eq_of_funEqOn₀
    intro x hx
    have hxlt : x < χ.fvSup := Semiformula.lt_fvSup_of_fvar? hx
    simp [Rew.comp_app, Rew.fixitr_fvar, hxlt, show x < m from by omega]
  have hcode : (⌜(Rew.fixitr 0 m ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + m))⌝ : ℕ)
      = ⌜(Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + χ.fvSup))⌝ := by
    rw [hcast_eq, Semiformula.quote_castLE (V := ℕ)
      (Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + χ.fvSup)) (by omega)]
  have hm : m = χ.fvSup := by
    rw [← hbv, ← hcodeβ, hcode]; exact Bootstrapping.bv_quote_fixitr χ
  -- conclude via codes: `⌜∀⁰* β⌝ = qqAlls ⌜β⌝ m = qqAlls ⌜fixitr 0 χ.fvSup ▹ χ⌝ (0+χ.fvSup) = ⌜χ.univCl'⌝`
  apply (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp
  rw [Bootstrapping.quote_allClosure (V := ℕ) β, Semiformula.univCl',
    Bootstrapping.quote_allClosure (V := ℕ) (Rew.fixitr 0 χ.fvSup ▹ χ), ← hcodeβ, hcode, hm]
  simp

/-- **mem_iff math (C = univ).** The recognizer fires on `⌜φ⌝` exactly when `φ` is the universal
closure of `succInd ψ` for some one-variable `ψ`. Forward inverts via `IsSemiformula.sound` +
`closure_inversion`; backward composes `quote_univCl'`/`subst_fvarVec_quote'`/`indBodyVal_quote`. -/
theorem chUniv_mem_iff (φ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 0) :
    InductionUnivR (⌜φ⌝ : ℕ) ↔ ∃ σ ∈ InductionScheme ℒₒᵣ Set.univ, φ = (σ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 0) := by
  rw [mem_inductionScheme_univ_iff]
  constructor
  · -- forward: recognizer fires ⟹ φ is an induction axiom
    rintro ⟨m, -, b, -, hp, hU, hsh, hbv, K, -, hKsemi, hsubst⟩
    obtain ⟨γ, rfl⟩ := Bootstrapping.IsSemiformula.sound hKsemi
    have hbsemi : Bootstrapping.IsSemiformula ℒₒᵣ m b := hbv ▸ hU.isSemiformula
    obtain ⟨β, rfl⟩ := Bootstrapping.IsSemiformula.sound hbsemi
    refine ⟨γ, ?_⟩
    -- (1) `β ⇜ (&·) = succInd γ`
    have hβγ : β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)) = succInd γ := by
      apply (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp
      have e := Bootstrapping.subst_fvarVec_quote' (V := ℕ) β
      simp only [natCast_nat] at e
      rw [← e, hsubst, indBodyVal_quote]
    -- (2) `β` is freevar-free (from `shift ⌜β⌝ = ⌜β⌝`)
    have hβfree : β.freeVariables = ∅ := by
      have hsβ : Rewriting.shift β = β :=
        (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp
          (by rw [Semiformula.quote_shift (V := ℕ) β]; exact hsh)
      -- every free var `x` of `β` (= shift β) has a free predecessor `x-1`, so the minimum descends
      have step : ∀ x, β.FVar? x → 1 ≤ x ∧ β.FVar? (x - 1) := by
        intro x hx
        rw [← hsβ] at hx
        rcases Semiformula.fvar?_rew hx with (⟨i, hi⟩ | ⟨z, hz, hi⟩)
        · simp [Rew.shift_bvar, Semiterm.FVar?] at hi
        · have hxz : x = z + 1 := by
            simpa [Rew.shift_fvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] using hi
          exact ⟨by omega, by rw [hxz]; simpa using hz⟩
      by_contra hne
      classical
      have hnem := Finset.nonempty_of_ne_empty hne
      obtain ⟨hge, hpred⟩ := step (β.freeVariables.min' hnem) (β.freeVariables.min'_mem hnem)
      exact absurd (β.freeVariables.min'_le _ hpred) (by omega)
    -- (3) `φ = ∀⁰* β`
    have hφ : φ = (∀⁰* β : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 0) := by
      apply (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp
      rw [hp, Bootstrapping.quote_allClosure (V := ℕ) β]; simp
    rw [hφ]
    exact closure_inversion β γ hβfree hbv hβγ
  · -- backward: φ = univCl'(succInd ψ) ⟹ recognizer fires
    rintro ⟨ψ, rfl⟩
    set χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 0 := succInd ψ with hχ
    set b : ℕ := (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + χ.fvSup))⌝ : ℕ) with hb
    have hcode : (⌜χ.univCl'⌝ : ℕ) = Bootstrapping.qqAlls b ((0 + χ.fvSup : ℕ)) := by
      rw [hb, Bootstrapping.quote_univCl' (V := ℕ) χ]; simp
    -- `s := subst (fvarVec m) b = indBodyVal ⌜ψ⌝ = ⌜succInd ψ⌝`, computed once and reused.
    have hs : Bootstrapping.subst ℒₒᵣ (Bootstrapping.fvarVec (0 + χ.fvSup : ℕ)) b
        = indBodyVal (⌜ψ⌝ : ℕ) := by
      rw [hb]
      have hsub := Bootstrapping.subst_fvarVec_quote' (V := ℕ)
        (Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + χ.fvSup))
      simp only [natCast_nat] at hsub
      rw [hsub, Bootstrapping.quote_subst_fvar_fixitr χ,
        show (⌜ψ⌝ : ℕ) = (⌜ψ⌝ : Bootstrapping.Semiformula ℕ ℒₒᵣ 1).val from rfl,
        indBodyVal_eq, indBody_quote, hχ]
      rfl
    refine ⟨(0 + χ.fvSup : ℕ), ?_, b, ?_, ?_, ?_, ?_, ?_, (⌜ψ⌝ : ℕ), ?_, ?_, ?_⟩
    · rw [hcode]; exact Bootstrapping.index_le_qqAlls _ _
    · rw [hcode]; exact Bootstrapping.le_qqAlls _ _
    · exact hcode
    · rw [hb]
      exact (Semiformula.quote_isSemiformula (V := ℕ)
        (Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + χ.fvSup))).isUFormula
    · -- shift b = b: the closure body is freevar-free, so meta `shift` fixes it
      rw [hb]
      have hnf : ∀ x, ¬(Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + χ.fvSup)).FVar? x := by
        intro x
        rw [Rew.eq_bind (Rew.fixitr 0 χ.fvSup)]
        simp only [Function.comp_def, Rew.fixitr_bvar, Rew.fixitr_fvar, Fin.natAdd_mk, zero_add]
        intro hh
        rcases Semiformula.fvar?_rew hh with (⟨z, hz⟩ | ⟨z, hz, hx⟩)
        · simp at hz
        · have : z < χ.fvSup := Semiformula.lt_fvSup_of_fvar? hz
          simp [this] at hx
      have hshift : Rewriting.shift (Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + χ.fvSup))
          = (Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + χ.fvSup)) :=
        Semiformula.rew_eq_self_of (by simp) (fun x hx ↦ absurd hx (hnf x))
      rw [← Semiformula.quote_shift (V := ℕ)
        (Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + χ.fvSup)), hshift]
    · rw [hb]; exact (Bootstrapping.bv_quote_fixitr χ).trans (zero_add _).symm
    · -- `K = ⌜ψ⌝ ≤ subst (fvarVec m) b = indBodyVal ⌜ψ⌝` — the clean half: `ψ` is the
      -- bound body of the `^∀ ⌜ψ⌝` conclusion sitting inside the `succInd` shape.
      rw [hs]; exact le_indBodyVal _
    · simp
    · -- subst (fvarVec m) b = indBodyVal ⌜ψ⌝
      exact hs

/-- The induction schema `InductionScheme ℒₒᵣ Set.univ` is `Δ₁`, via the recognizer `chUniv`. -/
noncomputable instance InductionScheme.delta1_univ :
    (InductionScheme ℒₒᵣ Set.univ).Δ₁ where
  ch := chUniv
  mem_iff φ := by
    have h : (ℕ ⊧/![(⌜φ⌝ : ℕ)] chUniv.val) ↔ InductionUnivR (⌜φ⌝ : ℕ) := by
      simp
    rw [h]; exact chUniv_mem_iff φ
  isDelta1 := HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by
    haveI := InductionUnivR.defined (V := V); simp

/-! ## Correctness of `IsSigma1`: `IsSigma1 ⌜ψ⌝ ↔ Hierarchy 𝚺 1 ψ` -/

open Bootstrapping in
/-- The code of the bounded universal `∀⁰[#0 < bShift t] φ` is `qqBall (termBShift ⌜t⌝) ⌜φ⌝`. -/
lemma quote_ball {n : ℕ} (t : SyntacticSemiterm ℒₒᵣ n) (φ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (n + 1)) :
    (⌜(∀⁰[“#0 < !!(Rew.bShift t)”] φ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ n)⌝ : ℕ)
      = qqBall (termBShift ℒₒᵣ (⌜t⌝ : ℕ)) (⌜φ⌝ : ℕ) := by
  rw [Semiformula.ball_eq, Semiformula.imp_eq]
  simp only [Semiformula.Operator.lt_def, Semiformula.neg_rel, Semiformula.quote_all,
    Semiformula.quote_or, qqBall, qqAll_inj, qqOr_inj, and_true]
  simp [Semiformula.quote_nrel, Arithmetic.qqNLT, Arithmetic.ltIndex, Semiterm.quote_def,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

open Bootstrapping in
/-- The raw code of `bShift s` is `termBShift ⌜s⌝`. -/
lemma termBShift_quote {n : ℕ} (s : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Rew.bShift s⌝ : ℕ) = termBShift ℒₒᵣ (⌜s⌝ : ℕ) := by
  simp [Semiterm.quote_def, Semiterm.typed_quote_bShift]

open Bootstrapping in
/-- `(⟸)` Every `𝚺₁` formula has a `𝚺₁`-recognized code. By `sigma₁_induction'`. -/
lemma isSigma1_of_hierarchy {n : ℕ} {ψ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ n} (h : Hierarchy 𝚺 1 ψ) :
    IsSigma1 (⌜ψ⌝ : ℕ) := by
  refine sigma₁_induction' h (P := fun n φ => IsSigma1 (⌜φ⌝ : ℕ))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro n; simp
  · intro n; simp
  · intro n t₁ t₂; simp [Semiformula.quote_rel]
  · intro n t₁ t₂; simp [Semiformula.quote_nrel]
  · intro n t₁ t₂; simp [Semiformula.quote_rel]
  · intro n t₁ t₂; simp [Semiformula.quote_nrel]
  · intro n φ ψ hφ hψ ihφ ihψ; simpa [Semiformula.quote_and] using ⟨ihφ, ihψ⟩
  · intro n φ ψ hφ hψ ihφ ihψ; simpa [Semiformula.quote_or] using ⟨ihφ, ihψ⟩
  · intro n t φ hφ ihφ
    rw [quote_ball]
    refine IsSigma1.mk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨termBShift ℒₒᵣ (⌜t⌝ : ℕ), (⌜φ⌝ : ℕ), ⟨(⌜t⌝ : ℕ), ?_, rfl⟩, ihφ, rfl⟩)))))))
    simp [Semiterm.quote_def]
  · intro n φ hφ ihφ; simpa [Semiformula.quote_ex] using ihφ

open Bootstrapping in
/-- `(⟹)` A `𝚺₁`-recognized code is the code of a `𝚺₁` formula. Meta-induction on the formula:
atoms are `𝚺₁` unconditionally; `∧/∨/∃` recurse; the `^∀` case is forced into the bounded shape by
the recognizer (`IsSigma1.of_all`), and the bound is a `bShift`-image (positivity via
`termBV_termBShift_le`), so `Hierarchy.ball` applies. -/
lemma hierarchy_of_isSigma1 {n : ℕ} (ψ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ n) :
    IsSigma1 (⌜ψ⌝ : ℕ) → Hierarchy 𝚺 1 ψ := by
  induction ψ using Semiformula.rec' with
  | hverum => intro _; simp
  | hfalsum => intro _; simp
  | hrel R v => intro _; exact Hierarchy.rel _ _ _ _
  | hnrel R v => intro _; exact Hierarchy.nrel _ _ _ _
  | hand φ ψ ihφ ihψ =>
      intro h; rw [Semiformula.quote_and (V := ℕ) φ ψ, IsSigma1.and_iff] at h
      exact Hierarchy.and (ihφ h.1) (ihψ h.2)
  | hor φ ψ ihφ ihψ =>
      intro h; rw [Semiformula.quote_or (V := ℕ) φ ψ, IsSigma1.or_iff] at h
      exact Hierarchy.or (ihφ h.1) (ihψ h.2)
  | hall φ ihφ =>
      intro h
      rw [Semiformula.quote_all (V := ℕ) φ] at h
      obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, hφeq⟩ := IsSigma1.of_all h
      have hsf := Semiformula.quote_isSemiformula (V := ℕ) φ
      simp only [natCast_nat] at hsf
      rw [hφeq, Arithmetic.qqNLT] at hsf
      simp only [IsSemiformula.or, IsSemiformula.nrel] at hsf
      obtain ⟨⟨_, hvec⟩, hqsf⟩ := hsf
      obtain ⟨φ₂, hφ₂⟩ := Bootstrapping.IsSemiformula.sound hqsf
      have htmsf := hvec.nth (i := 1) (show (1 : ℕ) < 2 by simp)
      simp only [nth_adjoin_one, nth_adjoin_zero] at htmsf
      obtain ⟨s, hs⟩ := Bootstrapping.IsSemiterm.sound
        ((IsSemiterm.def (L := ℒₒᵣ)).mpr ⟨ht,
          (termBV_termBShift_le (L := ℒₒᵣ) ht _).mp ((IsSemiterm.def (L := ℒₒᵣ)).mp htmsf).2⟩)
      have heq : (∀⁰ φ) = ∀⁰[“#0 < !!(Rew.bShift s)”] φ₂ := by
        apply (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp
        rw [Semiformula.quote_all (V := ℕ) φ, hφeq, quote_ball, hs, hφ₂]
        rfl
      have hφ : Hierarchy 𝚺 1 φ := ihφ (by rw [hφeq]; simp [IsSigma1.or_iff, hq, Arithmetic.qqNLT])
      have hφ2 : Hierarchy 𝚺 1 φ₂ := by
        have hform : φ = (“#0 < !!(Rew.bShift s)” 🡒 φ₂) :=
          (Semiformula.all_inj _ _).mp (by rw [← Semiformula.ball_eq]; exact heq)
        rw [hform, Semiformula.imp_eq, Hierarchy.or_iff] at hφ
        exact hφ.2
      rw [heq]
      exact Hierarchy.ball (Rew.positive_iff.mpr ⟨s, rfl⟩) hφ2
  | hexs φ ihφ =>
      intro h; rw [Semiformula.quote_ex (V := ℕ) φ, IsSigma1.ex_iff] at h
      exact Hierarchy.exs (ihφ h)

/-- **Correctness of the `𝚺₁`-code recognizer**: `IsSigma1 ⌜ψ⌝ ↔ Hierarchy 𝚺 1 ψ`. -/
lemma isSigma1_iff_hierarchy {n : ℕ} (ψ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ n) :
    Bootstrapping.IsSigma1 (⌜ψ⌝ : ℕ) ↔ Hierarchy 𝚺 1 ψ :=
  ⟨hierarchy_of_isSigma1 ψ, isSigma1_of_hierarchy⟩

/-! ## The `C = Hierarchy 𝚺 1` recognizer = `chUniv` + the `IsSigma1 K` side condition -/

section chSigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open Bootstrapping

/-- The recognizer for `InductionScheme ℒₒᵣ (Hierarchy 𝚺 1)`: `InductionUnivR` plus the side
condition `IsSigma1 K` on the recovered core `K`. -/
def InductionSigma1R (p : V) : Prop :=
  ∃ m ≤ p, ∃ b ≤ p,
    p = qqAlls b m ∧ IsUFormula ℒₒᵣ b ∧ shift ℒₒᵣ b = b ∧ bv ℒₒᵣ b = m
    ∧ ∃ K ≤ subst ℒₒᵣ (fvarVec m) b,
        IsSemiformula ℒₒᵣ 1 K ∧ IsSigma1 K ∧ subst ℒₒᵣ (fvarVec m) b = indBodyVal K

end chSigma1

/-- Concrete `𝚫₁.Semisentence 1` recognizer for the `𝚺₁` induction scheme. -/
noncomputable def chSigma1 : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “p.
    ∃ m < p + 1, ∃ b < p + 1,
      !qqAllsDef p b m ∧ !(Bootstrapping.isUFormula ℒₒᵣ).sigma b
      ∧ !(Bootstrapping.shiftGraph ℒₒᵣ) b b ∧ !(Bootstrapping.bvGraph ℒₒᵣ) m b
      ∧ ∃ fv, !fvarVecDef fv m ∧ ∃ s, !(Bootstrapping.substsGraph ℒₒᵣ) s fv b
        ∧ ∃ K < s + 1, !(Bootstrapping.isSemiformula ℒₒᵣ).sigma 1 K
          ∧ !(Bootstrapping.isSigma1).sigma K ∧ !indBodyValGraph s K”)
  (.mkPi “p.
    ∃ m < p + 1, ∃ b < p + 1,
      (∀ y, !qqAllsDef y b m → y = p) ∧ !(Bootstrapping.isUFormula ℒₒᵣ).pi b
      ∧ (∀ y, !(Bootstrapping.shiftGraph ℒₒᵣ) y b → y = b) ∧ (∀ y, !(Bootstrapping.bvGraph ℒₒᵣ) y b → y = m)
      ∧ ∀ fv, !fvarVecDef fv m → ∀ s, !(Bootstrapping.substsGraph ℒₒᵣ) s fv b
        → ∃ K < s + 1, !(Bootstrapping.isSemiformula ℒₒᵣ).pi 1 K
          ∧ !(Bootstrapping.isSigma1).pi K ∧ ∀ ib, !indBodyValGraph ib K → s = ib”)

section chSigma1Defined

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open Bootstrapping

instance InductionSigma1R.defined : 𝚫₁-Predicate[V] (InductionSigma1R : V → Prop) via chSigma1 := .mk <| by
  constructor
  · intro v; simp [chSigma1, HierarchySymbol.Semiformula.val_sigma, eq_comm]
  · intro v
    simp [chSigma1, HierarchySymbol.Semiformula.val_sigma, InductionSigma1R,
      lt_succ_iff_le, eq_comm]

end chSigma1Defined

/-- RHS of `chSigma1_mem_iff` reduced to a clean `∃ψ` (with the `𝚺₁` side condition). -/
lemma mem_inductionScheme_sigma1_iff (φ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 0) :
    (∃ σ ∈ InductionScheme ℒₒᵣ (Arithmetic.Hierarchy 𝚺 1), φ = (σ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 0))
      ↔ ∃ ψ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 1, Hierarchy 𝚺 1 ψ ∧ φ = (succInd ψ).univCl' := by
  simp only [InductionScheme, Set.mem_setOf_eq]
  constructor
  · rintro ⟨σ, ⟨ψ, hψ, rfl⟩, rfl⟩
    exact ⟨ψ, hψ, by simp [Semiformula.coe_univCl_eq_univCl']⟩
  · rintro ⟨ψ, hψ, rfl⟩
    exact ⟨Semiformula.univCl (succInd ψ), ⟨ψ, hψ, rfl⟩,
      by simp [Semiformula.coe_univCl_eq_univCl']⟩

open Bootstrapping in
/-- **mem_iff math (C = Hierarchy 𝚺 1).** Mirrors `chUniv_mem_iff`, threading the `IsSigma1 K`
side condition through `isSigma1_iff_hierarchy`. -/
theorem chSigma1_mem_iff (φ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 0) :
    InductionSigma1R (⌜φ⌝ : ℕ)
      ↔ ∃ σ ∈ InductionScheme ℒₒᵣ (Arithmetic.Hierarchy 𝚺 1), φ = (σ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 0) := by
  rw [mem_inductionScheme_sigma1_iff]
  constructor
  · rintro ⟨m, -, b, -, hp, hU, hsh, hbv, K, -, hKsemi, hKsig, hsubst⟩
    obtain ⟨γ, rfl⟩ := Bootstrapping.IsSemiformula.sound hKsemi
    have hbsemi : Bootstrapping.IsSemiformula ℒₒᵣ m b := hbv ▸ hU.isSemiformula
    obtain ⟨β, rfl⟩ := Bootstrapping.IsSemiformula.sound hbsemi
    refine ⟨γ, hierarchy_of_isSigma1 γ hKsig, ?_⟩
    have hβγ : β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)) = succInd γ := by
      apply (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp
      have e := Bootstrapping.subst_fvarVec_quote' (V := ℕ) β
      simp only [natCast_nat] at e
      rw [← e, hsubst, indBodyVal_quote]
    have hβfree : β.freeVariables = ∅ := by
      have hsβ : Rewriting.shift β = β :=
        (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp
          (by rw [Semiformula.quote_shift (V := ℕ) β]; exact hsh)
      have step : ∀ x, β.FVar? x → 1 ≤ x ∧ β.FVar? (x - 1) := by
        intro x hx
        rw [← hsβ] at hx
        rcases Semiformula.fvar?_rew hx with (⟨i, hi⟩ | ⟨z, hz, hi⟩)
        · simp [Rew.shift_bvar, Semiterm.FVar?] at hi
        · have hxz : x = z + 1 := by
            simpa [Rew.shift_fvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] using hi
          exact ⟨by omega, by rw [hxz]; simpa using hz⟩
      by_contra hne
      classical
      have hnem := Finset.nonempty_of_ne_empty hne
      obtain ⟨hge, hpred⟩ := step (β.freeVariables.min' hnem) (β.freeVariables.min'_mem hnem)
      exact absurd (β.freeVariables.min'_le _ hpred) (by omega)
    have hφ : φ = (∀⁰* β : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 0) := by
      apply (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp
      rw [hp, Bootstrapping.quote_allClosure (V := ℕ) β]; simp
    rw [hφ]
    exact closure_inversion β γ hβfree hbv hβγ
  · rintro ⟨ψ, hψ, rfl⟩
    set χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ 0 := succInd ψ with hχ
    set b : ℕ := (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + χ.fvSup))⌝ : ℕ) with hb
    have hcode : (⌜χ.univCl'⌝ : ℕ) = Bootstrapping.qqAlls b ((0 + χ.fvSup : ℕ)) := by
      rw [hb, Bootstrapping.quote_univCl' (V := ℕ) χ]; simp
    have hs : Bootstrapping.subst ℒₒᵣ (Bootstrapping.fvarVec (0 + χ.fvSup : ℕ)) b
        = indBodyVal (⌜ψ⌝ : ℕ) := by
      rw [hb]
      have hsub := Bootstrapping.subst_fvarVec_quote' (V := ℕ)
        (Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + χ.fvSup))
      simp only [natCast_nat] at hsub
      rw [hsub, Bootstrapping.quote_subst_fvar_fixitr χ,
        show (⌜ψ⌝ : ℕ) = (⌜ψ⌝ : Bootstrapping.Semiformula ℕ ℒₒᵣ 1).val from rfl,
        indBodyVal_eq, indBody_quote, hχ]
      rfl
    refine ⟨(0 + χ.fvSup : ℕ), ?_, b, ?_, ?_, ?_, ?_, ?_, (⌜ψ⌝ : ℕ), ?_, ?_, ?_, ?_⟩
    · rw [hcode]; exact Bootstrapping.index_le_qqAlls _ _
    · rw [hcode]; exact Bootstrapping.le_qqAlls _ _
    · exact hcode
    · rw [hb]
      exact (Semiformula.quote_isSemiformula (V := ℕ)
        (Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + χ.fvSup))).isUFormula
    · rw [hb]
      have hnf : ∀ x, ¬(Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + χ.fvSup)).FVar? x := by
        intro x
        rw [Rew.eq_bind (Rew.fixitr 0 χ.fvSup)]
        simp only [Function.comp_def, Rew.fixitr_bvar, Rew.fixitr_fvar, Fin.natAdd_mk, zero_add]
        intro hh
        rcases Semiformula.fvar?_rew hh with (⟨z, hz⟩ | ⟨z, hz, hx⟩)
        · simp at hz
        · have : z < χ.fvSup := Semiformula.lt_fvSup_of_fvar? hz
          simp [this] at hx
      have hshift : Rewriting.shift (Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + χ.fvSup))
          = (Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + χ.fvSup)) :=
        Semiformula.rew_eq_self_of (by simp) (fun x hx ↦ absurd hx (hnf x))
      rw [← Semiformula.quote_shift (V := ℕ)
        (Rew.fixitr 0 χ.fvSup ▹ χ : _root_.LO.FirstOrder.ArithmeticSemiformula ℕ (0 + χ.fvSup)), hshift]
    · rw [hb]; exact (Bootstrapping.bv_quote_fixitr χ).trans (zero_add _).symm
    · rw [hs]; exact le_indBodyVal _
    · simp
    · -- the new side condition: `IsSigma1 ⌜ψ⌝` from `Hierarchy 𝚺 1 ψ`
      exact isSigma1_of_hierarchy hψ
    · exact hs

/-- The induction schema `InductionScheme ℒₒᵣ (Hierarchy 𝚺 1)` is `Δ₁`, via `chSigma1`. -/
noncomputable instance InductionScheme.delta1_sigma1 :
    (InductionScheme ℒₒᵣ (Arithmetic.Hierarchy 𝚺 1)).Δ₁ where
  ch := chSigma1
  mem_iff φ := by
    have h : (ℕ ⊧/![(⌜φ⌝ : ℕ)] chSigma1.val) ↔ InductionSigma1R (⌜φ⌝ : ℕ) := by
      simp
    rw [h]; exact chSigma1_mem_iff φ
  isDelta1 := HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by
    haveI := InductionSigma1R.defined (V := V); simp

/-! ## B2 / B3 — assemble the headline instances -/

noncomputable instance PA_delta1Definable : 𝗣𝗔.Δ₁ :=
  Theory.Δ₁.add PeanoMinus.delta1 InductionScheme.delta1_univ

noncomputable instance ISigma1_delta1Definable : 𝗜𝚺₁.Δ₁ :=
  Theory.Δ₁.add PeanoMinus.delta1 InductionScheme.delta1_sigma1

end LO.FirstOrder.Arithmetic
