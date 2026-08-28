module

public import Foundation.FirstOrder.Incompleteness.First
public import Foundation.FirstOrder.Incompleteness.Second

/-!
# $\Delta_1$-definability of the induction schemata, and of `𝗜𝚺₁` and `𝗣𝗔`

This file establishes `Δ₁`-definability of the induction schemata, and hence of `𝗣𝗔` and `𝗜𝚺₁`:
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

namespace LO.FirstOrder.Arithmetic.Bootstrapping

/-! ## Internal iterated universal quantifier `qqAlls` -/

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

lemma qqAlls_all (p k : V) : qqAlls (^∀ p) k = ^∀ (qqAlls p k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqAlls_succ, ih, qqAlls_succ]

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

lemma IsSemiformula.qqAlls {n k p : V} (h : IsSemiformula L (n + k) p) :
    IsSemiformula L n (qqAlls p k) := by
  rw [isSemiformula_iff] at h ⊢
  obtain ⟨hu, hbv⟩ := h
  refine ⟨isUFormula_qqAlls.mpr hu, ?_⟩
  rw [bv_qqAlls hu, tsub_le_iff_right]
  exact hbv

lemma quote_allClosure {n : ℕ} (φ : Semiproposition L n) :
    (⌜(∀¹* φ : Semiproposition L 0)⌝ : V) = qqAlls (⌜φ⌝ : V) (n : V) := by
  induction n
  case zero => simp
  case succ n ih =>
    rw [show (∀¹* φ : Semiproposition L 0) = ∀¹* (∀¹ φ) from rfl]
    have := ih (∀¹ φ)
    rw [Semiformula.quote_all] at this
    rw [this, Nat.cast_succ, qqAlls_succ']

lemma quote_univCl' (ψ : Semiproposition L 0) :
    (⌜Semiformula.univCl' ψ⌝ : V)
      = qqAlls (⌜(Rew.fixitr 0 ψ.fvSup ▹ ψ : Semiproposition L (0 + ψ.fvSup))⌝ : V)
          ((0 + ψ.fvSup : ℕ) : V) := by
  rw [Semiformula.univCl']; exact quote_allClosure _

lemma quote_subst_fvar_fixitr (φ : Semiproposition L 0) :
    (⌜(Rew.fixitr 0 φ.fvSup ▹ φ : Semiproposition L (0 + φ.fvSup))
        ⇜ (fun x : Fin (0 + φ.fvSup) ↦ (&↑x : SyntacticTerm L))⌝ : V) = ⌜φ⌝ := by
  rw [show (Rew.fixitr 0 φ.fvSup ▹ φ : Semiproposition L (0 + φ.fvSup))
        ⇜ (fun x : Fin (0 + φ.fvSup) ↦ (&↑x : SyntacticTerm L)) = φ from by
    have := Semiformula.subst_comp_fixitr (L := L) φ
    convert this using 2]

end qqAlls

lemma _root_.LO.FirstOrder.Semiformula.fvar?_fvSup_pred {L : Language} {n : ℕ}
    (φ : Semiproposition L n) (h : 0 < φ.fvSup) : φ.FVar? (φ.fvSup - 1) := by
  by_cases he : φ.freeVariables = ∅
  · simp [Semiformula.fvSup, he] at h
  · obtain ⟨k, hk⟩ := Finset.max_of_nonempty (Finset.nonempty_iff_ne_empty.mpr he)
    rw [show φ.fvSup = k + 1 from by simp [Semiformula.fvSup, hk]]
    simpa using Finset.mem_of_max hk

/-! ## `castLE`-invariance of the Gödel code and free variables -/

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

lemma _root_.LO.FirstOrder.Semiformula.quote_castLE {n : ℕ} (φ : Semiproposition L n) :
    ∀ {n' : ℕ} (h : n ≤ n'), (⌜(Rew.castLE h ▹ φ : Semiproposition L n')⌝ : V) = ⌜φ⌝ := by
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
lemma _root_.LO.FirstOrder.Semiformula.freeVariables_castLE {n : ℕ} (φ : Semiproposition L n) :
    ∀ {n' : ℕ} (h : n ≤ n'), (Rew.castLE h ▹ φ : Semiproposition L n').freeVariables = φ.freeVariables := by
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

/-! ## The `bv`-pin bridge -/

section bvPin

variable {L : Language} [L.Encodable] [L.LORDefinable]

-- Only needs `GoedelQuote`/`Rewriting` structure on `L`, not `Encodable`/`LORDefinable`.
omit [L.Encodable] [L.LORDefinable] in
lemma not_fvar?_fixitr (χ : Semiproposition L 0) (x : ℕ) :
    ¬(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup)).FVar? x := by
  rw [Rew.eq_bind (Rew.fixitr 0 χ.fvSup)]
  simp only [Function.comp_def, Rew.fixitr_bvar, Rew.fixitr_fvar, Fin.natAdd_mk, zero_add]
  intro hh
  rcases Semiformula.fvar?_rew hh with (⟨z, hz⟩ | ⟨z, hz, hx⟩)
  · simp at hz
  · have : z < χ.fvSup := Semiformula.lt_fvSup_of_fvar? hz
    simp [this] at hx

lemma quote_shift_fixitr (χ : Semiproposition L 0) :
    Bootstrapping.shift (V := ℕ) L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))⌝ : ℕ)
      = ⌜(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))⌝ := by
  have hshift : Rewriting.shift (Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))
      = (Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup)) :=
    Semiformula.rew_eq_self_of (by simp) (fun x hx ↦ absurd hx (not_fvar?_fixitr χ x))
  rw [← Semiformula.quote_shift (V := ℕ) (Rew.fixitr 0 χ.fvSup ▹ χ), hshift]

/-- Pins the number of leading universals `m` recognized by the induction-scheme code to `fvSup χ`. -/
lemma bv_quote_fixitr (χ : Semiproposition L 0) :
    bv (V := ℕ) L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))⌝ : ℕ)
      = χ.fvSup := by
  have hbsemi := Semiformula.quote_isSemiformula (V := ℕ)
    (Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))
  have hbU : IsUFormula L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))⌝ : ℕ) :=
    hbsemi.isUFormula
  have hle := hbsemi.bv_le
  simp only [Nat.zero_add, natCast_nat] at hle
  rcases (hle : bv (V := ℕ) L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))⌝ : ℕ)
      = χ.fvSup ∨ bv (V := ℕ) L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))⌝ : ℕ)
      < χ.fvSup) with heq | hlt
  · exact heq
  exfalso
  set j := bv (V := ℕ) L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))⌝ : ℕ) with hj
  have hpos : 0 < χ.fvSup := by omega
  have hsemi : IsSemiformula L j (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))⌝ : ℕ) := by
    have := IsUFormula.isSemiformula hbU; rwa [← hj] at this
  obtain ⟨γ, hγ⟩ := IsSemiformula.sound hsemi
  have hjle : j ≤ 0 + χ.fvSup := by omega
  have hcast : (Rew.castLE hjle ▹ γ : Semiproposition L (0 + χ.fvSup))
      = (Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup)) := by
    apply (Semiformula.quote_inj_iff (V := ℕ)).mp
    rw [Semiformula.quote_castLE, hγ]
  have hγfree : γ.freeVariables = ∅ := by
    have hb : (Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup)).freeVariables = ∅ :=
      Finset.eq_empty_of_forall_notMem fun x hx ↦ not_fvar?_fixitr χ x hx
    have := Semiformula.freeVariables_castLE γ hjle
    rw [hcast, hb] at this; exact this.symm
  have hχeq : χ = γ ⇜ (fun i : Fin j ↦ (&↑i : SyntacticTerm L)) := by
    have e1 : (Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))
        ⇜ (fun x : Fin (0 + χ.fvSup) ↦ (&↑x : SyntacticTerm L)) = χ := Semiformula.subst_comp_fixitr χ
    have hRewEq : (Rew.subst (fun x : Fin (0 + χ.fvSup) ↦ (&↑x : SyntacticTerm L))).comp (Rew.castLE hjle)
        = Rew.subst (fun i : Fin j ↦ (&↑i : SyntacticTerm L)) := by
      ext x <;> simp [Rew.comp_app]
    symm
    rw [← e1, ← hcast]
    unfold Rewriting.subst
    rw [← TransitiveRewriting.comp_app, hRewEq]
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

/-! ## Internal free-variable vector `fvarVec` -/

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

lemma nth_fvarVec (k : V) : ∀ i < k, (fvarVec k).[i] = ^&i := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    intro i hi
    rcases (lt_succ_iff_le.mp hi).lt_or_eq with hlt | rfl
    · rw [fvarVec_succ, concat_nth_lt _ _ (by simpa using hlt)]; exact ih i hlt
    · rw [fvarVec_succ, concat_nth_len' _ _ (by simp)]

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

lemma subst_fvarVec_quote' {m : ℕ} (β : ArithmeticSemiproposition m) :
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

/-! ## Σ₁ side condition: internal `IsSigma1` predicate (for `C = Hierarchy 𝚺 1`) -/

section isSigma1

variable {L : Language} [L.Encodable] [L.LORDefinable]

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

/-- `qqBall u q = ^∀ ((^#0 ^≮ u) ^⋎ q)`, the code of `∀¹[“#0 < u”] q`. -/
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

/-- Single-step operator: `p` is `𝚺₁` given that its immediate subformulas in `C` are. -/
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
      | ⟨u, _, q, _, ⟨t, _, ht, rfl⟩, hq, rfl⟩) <;> grind

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
      | ⟨p₁, hp, rfl⟩ | ⟨u, q, ht, hq, rfl⟩) <;> grind

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
      simp only [qqAnd, qqVerum, qqFalsum, qqRel, qqNRel, qqOr, qqExs, qqBall, qqAll, add_left_inj, pair_ext_iff,
        OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, Nat.succ_ne_self, false_and,
        true_and] at h
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨hp, hq⟩
  · rintro ⟨hp, hq⟩
    exact IsSigma1.mk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, hp, hq, rfl⟩)))))

@[simp] lemma IsSigma1.or_iff {p q : V} : IsSigma1 (p ^⋎ q) ↔ IsSigma1 p ∧ IsSigma1 q := by
  constructor
  · intro h
    rcases h.case with (h | h | ⟨_,_,_,h⟩ | ⟨_,_,_,h⟩ | ⟨_,_,_,_,h⟩ | ⟨p₁,p₂,hp,hq,h⟩ | ⟨_,_,h⟩ | ⟨u,q',_,_,h⟩) <;>
      simp only [qqOr, qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqExs, qqBall, qqAll, add_left_inj, pair_ext_iff,
        OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, Nat.succ_ne_self, false_and,
        true_and] at h
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨hp, hq⟩
  · rintro ⟨hp, hq⟩
    exact IsSigma1.mk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, hp, hq, rfl⟩))))))

@[simp] lemma IsSigma1.ex_iff {p : V} : IsSigma1 (^∃ p) ↔ IsSigma1 p := by
  constructor
  · intro h
    rcases h.case with (h | h | ⟨_,_,_,h⟩ | ⟨_,_,_,h⟩ | ⟨_,_,_,_,h⟩ | ⟨_,_,_,_,h⟩ | ⟨p₁,hp,h⟩ | ⟨u,q',_,_,h⟩) <;>
      simp only [qqExs, qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqBall, qqAll, add_left_inj, pair_ext_iff,
        OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, Nat.succ_ne_self, false_and,
        true_and] at h
    · obtain rfl := h; exact hp
  · rintro hp
    exact IsSigma1.mk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩)))))))

lemma IsSigma1.of_all {p : V} (h : IsSigma1 (^∀ p)) :
    ∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsSigma1 q
      ∧ p = qqOr (Arithmetic.qqNLT (qqBvar 0) u) q := by
  rcases h.case with (h | h | ⟨_,_,_,h⟩ | ⟨_,_,_,h⟩ | ⟨_,_,_,_,h⟩ | ⟨_,_,_,_,h⟩ | ⟨_,_,h⟩
    | ⟨u, q, hguard, hq, h⟩) <;>
    first
      | (simp [qqAll, qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqExs] at h
         done)
      | (rw [show qqBall u q = ^∀ (qqOr (Arithmetic.qqNLT (qqBvar 0) u) q) from rfl, qqAll_inj] at h
         exact ⟨u, q, hguard, hq, h⟩)

end isSigma1

end LO.FirstOrder.Arithmetic.Bootstrapping

namespace LO.FirstOrder.Arithmetic

open LO.FirstOrder.Theory

/-! ## B1 — `𝗣𝗔⁻` is `Δ₁` (it is finite) -/

noncomputable instance PeanoMinus.delta1 : (𝗣𝗔⁻ : ArithmeticTheory).Δ₁ :=
  Theory.Δ₁.ofFinite _ PeanoMinus.finite

/-! ## Typed decomposition of `succInd` -/

section succInd

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma succInd_eq (φ : ArithmeticSemiproposition 1) :
    succInd φ =
      ((φ ⇜ (![‘0’] : Fin 1 → ArithmeticSemiterm ℕ 0))
        🡒 ((∀¹ (φ 🡒 (φ ⇜ (![‘#0 + 1’] : Fin 1 → ArithmeticSemiterm ℕ 1)))) 🡒 ∀¹ φ)) := by
  unfold succInd; simp

lemma typed_quote_succInd (φ : ArithmeticSemiproposition 1) :
    (⌜succInd φ⌝ : Bootstrapping.Semiformula V ℒₒᵣ 0) =
      (⌜φ ⇜ (![‘0’] : Fin 1 → ArithmeticSemiterm ℕ 0)⌝)
        🡒 ((∀¹ (⌜φ⌝ 🡒 ⌜φ ⇜ (![‘#0 + 1’] : Fin 1 → ArithmeticSemiterm ℕ 1)⌝)) 🡒 ∀¹ ⌜φ⌝) := by
  unfold succInd
  rw [show φ ⇜ (![#0] : Fin 1 → ArithmeticSemiterm ℕ 1) = φ from by simp]
  simp

/-- The typed `succInd` shape as a function of the (typed) core code `K = ⌜ψ⌝`. -/
noncomputable def indBody (K : Bootstrapping.Semiformula V ℒₒᵣ 1) : Bootstrapping.Semiformula V ℒₒᵣ 0 :=
  (K.subst ![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝])
    🡒 ((∀¹ (K 🡒 K.subst ![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝])) 🡒 ∀¹ K)

lemma indBody_quote (φ : ArithmeticSemiproposition 1) :
    indBody (⌜φ⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1) = ⌜succInd φ⌝ := by
  rw [typed_quote_succInd]; unfold indBody; simp [Matrix.constant_eq_singleton]

/-- The raw `V → V` form of `(indBody ·).val`. -/
noncomputable def indBodyVal (k : V) : V :=
  Bootstrapping.imp ℒₒᵣ
    (Bootstrapping.subst ℒₒᵣ
      (Bootstrapping.SemitermVec.val (![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝] : Bootstrapping.SemitermVec V ℒₒᵣ 1 0)) k)
    (Bootstrapping.imp ℒₒᵣ
      (Bootstrapping.qqAll (Bootstrapping.imp ℒₒᵣ k
        (Bootstrapping.subst ℒₒᵣ
          (Bootstrapping.SemitermVec.val (![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝] : Bootstrapping.SemitermVec V ℒₒᵣ 1 1)) k)))
      (Bootstrapping.qqAll k))

lemma indBodyVal_eq (K : Bootstrapping.Semiformula V ℒₒᵣ 1) : indBodyVal K.val = (indBody K).val := by
  simp only [indBodyVal, indBody, Bootstrapping.Semiformula.val_imp, Bootstrapping.Semiformula.val_all,
    Bootstrapping.Semiformula.val_substs]

lemma le_indBodyVal (k : V) : k ≤ indBodyVal k := by
  unfold indBodyVal Bootstrapping.imp
  exact (Bootstrapping.le_qqAll _).trans
    (le_of_lt ((Bootstrapping.lt_or_right _ _).trans (Bootstrapping.lt_or_right _ _)))

lemma indBodyVal_quote (γ : ArithmeticSemiproposition 1) : indBodyVal (⌜γ⌝ : ℕ) = (⌜succInd γ⌝ : ℕ) := by
  rw [show (⌜γ⌝ : ℕ) = (⌜γ⌝ : Bootstrapping.Semiformula ℕ ℒₒᵣ 1).val from rfl, indBodyVal_eq,
    indBody_quote]
  rfl

instance indBodyVal_definable : 𝚺₁-Function₁ (indBodyVal : V → V) := by
  unfold indBodyVal
  definability

/-! ### A concrete `𝚺₁`-graph for `indBodyVal` -/

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

/-! ## The crux — the induction schema is `Δ₁` -/

section ch

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open Bootstrapping

/-- The recognizer predicate for `InductionScheme ℒₒᵣ C` over a model `V`, parameterized by a side
condition `S` on the recovered core. -/
def InductionR (S : V → Prop) (p : V) : Prop :=
  ∃ m ≤ p, ∃ b ≤ p,
    p = qqAlls b m ∧ IsUFormula ℒₒᵣ b ∧ shift ℒₒᵣ b = b ∧ bv ℒₒᵣ b = m
    ∧ ∃ K ≤ subst ℒₒᵣ (fvarVec m) b,
        IsSemiformula ℒₒᵣ 1 K ∧ S K ∧ subst ℒₒᵣ (fvarVec m) b = indBodyVal K

end ch

/-- Concrete `𝚫₁.Semisentence 1` recognizer for `InductionR cond`. -/
noncomputable def chInd (cond : 𝚫₁.Semisentence 1) : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “p.
    ∃ m < p + 1, ∃ b < p + 1,
      !qqAllsDef p b m ∧ !(Bootstrapping.isUFormula ℒₒᵣ).sigma b
      ∧ !(Bootstrapping.shiftGraph ℒₒᵣ) b b ∧ !(Bootstrapping.bvGraph ℒₒᵣ) m b
      ∧ ∃ fv, !fvarVecDef fv m ∧ ∃ s, !(Bootstrapping.substsGraph ℒₒᵣ) s fv b
        ∧ ∃ K < s + 1, !(Bootstrapping.isSemiformula ℒₒᵣ).sigma 1 K
          ∧ !cond.sigma K ∧ !indBodyValGraph s K”)
  (.mkPi “p.
    ∃ m < p + 1, ∃ b < p + 1,
      (∀ y, !qqAllsDef y b m → y = p) ∧ !(Bootstrapping.isUFormula ℒₒᵣ).pi b
      ∧ (∀ y, !(Bootstrapping.shiftGraph ℒₒᵣ) y b → y = b) ∧ (∀ y, !(Bootstrapping.bvGraph ℒₒᵣ) y b → y = m)
      ∧ ∀ fv, !fvarVecDef fv m → ∀ s, !(Bootstrapping.substsGraph ℒₒᵣ) s fv b
        → ∃ K < s + 1, !(Bootstrapping.isSemiformula ℒₒᵣ).pi 1 K
          ∧ !cond.pi K ∧ ∀ ib, !indBodyValGraph ib K → s = ib”)

noncomputable def chUniv : 𝚫₁.Semisentence 1 := chInd ⊤

noncomputable def chSigma1 : 𝚫₁.Semisentence 1 := chInd Bootstrapping.isSigma1

section chDefined

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open Bootstrapping

instance InductionR.defined {S : V → Prop} {cond : 𝚫₁.Semisentence 1}
    [hcond : 𝚫₁-Predicate[V] S via cond] :
    𝚫₁-Predicate[V] (InductionR S : V → Prop) via chInd cond := .mk <| by
  constructor
  · intro v; simp [chInd, HierarchySymbol.Semiformula.val_sigma, eq_comm]
  · intro v
    simp [chInd, HierarchySymbol.Semiformula.val_sigma, InductionR, lt_succ_iff_le, eq_comm]

noncomputable instance InductionR.univ_defined :
    𝚫₁-Predicate[V] (InductionR (fun _ ↦ True) : V → Prop) via chUniv :=
  InductionR.defined (hcond := ⟨by simp, by intro v; simp⟩)

noncomputable instance InductionR.sigma1_defined :
    𝚫₁-Predicate[V] (InductionR IsSigma1 : V → Prop) via chSigma1 :=
  InductionR.defined

end chDefined

lemma mem_inductionScheme_iff {C : ArithmeticSemiproposition 1 → Prop} (φ : ArithmeticSemiproposition 0) :
    (∃ σ ∈ InductionScheme ℒₒᵣ C, φ = (σ : ArithmeticSemiproposition 0))
      ↔ ∃ ψ : ArithmeticSemiproposition 1, C ψ ∧ φ = (succInd ψ).univCl' := by
  simp only [InductionScheme, Set.mem_setOf_eq]
  constructor
  · rintro ⟨σ, ⟨ψ, hψ, rfl⟩, rfl⟩
    exact ⟨ψ, hψ, by simp [Semiformula.coe_univCl_eq_univCl']⟩
  · rintro ⟨ψ, hψ, rfl⟩
    exact ⟨Semiformula.univCl (succInd ψ), ⟨ψ, hψ, rfl⟩,
      by simp [Semiformula.coe_univCl_eq_univCl']⟩

/-- A freevar-free, `bv`-pinned formula `β` that substitutes back to `succInd γ` is exactly the
`fixitr`-image, so its `m`-fold closure equals `(succInd γ).univCl'`. -/
theorem closure_inversion {m : ℕ} (β : ArithmeticSemiproposition m) (γ : ArithmeticSemiproposition 1)
    (hfree : β.freeVariables = ∅) (hbv : Bootstrapping.bv (V := ℕ) ℒₒᵣ (⌜β⌝ : ℕ) = m)
    (hβγ : β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)) = succInd γ) :
    (∀¹* β : ArithmeticSemiproposition 0) = (succInd γ).univCl' := by
  set χ : ArithmeticSemiproposition 0 := succInd γ with hχ
  have hcodeβ : (⌜(Rew.fixitr 0 m ▹ χ : ArithmeticSemiproposition (0 + m))⌝ : ℕ) = ⌜β⌝ := by
    have hcompcast :
        ((Rew.fixitr 0 m).comp (Rew.subst (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)))) ▹ β
          = (Rew.castLE (Nat.le_add_left m 0) ▹ β : ArithmeticSemiproposition (0 + m)) := by
      apply Semiformula.rew_eq_of_funEqOn
      · intro x; simp [Rew.comp_app, Rew.fixitr_fvar, Fin.ext_iff]
      · intro x hx; rw [Semiformula.FVar?, hfree] at hx; simp at hx
    have heq : (Rew.fixitr 0 m ▹ χ : ArithmeticSemiproposition (0 + m))
        = (Rew.castLE (Nat.le_add_left m 0) ▹ β : ArithmeticSemiproposition (0 + m)) := by
      rw [← hcompcast, TransitiveRewriting.comp_app,
        show (Rew.subst (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)) ▹ β) = χ from hβγ]
    rw [heq, Semiformula.quote_castLE (V := ℕ) β (Nat.le_add_left m 0)]
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
  have hcast_eq : (Rew.fixitr 0 m ▹ χ : ArithmeticSemiproposition (0 + m))
      = (Rew.castLE (by omega : (0 + χ.fvSup) ≤ (0 + m))
          ▹ (Rew.fixitr 0 χ.fvSup ▹ χ : ArithmeticSemiproposition (0 + χ.fvSup))) := by
    rw [← TransitiveRewriting.comp_app]
    apply Semiformula.rew_eq_of_funEqOn₀
    intro x hx
    have hxlt : x < χ.fvSup := Semiformula.lt_fvSup_of_fvar? hx
    simp [Rew.comp_app, Rew.fixitr_fvar, hxlt, show x < m from by omega]
  have hcode : (⌜(Rew.fixitr 0 m ▹ χ : ArithmeticSemiproposition (0 + m))⌝ : ℕ)
      = ⌜(Rew.fixitr 0 χ.fvSup ▹ χ : ArithmeticSemiproposition (0 + χ.fvSup))⌝ := by
    rw [hcast_eq, Semiformula.quote_castLE (V := ℕ)
      (Rew.fixitr 0 χ.fvSup ▹ χ : ArithmeticSemiproposition (0 + χ.fvSup)) (by omega)]
  have hm : m = χ.fvSup := by
    rw [← hbv, ← hcodeβ, hcode]; exact Bootstrapping.bv_quote_fixitr χ
  apply (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp
  rw [Bootstrapping.quote_allClosure (V := ℕ) β, Semiformula.univCl',
    Bootstrapping.quote_allClosure (V := ℕ) (Rew.fixitr 0 χ.fvSup ▹ χ), ← hcodeβ, hcode, hm]
  simp

private lemma freeVariables_eq_empty_of_shift_quote_fixed {m : ℕ} (β : ArithmeticSemiproposition m)
    (hsh : Bootstrapping.shift (V := ℕ) ℒₒᵣ (⌜β⌝ : ℕ) = ⌜β⌝) : β.freeVariables = ∅ := by
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

/-- `InductionR S` fires exactly on codes of universal closures of `succInd ψ` for `ψ` with `C ψ`,
given that `S` correctly recognizes the codes of `C`-formulas. -/
theorem inductionR_quote_iff {S : ℕ → Prop} {C : ArithmeticSemiproposition 1 → Prop}
    (hS : ∀ γ, S (⌜γ⌝ : ℕ) ↔ C γ) (φ : ArithmeticSemiproposition 0) :
    InductionR S (⌜φ⌝ : ℕ) ↔ ∃ ψ, C ψ ∧ φ = (succInd ψ).univCl' := by
  constructor
  · rintro ⟨m, -, b, -, hp, hU, hsh, hbv, K, -, hKsemi, hKS, hsubst⟩
    obtain ⟨γ, rfl⟩ := Bootstrapping.IsSemiformula.sound hKsemi
    have hbsemi : Bootstrapping.IsSemiformula ℒₒᵣ m b := hbv ▸ hU.isSemiformula
    obtain ⟨β, rfl⟩ := Bootstrapping.IsSemiformula.sound hbsemi
    refine ⟨γ, (hS γ).mp hKS, ?_⟩
    have hβγ : β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)) = succInd γ := by
      apply (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp
      have e := Bootstrapping.subst_fvarVec_quote' (V := ℕ) β
      simp only [natCast_nat] at e
      rw [← e, hsubst, indBodyVal_quote]
    have hβfree : β.freeVariables = ∅ := freeVariables_eq_empty_of_shift_quote_fixed β hsh
    have hφ : φ = (∀¹* β : ArithmeticSemiproposition 0) := by
      apply (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp
      rw [hp, Bootstrapping.quote_allClosure (V := ℕ) β]; simp
    rw [hφ]
    exact closure_inversion β γ hβfree hbv hβγ
  · rintro ⟨ψ, hψ, rfl⟩
    set χ : ArithmeticSemiproposition 0 := succInd ψ with hχ
    set b : ℕ := (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : ArithmeticSemiproposition (0 + χ.fvSup))⌝ : ℕ) with hb
    have hcode : (⌜χ.univCl'⌝ : ℕ) = Bootstrapping.qqAlls b ((0 + χ.fvSup : ℕ)) := by
      rw [hb, Bootstrapping.quote_univCl' (V := ℕ) χ]; simp
    have hs : Bootstrapping.subst ℒₒᵣ (Bootstrapping.fvarVec (0 + χ.fvSup : ℕ)) b
        = indBodyVal (⌜ψ⌝ : ℕ) := by
      rw [hb]
      have hsub := Bootstrapping.subst_fvarVec_quote' (V := ℕ)
        (Rew.fixitr 0 χ.fvSup ▹ χ : ArithmeticSemiproposition (0 + χ.fvSup))
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
        (Rew.fixitr 0 χ.fvSup ▹ χ : ArithmeticSemiproposition (0 + χ.fvSup))).isUFormula
    · rw [hb]; exact Bootstrapping.quote_shift_fixitr χ
    · rw [hb]; exact (Bootstrapping.bv_quote_fixitr χ).trans (zero_add _).symm
    · rw [hs]; exact le_indBodyVal _
    · simp
    · exact (hS ψ).mpr hψ
    · exact hs

/-- The induction schema `InductionScheme ℒₒᵣ Set.univ` is `Δ₁`, via the recognizer `chUniv`. -/
noncomputable instance InductionScheme.delta1_univ :
    (InductionScheme ℒₒᵣ Set.univ).Δ₁ where
  ch := chUniv
  mem_iff φ := by
    have h : (ℕ ⊧/![(⌜φ⌝ : ℕ)] chUniv.val) ↔ InductionR (fun _ ↦ True) (⌜φ⌝ : ℕ) := by
      simp
    rw [h]
    exact (inductionR_quote_iff (C := Set.univ) (fun _ ↦ Iff.rfl) φ).trans (mem_inductionScheme_iff φ).symm
  isDelta1 := HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by
    haveI := InductionR.univ_defined (V := V); simp

/-! ## Correctness of `IsSigma1`: `IsSigma1 ⌜ψ⌝ ↔ Hierarchy 𝚺 1 ψ` -/

open Bootstrapping in
lemma quote_ball {n : ℕ} (t : SyntacticSemiterm ℒₒᵣ n) (φ : ArithmeticSemiproposition (n + 1)) :
    (⌜(∀¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemiproposition n)⌝ : ℕ)
      = qqBall (termBShift ℒₒᵣ (⌜t⌝ : ℕ)) (⌜φ⌝ : ℕ) := by
  rw [Semiformula.ball_eq, Semiformula.imp_eq]
  simp only [Semiformula.Operator.lt_def, Semiformula.neg_rel, Semiformula.quote_all,
    Semiformula.quote_or, qqBall, qqAll_inj, qqOr_inj, and_true]
  simp [Semiformula.quote_nrel, Arithmetic.qqNLT, Arithmetic.ltIndex, Semiterm.quote_def,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

open Bootstrapping in
lemma termBShift_quote {n : ℕ} (s : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Rew.bShift s⌝ : ℕ) = termBShift ℒₒᵣ (⌜s⌝ : ℕ) := by
  simp [Semiterm.quote_def, Semiterm.typed_quote_bShift]

open Bootstrapping in
lemma isSigma1_of_hierarchy {n : ℕ} {ψ : ArithmeticSemiproposition n} (h : Hierarchy 𝚺 1 ψ) :
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
lemma hierarchy_of_isSigma1 {n : ℕ} (ψ : ArithmeticSemiproposition n) :
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
      have heq : (∀¹ φ) = ∀¹[“#0 < !!(Rew.bShift s)”] φ₂ := by
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

/-- Correctness of the `𝚺₁`-code recognizer. -/
lemma isSigma1_iff_hierarchy {n : ℕ} (ψ : ArithmeticSemiproposition n) :
    Bootstrapping.IsSigma1 (⌜ψ⌝ : ℕ) ↔ Hierarchy 𝚺 1 ψ :=
  ⟨hierarchy_of_isSigma1 ψ, isSigma1_of_hierarchy⟩

/-- The induction schema `InductionScheme ℒₒᵣ (Hierarchy 𝚺 1)` is `Δ₁`, via `chSigma1`. -/
noncomputable instance InductionScheme.delta1_sigma1 :
    (InductionScheme ℒₒᵣ (Arithmetic.Hierarchy 𝚺 1)).Δ₁ where
  ch := chSigma1
  mem_iff φ := by
    have h : (ℕ ⊧/![(⌜φ⌝ : ℕ)] chSigma1.val) ↔ InductionR Bootstrapping.IsSigma1 (⌜φ⌝ : ℕ) := by
      simp
    rw [h]
    exact (inductionR_quote_iff isSigma1_iff_hierarchy φ).trans (mem_inductionScheme_iff φ).symm
  isDelta1 := HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by
    haveI := InductionR.sigma1_defined (V := V); simp

/-! ## B2 / B3 — assemble the headline instances -/

noncomputable instance PA_delta1Definable : 𝗣𝗔.Δ₁ :=
  Theory.Δ₁.add PeanoMinus.delta1 InductionScheme.delta1_univ

noncomputable instance ISigma1_delta1Definable : 𝗜𝚺₁.Δ₁ :=
  Theory.Δ₁.add PeanoMinus.delta1 InductionScheme.delta1_sigma1

end LO.FirstOrder.Arithmetic
