import Foundation.FirstOrder.Incompleteness.StandardProvability.D1

/-!
# Formalized $\Sigma_1$-Completeness

-/

namespace LO.ISigma1.Metamath

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

namespace InternalArithmetic

variable {T : LOR.TTheory (V := V)} [R₀Theory T]

noncomputable def toNumVec {n} (e : Fin n → V) : (Language.codeIn ℒₒᵣ V).SemitermVec n 0 :=
  ⟨⌜fun i ↦ numeral (e i)⌝,
   IsSemitermVec.iff.mpr <| ⟨by simp, by
    intro i hi
    rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    simp [quote_nth_fin (fun i ↦ numeral (e i)) i]⟩⟩

@[simp] lemma toNumVec_nil : (toNumVec (![] : Fin 0 → V)) = .nil _ _ := by ext; simp [toNumVec]

@[simp] lemma toNumVec_nth {n} (e : Fin n → V) (i : Fin n) : (toNumVec e).nth i = ↑(e i) := by ext; simp [toNumVec]

@[simp] lemma toNumVec_val_nth {n} (e : Fin n → V) (i : Fin n) : (toNumVec e).val.[i] = numeral (e i) := by simp [toNumVec]

/-- TODO: move-/
@[simp] lemma coe_coe_lt {n} (i : Fin n) : (i : V) < (n : V) :=
  calc (i : V) < (i : V) + (n - i : V) := by simp
  _  = (n : V) := by simp

@[simp] lemma len_semitermvec {L : Metamath.Language V} {pL} [L.Defined pL] (v : SemitermVec L k n) : len v.val = k := v.prop.lh

@[simp] lemma cast_substs_numVec (φ : Semisentence ℒₒᵣ (n + 1)) :
    ((.cast (V := V) (n := ↑(n + 1)) (n' := ↑n + 1) ⌜Rew.embs ▹ φ⌝ (by simp)) ^/[(toNumVec e).q.substs (typedNumeral 0 x).sing]) =
    ⌜Rew.embs ▹ φ⌝ ^/[toNumVec (x :> e)] := by
  have : (toNumVec e).q.substs (typedNumeral 0 x).sing = x ∷ᵗ toNumVec e := by
    suffices
      (⌜ℒₒᵣ⌝[V]).termSubstVec (n + 1) (numeral x ∷ 0) ((⌜ℒₒᵣ⌝[V]).qVec (toNumVec e).val)
      = numeral x ∷ (toNumVec e).val by ext; simpa
    apply nth_ext' ((↑n : V) + 1)
      (by rw [len_termSubstVec]; simpa using (toNumVec e).prop.qVec.isUTerm)
      (by simp [(toNumVec e).prop.lh])
    intro i hi
    rw [nth_termSubstVec (by simpa using (toNumVec e).prop.qVec.isUTerm) hi]
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp [qVec]
    · simp only [qVec, nth_cons_succ, SemitermVec.prop]
      rcases eq_fin_of_lt_nat (by simpa using hi) with ⟨i, rfl⟩
      rw [nth_termBShiftVec (by simp),
        toNumVec_val_nth, numeral_bShift,
        numeral_substs (n := 1) (m := 0) (by simp)]
      simp
  rw [this]
  ext; simp [toNumVec, Matrix.comp_vecCons']

namespace TProof

open Language.Theory.TProof Entailment

variable (T)

noncomputable def termEqComplete {n : ℕ} (e : Fin n → V) :
    (t : Semiterm ℒₒᵣ Empty n) → T ⊢ ⌜Rew.embs t⌝^ᵗ/[toNumVec e] =' ↑(t.valbm V e)
  | #z                                 => by simpa using eqRefl T (e z)
  | &x                                 => Empty.elim x
  | Semiterm.func Language.Zero.zero v => by simpa using eqRefl T _
  | Semiterm.func Language.One.one v   => by simpa using eqRefl T _
  | Semiterm.func Language.Add.add v   => by
      simp only [Rew.func, Semiterm.codeIn'_add, Fin.isValue, subst_add, Semiterm.val_func,
        Structure.add_eq_of_lang]
      have ih : T ⊢ (⌜Rew.embs (v 0)⌝^ᵗ/[toNumVec e] + ⌜Rew.embs (v 1)⌝^ᵗ/[toNumVec e]) =' (↑((v 0).valbm V e) + ↑((v 1).valbm V e)) :=
        addExt T _ _ _ _ ⨀ termEqComplete e (v 0) ⨀ termEqComplete e (v 1)
      have : T ⊢ ((v 0).valbm V e + (v 1).valbm V e : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑((v 0).valbm V e + (v 1).valbm V e) := addComplete T _ _
      exact eqTrans T _ _ _ ⨀ ih ⨀ this
  | Semiterm.func Language.Mul.mul v   => by
      have ih : T ⊢ (⌜Rew.embs (v 0)⌝^ᵗ/[toNumVec e] * ⌜Rew.embs (v 1)⌝^ᵗ/[toNumVec e]) =' (↑((v 0).valbm V e) * ↑((v 1).valbm V e)) :=
        mulExt T _ _ _ _ ⨀ termEqComplete e (v 0) ⨀ termEqComplete e (v 1)
      have : T ⊢ ((v 0).valbm V e * (v 1).valbm V e : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑((v 0).valbm V e * (v 1).valbm V e) := mulComplete T _ _
      simpa [Rew.func, Semiterm.val_func] using eqTrans T _ _ _ ⨀ ih ⨀ this

lemma termEq_complete! {n : ℕ} (e : Fin n → V) (t : Semiterm ℒₒᵣ Empty n) :
    T ⊢! ⌜Rew.embs t⌝^ᵗ/[toNumVec e] =' ↑(t.valbm V e) := ⟨termEqComplete T e t⟩

open FirstOrder.Arithmetic

theorem bold_sigma₁_complete {n} {φ : Semisentence ℒₒᵣ n} (hp : Hierarchy 𝚺 1 φ) {e} :
    V ⊧/e φ → T ⊢! ⌜Rew.embs ▹ φ⌝^/[toNumVec e] := by
  revert e
  apply sigma₁_induction' hp
  case hVerum => intro n; simp
  case hFalsum =>
    intro n
    simp only [LogicalConnective.HomClass.map_bot, Prop.bot_eq_false,
      Semiformula.codeIn'_falsum, Language.Semiformula.substs_falsum, false_implies, implies_true]
  case hEQ =>
    intro n t₁ t₂ e h
    have : t₁.valbm V e = t₂.valbm V e := by simpa using h
    suffices T ⊢! ⌜Rew.embs t₁⌝^ᵗ/[toNumVec e] =' ⌜Rew.embs t₂⌝^ᵗ/[toNumVec e] by
      simpa only [Semiformula.rew_rel2, Semiformula.codeIn'_eq, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.vecHead, Matrix.cons_val_fin_one, substs_equals] using this
    refine eq_ext T _ _ _ _ ⨀ ?_ ⨀ ?_ ⨀ eq_complete! T this
    · exact eq_symm'! _ <| termEq_complete! T e t₁
    · exact eq_symm'! _ <| termEq_complete! T e t₂
  case hNEQ =>
    intro n t₁ t₂ e h
    have : t₁.valbm V e ≠ t₂.valbm V e := by simpa using h
    suffices T ⊢! ⌜Rew.embs t₁⌝^ᵗ/[toNumVec e] ≠' ⌜Rew.embs t₂⌝^ᵗ/[toNumVec e] by
      simpa only [Semiformula.rew_nrel2, Semiformula.codeIn'_neq, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.vecHead, Matrix.cons_val_fin_one, substs_notEquals] using this
    refine ne_ext T _ _ _ _ ⨀ ?_ ⨀ ?_ ⨀ ne_complete! T this
    · exact eq_symm'! _ <| termEq_complete! T e t₁
    · exact eq_symm'! _ <| termEq_complete! T e t₂
  case hLT =>
    intro n t₁ t₂ e h
    have : t₁.valbm V e < t₂.valbm V e := by simpa using h
    suffices T ⊢! ⌜Rew.embs t₁⌝^ᵗ/[toNumVec e] <' ⌜Rew.embs t₂⌝^ᵗ/[toNumVec e] by
      simpa only [Semiformula.rew_rel2, Semiformula.codeIn'_lt, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.vecHead, Matrix.cons_val_fin_one, substs_lessThan] using this
    refine lt_ext! T _ _ _ _ ⨀ ?_ ⨀ ?_ ⨀ lt_complete! T this
    · exact eq_symm'! _ <| termEq_complete! T e t₁
    · exact eq_symm'! _ <| termEq_complete! T e t₂
  case hNLT =>
    intro n t₁ t₂ e h
    have : t₂.valbm V e ≤ t₁.valbm V e := by simpa using h
    suffices T ⊢! ⌜Rew.embs t₁⌝^ᵗ/[toNumVec e] ≮' ⌜Rew.embs t₂⌝^ᵗ/[toNumVec e] by
      simpa only [Semiformula.rew_nrel2, Semiformula.codeIn'_nlt, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.vecHead, Matrix.cons_val_fin_one, substs_notLessThan] using this
    refine nlt_ext T _ _ _ _ ⨀ ?_ ⨀ ?_ ⨀ nlt_complete T this
    · exact eq_symm'! _ <| termEq_complete! T e t₁
    · exact eq_symm'! _ <| termEq_complete! T e t₂
  case hAnd =>
    intro n φ ψ _ _ ihp ihq e h
    have h : Semiformula.Evalbm V e φ ∧ Semiformula.Evalbm V e ψ := by simpa using h
    simpa only [LogicalConnective.HomClass.map_and, Semiformula.codeIn'_and,
      Language.Semiformula.substs_and] using K!_intro (ihp h.1) (ihq h.2)
  case hOr =>
    intro n φ ψ _ _ ihp ihq e h
    have : Semiformula.Evalbm V e φ ∨ Semiformula.Evalbm V e ψ := by simpa using h
    rcases this with (h | h)
    · simpa only [LogicalConnective.HomClass.map_or, Semiformula.codeIn'_or,
      Language.Semiformula.substs_or] using A!_intro_left (ihp h)
    · simpa only [LogicalConnective.HomClass.map_or, Semiformula.codeIn'_or,
      Language.Semiformula.substs_or] using A!_intro_right (ihq h)
  case hBall =>
    intro n t φ _ ihp e h
    suffices T ⊢! Language.Semiformula.ball (⌜Rew.emb t⌝^ᵗ/[toNumVec e]) ((_)^/[(toNumVec e).q]) by
      simpa only [Rewriting.smul_ball, Rew.q_emb, Rew.hom_finitary2, Rew.emb_bvar, ← Rew.emb_bShift_term,
        Semiformula.codeIn'_ball, substs_ball]
    apply ball_replace! T _ _ _ ⨀ (eq_symm! T _ _ ⨀ termEq_complete! T e t) ⨀ ?_
    apply ball_intro!
    intro x hx
    suffices T ⊢! ⌜Rew.embs ▹ φ⌝^/[toNumVec (x :> e)] by simpa [Language.TSemifromula.substs_substs]
    have : Semiformula.Evalbm V (x :> e) φ := by
      have : ∀ x < t.valbm V e, Semiformula.Evalbm V (x :> e) φ := by simpa using h
      exact this x hx
    exact ihp this
  case hEx =>
    intro n φ _ ihp e h
    simp only [Rewriting.app_ex, Rew.q_emb, Semiformula.codeIn'_ex, Language.Semiformula.substs_ex]
    have : ∃ x, Semiformula.Evalbm V (x :> e) φ := by simpa using h
    rcases this with ⟨x, hx⟩
    apply ex! x
    simpa [Language.TSemifromula.substs_substs] using ihp hx

/-- Hilbert–Bernays provability condition D3 -/
theorem sigma₁_complete {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) : V ⊧ₘ₀ σ → T ⊢! ⌜σ⌝ := by
  intro h; simpa using bold_sigma₁_complete T hσ (e := ![]) (by simpa [models₀_iff] using h)

end TProof

end InternalArithmetic

section

variable {T : ArithmeticTheory} [T.Delta1Definable]

theorem sigma₁_complete {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    V ⊧ₘ₀ σ → T.Provable (⌜σ⌝ : V) := fun h ↦ by
  simpa [provable_iff] using InternalArithmetic.TProof.sigma₁_complete _ hσ h

theorem sigma₁_complete_provable {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    V ⊧ₘ₀ σ → T†V ⊢! ⌜σ⌝ := fun h ↦ by
  simpa [provable_iff] using InternalArithmetic.TProof.sigma₁_complete _ hσ h

end

section D2

variable {T : ArithmeticTheory} [T.Delta1Definable]

/-- Hilbert–Bernays provability condition D2 -/
theorem modus_ponens {φ ψ : SyntacticFormula ℒₒᵣ} (hφψ : T.Provable (⌜φ ➝ ψ⌝ : V)) (hφ : T.Provable (⌜φ⌝ : V)) :
    T.Provable (⌜ψ⌝ : V) := provable_iff'.mpr <| (by simpa using provable_iff'.mp hφψ) ⨀ provable_iff'.mp hφ

theorem modus_ponens₀ {σ τ : Sentence ℒₒᵣ} (hστ : T.Provable (⌜σ ➝ τ⌝ : V)) (hσ : T.Provable (⌜σ⌝ : V)) :
    T.Provable (⌜τ⌝ : V) := provable_iff.mpr <| (by simpa using provable_iff.mp hστ) ⨀ provable_iff.mp hσ

end D2

end LO.ISigma1.Metamath
