import Foundation.FirstOrder.Incompleteness.StandardProvability.D1

/-!
# Formalized $\Sigma_1$-Completeness

-/

namespace LO.ISigma1.Metamath

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

namespace InternalArithmetic

variable {T : ArithmeticTheory} [T.Δ₁Definable]

noncomputable abbrev bv {n : V} (x : V) (h : x < n := by simp) : Semiterm V ℒₒᵣ n := Semiterm.bv x h

noncomputable abbrev fv {n : V} (x : V) : Semiterm V ℒₒᵣ n := Semiterm.fv x

local prefix:max "#'" => bv

local prefix:max "&'" => fv

noncomputable def toNumVec {n} (e : Fin n → V) : SemitermVec V ℒₒᵣ n 0 :=
  ⟨⌜fun i ↦ numeral (e i)⌝,
   (IsSemitermVec.iff (L := ℒₒᵣ)).mpr <| ⟨by simp, by
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

@[simp] lemma len_semitermvec (v : SemitermVec V ℒₒᵣ k n) : len v.val = k := v.prop.lh

@[simp] lemma cast_substs_numVec (φ : Semisentence ℒₒᵣ (n + 1)) :
    (.sCast (⌜Rew.embs ▹ φ⌝ : Semiformula V ℒₒᵣ ↑(n + 1))) ^/[(toNumVec e).q.substs (typedNumeral 0 x).sing] =
    ⌜Rew.embs ▹ φ⌝ ^/[toNumVec (x :> e)] := by
  have : (toNumVec e).q.substs (typedNumeral 0 x).sing = x ∷ᵗ toNumVec e := by
    suffices
        termSubstVec ℒₒᵣ ↑(n + 1) (numeral x ∷ 0) (qVec ℒₒᵣ (toNumVec e).val) = numeral x ∷ (toNumVec e).val by ext; simpa
    refine nth_ext' ((↑n : V) + 1) ?_ ?_ ?_
    · rw [len_termSubstVec (L := ℒₒᵣ)]
      · simp
      simpa using (toNumVec e).prop.qVec.isUTerm
    · simp [(toNumVec e).prop.lh]
    · intro i hi
      suffices
        termSubst ℒₒᵣ (numeral x ∷ 0) (qVec ℒₒᵣ (toNumVec e).val).[i] = (numeral x ∷ (toNumVec e).val).[i] by
          rwa [nth_termSubstVec (V := V) (L := ℒₒᵣ) (k := ↑(n + 1)) (by simpa using (toNumVec e).prop.qVec.isUTerm) hi]
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [qVec]
      · simp only [qVec, nth_cons_succ]
        rcases eq_fin_of_lt_nat (by simpa using hi) with ⟨i, rfl⟩
        rw [nth_termBShiftVec (L := ℒₒᵣ) (by simp),
          toNumVec_val_nth, numeral_bShift,
          numeral_substs (n := 1) (m := 0) (by simp)]
        simp
  rw [this]
  ext; simp [toNumVec, Matrix.comp_vecCons']

namespace TProof

open TProof Entailment

variable (T)

noncomputable abbrev num (n : V) := typedNumeral 0 n

scoped prefix:max "⇣" => num

@[simp] lemma eq_refl (t : Term V ℒₒᵣ) : T.internalize V ⊢! t ≐ t := by sorry

lemma eq_symm {t₁ t₂ : Term V ℒₒᵣ} : T.internalize V ⊢! (t₁ ≐ t₂) ➝ (t₂ ≐ t₁) := by sorry

lemma eq_trans {t₁ t₂ t₃ : Term V ℒₒᵣ} : T.internalize V ⊢! (t₁ ≐ t₂) ➝ (t₂ ≐ t₃) ➝ (t₁ ≐ t₃) := by sorry

lemma add_ext {t₁ u₁ t₂ u₂ : Term V ℒₒᵣ} : T.internalize V ⊢! (t₁ ≐ t₂) ➝ (u₁ ≐ u₂) ➝ (t₁ + u₁ ≐ t₂ + u₂) := by sorry

lemma mul_ext {t₁ u₁ t₂ u₂ : Term V ℒₒᵣ} : T.internalize V ⊢! (t₁ ≐ t₂) ➝ (u₁ ≐ u₂) ➝ (t₁ * u₁ ≐ t₂ * u₂) := by sorry

lemma numeral_add (n m : V) : T.internalize V ⊢! ⇣n + ⇣m ≐ ⇣(n + m) := sorry

lemma numeral_mul (n m : V) : T.internalize V ⊢! ⇣n * ⇣m ≐ ⇣(n * m) := sorry

lemma numeral_ne {n m : V} (h : n ≠ m) : T.internalize V ⊢! ⇣n ≉ ⇣m := sorry

lemma lt_ext {t₁ u₁ t₂ u₂ : Term V ℒₒᵣ} : T.internalize V ⊢! (t₁ ≐ t₂) ➝ (u₁ ≐ u₂) ➝ (t₁ <' u₁) ➝ (t₂ <' u₂) := sorry

lemma numeral_lt {n m : V} (h : n < m) : T.internalize V ⊢! ⇣n <' ⇣m := sorry

lemma numeral_nlt {n m : V} (h : n ≥ m) : T.internalize V ⊢! ⇣n ≮' ⇣m := sorry

lemma nlt_numeral (t : Term V ℒₒᵣ) (n : V) :
  T.internalize V ⊢! (t ≮' ⇣n) ⭤ (tSubstItr t.sing (#'1 ≉ #'0) n).conj := sorry

variable {T}

lemma eq_comm {t₁ t₂ : Term V ℒₒᵣ} :
    T.internalize V ⊢! t₁ ≐ t₂ → T.internalize V ⊢! t₂ ≐ t₁ := fun h ↦ eq_symm T ⨀ h

lemma eq_compose {t₁ t₂ t₃ : Term V ℒₒᵣ} :
    T.internalize V ⊢! t₁ ≐ t₂ → T.internalize V ⊢! t₂ ≐ t₃ → T.internalize V ⊢! t₁ ≐ t₃ := fun h₁ h₂ ↦ eq_trans T ⨀! h₁ ⨀! h₂

variable (T)

theorem term_complete {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ Empty n) (e : Fin n → V) :
    T.internalize V ⊢! ⌜t⌝^ᵗ/[toNumVec e] ≐ ⇣(t.valbm V e) :=
  match t with
  |                         #z => by simp [Semiterm.typed_quote_empty_def]
  |                         &x => Empty.elim x
  | .func Language.Zero.zero v => by simp [Semiterm.typed_quote_empty_def]
  |   .func Language.One.one v => by simp [Semiterm.typed_quote_empty_def]
  |   .func Language.Add.add v => by
      suffices
          T.internalize V ⊢! ⌜v 0⌝^ᵗ/[toNumVec e] + ⌜v 1⌝^ᵗ/[toNumVec e] ≐ ⇣((v 0).valbm V e + (v 1).valbm V e) by
        simpa [Rew.func, Semiterm.val_func, Semiterm.typed_quote_empty_def]
      have ih : T.internalize V ⊢! ⌜v 0⌝^ᵗ/[toNumVec e] + ⌜v 1⌝^ᵗ/[toNumVec e] ≐ ⇣((v 0).valbm V e) + ⇣((v 1).valbm V e) :=
        add_ext T ⨀ term_complete (v 0) e ⨀ term_complete (v 1) e
      have : T.internalize V ⊢! ⇣((v 0).valbm V e) + ⇣((v 1).valbm V e) ≐ ⇣((v 0).valbm V e + (v 1).valbm V e) := numeral_add T _ _
      exact eq_compose ih this
  |   .func Language.Mul.mul v => by
      suffices
          T.internalize V ⊢! ⌜v 0⌝^ᵗ/[toNumVec e] * ⌜v 1⌝^ᵗ/[toNumVec e] ≐ ⇣((v 0).valbm V e * (v 1).valbm V e) by
        simpa [Rew.func, Semiterm.val_func, Semiterm.typed_quote_empty_def]
      have ih : T.internalize V ⊢! ⌜v 0⌝^ᵗ/[toNumVec e] * ⌜v 1⌝^ᵗ/[toNumVec e] ≐ ⇣((v 0).valbm V e) * ⇣((v 1).valbm V e) :=
        mul_ext T ⨀ term_complete (v 0) e ⨀ term_complete (v 1) e
      have : T.internalize V ⊢! ⇣((v 0).valbm V e) * ⇣((v 1).valbm V e) ≐ ⇣((v 0).valbm V e * (v 1).valbm V e) := numeral_mul T _ _
      exact eq_compose ih this

open FirstOrder.Arithmetic

theorem bold_sigma₁_complete {n} {φ : Semisentence ℒₒᵣ n} (hp : Hierarchy 𝚺 1 φ) {e} :
    V ⊧/e φ → T.internalize V ⊢! ⌜φ⌝^/[toNumVec e] := by
  revert e
  apply sigma₁_induction' hp
  case hVerum => intro n; simp
  case hFalsum => intro n; simp
  case hEQ =>
    intro n t₁ t₂ e h
    suffices T.internalize V ⊢! ⌜t₁⌝^ᵗ/[toNumVec e] ≐ ⌜t₂⌝^ᵗ/[toNumVec e] by
      simpa [Semiformula.quote_semisentence_def]
    have : t₁.valbm V e = t₂.valbm V e := by simpa using h
    have h₀ : T.internalize V ⊢!     ⇣(t₁.valbm V e) ≐ ⇣(t₂.valbm V e) := by simp [this]
    have h₁ : T.internalize V ⊢! ⌜t₁⌝^ᵗ/[toNumVec e] ≐ ⇣(t₁.valbm V e) := term_complete T t₁ e
    have h₂ : T.internalize V ⊢! ⌜t₂⌝^ᵗ/[toNumVec e] ≐ ⇣(t₂.valbm V e) := term_complete T t₂ e
    exact eq_compose (eq_compose h₁ h₀) (eq_comm h₂)
  case hNEQ =>
    intro n t₁ t₂ e h
    suffices T.internalize V ⊢! ∼(⌜t₁⌝^ᵗ/[toNumVec e] ≐ ⌜t₂⌝^ᵗ/[toNumVec e]) by
      simpa [Semiformula.quote_semisentence_def]
    have : t₁.valbm V e ≠ t₂.valbm V e := by simpa using h
    have h₀ : T.internalize V ⊢! ∼(⇣(Semiterm.valbm V e t₁) ≐ ⇣(Semiterm.valbm V e t₂)) := by simpa using numeral_ne T this
    have h₁ : T.internalize V ⊢! ⌜t₁⌝^ᵗ/[toNumVec e] ≐ ⇣(t₁.valbm V e) := term_complete T t₁ e
    have h₂ : T.internalize V ⊢! ⌜t₂⌝^ᵗ/[toNumVec e] ≐ ⇣(t₂.valbm V e) := term_complete T t₂ e
    sorry
  case hLT =>
    intro n t₁ t₂ e h
    suffices T.internalize V ⊢! ⌜t₁⌝^ᵗ/[toNumVec e] <' ⌜t₂⌝^ᵗ/[toNumVec e] by
      simpa [Semiformula.quote_semisentence_def]
    sorry
  case hNLT =>
    intro n t₁ t₂ e h
    suffices T.internalize V ⊢! ∼(⌜t₁⌝^ᵗ/[toNumVec e] <' ⌜t₂⌝^ᵗ/[toNumVec e]) by
      simpa [Semiformula.quote_semisentence_def]
    sorry
  case hAnd =>
    intro n φ ψ _ _ ihφ ihψ e h
    have H : V ⊧/e φ ∧ V ⊧/e ψ := by simpa using  h
    simpa using K!_intro (ihφ H.1) (ihψ H.2)
  case hBall =>
    intro n t φ _ ihp e h
    suffices
        Theory.internalize V T ⊢!
          Semiformula.ball (⌜t⌝^ᵗ/[toNumVec e]) ((⌜φ⌝ : Semiformula V ℒₒᵣ ↑(n + 1)).sCast^/[(toNumVec e).q]) by
      simpa
    apply TProof.all!
    simp [Semiformula.free, Semiformula.substs1]
    suffices
      T.internalize V ⊢
        (&'0 ≮' (⌜t⌝^ᵗ/[toNumVec e])) ⋎
        ((.sCast ⌜φ⌝ : Semiformula V ℒₒᵣ (↑n + 1))^/[(toNumVec e).q]).shift^/[(&'0).sing] by
      simp [←Semiterm.bShift_shift_comm]
    have : T.internalize V ⊢ (tSubstItr (&'0).sing (#'1 ≉ #'0) n).conj ⋎ φ.shift^/[(&'0).sing] := by
      apply TProof.conjOr'
      intro i hi
      have hi : i < n := by simpa using hi
      let Γ := [&'0 ≐ typedNumeral 0 i]
      suffices Γ ⊢[T.internalize V] φ.shift^/[(&'0).sing] by
        simpa [nth_tSubstItr', hi, Semiformula.imp_def] using deduct' this
      have e : Γ ⊢[T.internalize V] ↑i ≐ &'0 := sorry
      have : T.internalize V ⊢ φ.shift^/[(i : Term V ℒₒᵣ).sing] := by
        simpa [Language.TSemifromula.shift_substs] using TProof.shift (bs i hi)
      sorry--exact of (replace T φ.shift ↑i &'0) ⨀ e ⨀ of this
    exact A_replace_left this (K_right (nltNumeral T (&'0) n))





  sorry


/--/

    refine eq_ext T _ _ _ _ ⨀ ?_ ⨀ ?_ ⨀ eq_complete! T this
    · exact eq_symm'! _ <| termEq_complete! T e t₁
    · exact eq_symm'! _ <| termEq_complete! T e t₂
  case hNEQ =>
    intro n t₁ t₂ e h
    have : t₁.valbm V e ≠ t₂.valbm V e := by simpa using h
    suffices T.internalize V ⊢! ⌜Rew.embs t₁⌝^ᵗ/[toNumVec e] ≉ ⌜Rew.embs t₂⌝^ᵗ/[toNumVec e] by
      simpa only [Semiformula.rew_nrel2, Semiformula.codeIn'_neq, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.vecHead, Matrix.cons_val_fin_one, substs_notEquals] using this
    refine ne_ext T _ _ _ _ ⨀ ?_ ⨀ ?_ ⨀ ne_complete! T this
    · exact eq_symm'! _ <| termEq_complete! T e t₁
    · exact eq_symm'! _ <| termEq_complete! T e t₂
  case hLT =>
    intro n t₁ t₂ e h
    have : t₁.valbm V e < t₂.valbm V e := by simpa using h
    suffices T.internalize V ⊢! ⌜Rew.embs t₁⌝^ᵗ/[toNumVec e] <' ⌜Rew.embs t₂⌝^ᵗ/[toNumVec e] by
      simpa only [Semiformula.rew_rel2, Semiformula.codeIn'_lt, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.vecHead, Matrix.cons_val_fin_one, substs_lessThan] using this
    refine lt_ext! T _ _ _ _ ⨀ ?_ ⨀ ?_ ⨀ lt_complete! T this
    · exact eq_symm'! _ <| termEq_complete! T e t₁
    · exact eq_symm'! _ <| termEq_complete! T e t₂
  case hNLT =>
    intro n t₁ t₂ e h
    have : t₂.valbm V e ≤ t₁.valbm V e := by simpa using h
    suffices T.internalize V ⊢! ⌜Rew.embs t₁⌝^ᵗ/[toNumVec e] ≮' ⌜Rew.embs t₂⌝^ᵗ/[toNumVec e] by
      simpa only [Semiformula.rew_nrel2, Semiformula.codeIn'_nlt, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.vecHead, Matrix.cons_val_fin_one, substs_notLessThan] using this
    refine nlt_ext T _ _ _ _ ⨀ ?_ ⨀ ?_ ⨀ nlt_complete T this
    · exact eq_symm'! _ <| termEq_complete! T e t₁
    · exact eq_symm'! _ <| termEq_complete! T e t₂
  case hAnd =>
    intro n φ ψ _ _ ihp ihq e h
    have h : Semiformula.Evalbm V e φ ∧ Semiformula.Evalbm V e ψ := by simpa using h
    simpa only [LogicalConnective.HomClass.map_and, Semiformula.codeIn'_and,
      Semiformula.substs_and] using K!_intro (ihp h.1) (ihq h.2)
  case hOr =>
    intro n φ ψ _ _ ihp ihq e h
    have : Semiformula.Evalbm V e φ ∨ Semiformula.Evalbm V e ψ := by simpa using h
    rcases this with (h | h)
    · simpa only [LogicalConnective.HomClass.map_or, Semiformula.codeIn'_or,
      Semiformula.substs_or] using A!_intro_left (ihp h)
    · simpa only [LogicalConnective.HomClass.map_or, Semiformula.codeIn'_or,
      Semiformula.substs_or] using A!_intro_right (ihq h)
  case hBall =>
    intro n t φ _ ihp e h
    suffices T.internalize V ⊢! Semiformula.ball (⌜Rew.emb t⌝^ᵗ/[toNumVec e]) ((_)^/[(toNumVec e).q]) by
      simpa only [Rewriting.smul_ball, Rew.q_emb, Rew.hom_finitary2, Rew.emb_bvar, ← Rew.emb_bShift_term,
        Semiformula.codeIn'_ball, substs_ball]
    apply ball_replace! T _ _ _ ⨀ (eq_symm! T _ _ ⨀ termEq_complete! T e t) ⨀ ?_
    apply ball_intro!
    intro x hx
    suffices T.internalize V ⊢! ⌜Rew.embs ▹ φ⌝^/[toNumVec (x :> e)] by simpa [Language.TSemifromula.substs_substs]
    have : Semiformula.Evalbm V (x :> e) φ := by
      have : ∀ x < t.valbm V e, Semiformula.Evalbm V (x :> e) φ := by simpa using h
      exact this x hx
    exact ihp this
  case hEx =>
    intro n φ _ ihp e h
    simp only [Rewriting.app_ex, Rew.q_emb, Semiformula.codeIn'_ex, Semiformula.substs_ex]
    have : ∃ x, Semiformula.Evalbm V (x :> e) φ := by simpa using h
    rcases this with ⟨x, hx⟩
    apply ex! x
    simpa [Language.TSemifromula.substs_substs] using ihp hx

/-- Hilbert–Bernays provability condition D3 -/
theorem sigma₁_complete {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) : V ⊧ₘ₀ σ → T.internalize V ⊢! ⌜σ⌝ := by
  intro h; simpa using bold_sigma₁_complete T hσ (e := ![]) (by simpa [models₀_iff] using h)

end TProof

end InternalArithmetic

section

variable {T : ArithmeticTheory} [T.Δ₁Definable]

theorem sigma₁_complete {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    V ⊧ₘ₀ σ → T.Provable (⌜σ⌝ : V) := fun h ↦ by
  simpa [provable_iff] using InternalArithmetic.TProof.sigma₁_complete _ hσ h

theorem sigma₁_complete_provable {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    V ⊧ₘ₀ σ → T†V ⊢! ⌜σ⌝ := fun h ↦ by
  simpa [provable_iff] using InternalArithmetic.TProof.sigma₁_complete _ hσ h

end

section D2

variable {T : ArithmeticTheory} [T.Δ₁Definable]

/-- Hilbert–Bernays provability condition D2 -/
theorem modus_ponens {φ ψ : SyntacticFormula ℒₒᵣ} (hφψ : T.Provable (⌜φ ➝ ψ⌝ : V)) (hφ : T.Provable (⌜φ⌝ : V)) :
    T.Provable (⌜ψ⌝ : V) := provable_iff'.mpr <| (by simpa using provable_iff'.mp hφψ) ⨀ provable_iff'.mp hφ

theorem modus_ponens₀ {σ τ : Sentence ℒₒᵣ} (hστ : T.Provable (⌜σ ➝ τ⌝ : V)) (hσ : T.Provable (⌜σ⌝ : V)) :
    T.Provable (⌜τ⌝ : V) := provable_iff.mpr <| (by simpa using provable_iff.mp hστ) ⨀ provable_iff.mp hσ

end D2

end LO.ISigma1.Metamath
