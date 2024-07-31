import Arithmetization.ISigmaOne.Metamath.Theory.R
import Arithmetization.ISigmaOne.Metamath.DerivabilityConditions.D1

/-!

# Formalized $\Sigma_1$-Completeness

-/

noncomputable section

open Classical

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

namespace Formalized

variable {T : LOR.TTheory (V := V)} [R₀Theory T.thy]

def toNumVec {n} (e : Fin n → V) : (Language.codeIn ℒₒᵣ V).TSemitermVec n 0 :=
  ⟨⌜fun i ↦ numeral (e i)⌝, by simp, by
    intro i hi
    rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    simp [quote_nth_fin (fun i ↦ numeral (e i)) i]⟩

@[simp] lemma toNumVec_nil : (toNumVec (![] : Fin 0 → V)) = .nil _ _ := by ext; simp [toNumVec]

@[simp] lemma toNumVec_nth {n} (e : Fin n → V) (i : Fin n) : (toNumVec e).nth i = ↑(e i) := by ext; simp [toNumVec]

@[simp] lemma toNumVec_val_nth {n} (e : Fin n → V) (i : Fin n) : (toNumVec e).val.[i] = numeral (e i) := by simp [toNumVec]

/-- TODO: move-/
@[simp] lemma coe_coe_lt {n} (i : Fin n) : (i : V) < (n : V) :=
  calc (i : V) < (i : V) + (n - i : V) := by simp
  _  = (n : V) := by simp

@[simp] lemma cast_substs_numVec (p : Semisentence ℒₒᵣ (n + 1)) :
    ((.cast (V := V) (n := ↑(n + 1)) (n' := ↑n + 1) ⌜Rew.embs.hom p⌝ (by simp)) ^/[(toNumVec e).q.substs (typedNumeral 0 x).sing]) =
    ⌜Rew.embs.hom p⌝ ^/[toNumVec (x :> e)] := by
  have : (toNumVec e).q.substs (typedNumeral 0 x).sing = x ∷ᵗ toNumVec e := by
    ext; simp
    apply nth_ext' ((↑n : V) + 1)
      (by rw [len_termSubstVec]; simpa using (toNumVec e).prop.qVec)
      (by simp [←(toNumVec e).prop.1])
    intro i hi
    rw [nth_termSubstVec (by simpa using (toNumVec e).prop.qVec) hi]
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp [Language.qVec]
    · simp only [Language.qVec, nth_cons_succ, Language.TSemitermVec.prop]
      rcases eq_fin_of_lt_nat (by simpa using hi) with ⟨i, rfl⟩
      rw [nth_termBShiftVec (by simp)]
      simp; exact coe_coe_lt (V := V) i
  rw [this]
  ext; simp [toNumVec]


namespace TProof

open Language.Theory.TProof System

variable (T)

noncomputable def termEqComplete {n : ℕ} (e : Fin n → V) :
    (t : Semiterm ℒₒᵣ Empty n) → T ⊢ ⌜Rew.embs t⌝^ᵗ/[toNumVec e] =' ↑(t.valbm V e)
  | #z                                 => by simpa using eqRefl T (e z)
  | &x                                 => Empty.elim x
  | Semiterm.func Language.Zero.zero v => by simpa using eqRefl T _
  | Semiterm.func Language.One.one v   => by simpa using eqRefl T _
  | Semiterm.func Language.Add.add v   => by
      simp [Rew.func, Semiterm.val_func]
      have ih : T ⊢ (⌜Rew.embs (v 0)⌝^ᵗ/[toNumVec e] + ⌜Rew.embs (v 1)⌝^ᵗ/[toNumVec e]) =' (↑((v 0).valbm V e) + ↑((v 1).valbm V e)) :=
        addExt T _ _ _ _ ⨀ termEqComplete e (v 0) ⨀ termEqComplete e (v 1)
      have : T ⊢ (↑((v 0).valbm V e) + ↑((v 1).valbm V e)) =' ↑((v 0).valbm V e + (v 1).valbm V e) := addComplete T _ _
      exact eqTrans T _ _ _ ⨀ ih ⨀ this
  | Semiterm.func Language.Mul.mul v   => by
      simp [Rew.func, Semiterm.val_func]
      have ih : T ⊢ (⌜Rew.embs (v 0)⌝^ᵗ/[toNumVec e] * ⌜Rew.embs (v 1)⌝^ᵗ/[toNumVec e]) =' (↑((v 0).valbm V e) * ↑((v 1).valbm V e)) :=
        mulExt T _ _ _ _ ⨀ termEqComplete e (v 0) ⨀ termEqComplete e (v 1)
      have : T ⊢ (↑((v 0).valbm V e) * ↑((v 1).valbm V e)) =' ↑((v 0).valbm V e * (v 1).valbm V e) := mulComplete T _ _
      exact eqTrans T _ _ _ ⨀ ih ⨀ this

lemma termEq_complete! {n : ℕ} (e : Fin n → V) (t : Semiterm ℒₒᵣ Empty n) :
    T ⊢! ⌜Rew.embs t⌝^ᵗ/[toNumVec e] =' ↑(t.valbm V e) := ⟨termEqComplete T e t⟩

open FirstOrder.Arith

theorem bold_sigma₁_complete {n} {p : Semisentence ℒₒᵣ n} (hp : Hierarchy 𝚺 1 p) {e} :
    V ⊧/e p → T ⊢! ⌜Rew.embs.hom p⌝^/[toNumVec e] := by
  revert e
  apply sigma₁_induction' hp
  case hVerum => intro n; simp
  case hFalsum =>
    intro n
    simp only [LogicalConnective.HomClass.map_bot, Prop.bot_eq_false,
      Semiformula.codeIn'_falsum, Language.TSemiformula.substs_falsum, false_implies, implies_true]
  case hEQ =>
    intro n t₁ t₂ e h
    have : t₁.valbm V e = t₂.valbm V e := by simpa using h
    suffices T ⊢! ⌜Rew.embs t₁⌝^ᵗ/[toNumVec e] =' ⌜Rew.embs t₂⌝^ᵗ/[toNumVec e] by
      simpa only [Rew.rel2, Semiformula.codeIn'_eq, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.vecHead, Matrix.cons_val_fin_one, substs_equals] using this
    refine eq_ext T _ _ _ _ ⨀ ?_ ⨀ ?_ ⨀ eq_complete! T this
    · exact eq_symm'! _ <| termEq_complete! T e t₁
    · exact eq_symm'! _ <| termEq_complete! T e t₂
  case hNEQ =>
    intro n t₁ t₂ e h
    have : t₁.valbm V e ≠ t₂.valbm V e := by simpa using h
    suffices T ⊢! ⌜Rew.embs t₁⌝^ᵗ/[toNumVec e] ≠' ⌜Rew.embs t₂⌝^ᵗ/[toNumVec e] by
      simpa only [Rew.nrel2, Semiformula.codeIn'_neq, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.vecHead, Matrix.cons_val_fin_one, substs_notEquals] using this
    refine ne_ext T _ _ _ _ ⨀ ?_ ⨀ ?_ ⨀ ne_complete! T this
    · exact eq_symm'! _ <| termEq_complete! T e t₁
    · exact eq_symm'! _ <| termEq_complete! T e t₂
  case hLT => sorry
  case hNLT => sorry
  case hAnd =>
    intro n p q hp hq ihp ihq e h
    have h : Semiformula.Evalbm V e p ∧ Semiformula.Evalbm V e q := by simpa using h
    simpa only [LogicalConnective.HomClass.map_and, Semiformula.codeIn'_and,
      Language.TSemiformula.substs_and] using and_intro! (ihp h.1) (ihq h.2)
  case hOr =>
    intro n p q hp hq ihp ihq e h
    have : Semiformula.Evalbm V e p ∨ Semiformula.Evalbm V e q := by simpa using h
    rcases this with (h | h)
    · simpa only [LogicalConnective.HomClass.map_or, Semiformula.codeIn'_or,
      Language.TSemiformula.substs_or] using or₁'! (ihp h)
    · simpa only [LogicalConnective.HomClass.map_or, Semiformula.codeIn'_or,
      Language.TSemiformula.substs_or] using or₂'! (ihq h)
  case hBall =>
    intro n t p hp ihp e h
    simp only [Rew.ball, Rew.q_emb, Rew.hom_finitary2, Rew.emb_bvar, ← Rew.emb_bShift_term,
      Semiformula.codeIn'_ball, substs_ball]
    apply ball_replace! T _ _ _ ⨀ (eq_symm! T _ _ ⨀ termEq_complete! T e t) ⨀ ?_
    apply ball_intro!
    intro x hx
    suffices T ⊢! ⌜Rew.embs.hom p⌝^/[toNumVec (x :> e)]  by
      simpa [Language.TSemifromula.substs_substs]
    have : Semiformula.Evalbm V (x :> e) p := by
      simp at h; exact h x hx
    exact ihp this
  case hEx =>
    intro n p hp ihp e h
    simp only [Rew.ex, Rew.q_emb, Semiformula.codeIn'_ex, Language.TSemiformula.substs_ex]
    have : ∃ x, Semiformula.Evalbm V (x :> e) p := by simpa using h
    rcases this with ⟨x, hx⟩
    apply ex! x
    simpa [Language.TSemifromula.substs_substs] using ihp hx

/-- Hilbert–Bernays provability condition D3 -/
theorem sigma₁_complete {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) : V ⊧ₘ σ → T ⊢! ⌜σ⌝ := by
  intro h; simpa using bold_sigma₁_complete T hσ (e := ![]) h

end TProof

end Formalized

/-
end LO.Arith

namespace LO.FirstOrder.Theory

open LO.Arith LO.Arith.Formalized

variable (T : Theory ℒₒᵣ) [Arith.DefinableSigma₁Theory T]

class ISigma₁EQaddR₀ where
  EQ : ∀ (V : Type) [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁], EQTheory (Theory.codeIn V T)
  R0 : ∀ (V : Type) [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁], R₀Theory (Theory.codeIn V T)

end LO.FirstOrder.Theory

namespace LO.Arith.Formalized

open LO.FirstOrder

variable {V : Type} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable (T : Theory ℒₒᵣ) [Arith.DefinableSigma₁Theory T]

instance [T.ISigma₁EQaddR₀] : EQTheory (Theory.codeIn V T) := Theory.ISigma₁EQaddR₀.EQ V

instance [T.ISigma₁EQaddR₀] : R₀Theory (Theory.codeIn V T) := Theory.ISigma₁EQaddR₀.R0 V

end LO.Arith.Formalized

end
-/
