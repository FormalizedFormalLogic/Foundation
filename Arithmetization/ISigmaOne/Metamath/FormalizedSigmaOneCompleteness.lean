import Arithmetization.ISigmaOne.Metamath.Proof.R
import Arithmetization.ISigmaOne.Metamath.Coding

/-!

# Formalized $\Sigma_1$-Completeness

-/

namespace LO.FirstOrder.Rew

variable {L : Language}

abbrev embₙ {o : Type v₁} [IsEmpty o] {n} : Rew L o n ℕ n := emb

lemma emb_comp_bShift_comm {o : Type v₁} [IsEmpty o] :
    Rew.bShift.comp (Rew.emb : Rew L o n ξ n) = Rew.emb.comp Rew.bShift := by
  ext x; simp [comp_app]
  exact IsEmpty.elim (by assumption) x

lemma emb_bShift_term {o : Type v₁} [IsEmpty o] (t : Semiterm L o n) :
    Rew.bShift (Rew.emb t : Semiterm L ξ n) = Rew.emb (Rew.bShift t) := by
  simp [←comp_app, emb_comp_bShift_comm]

end LO.FirstOrder.Rew

noncomputable section

open Classical

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

namespace Formalized

variable {T : LOR.Theory V} {pT : (Language.lDef ℒₒᵣ).TDef} [T.Defined pT] [EQTheory T] [R₀Theory T]

def toNumVec {n} (e : Fin n → V) : (Language.codeIn ℒₒᵣ V).TSemitermVec n 0 :=
  ⟨⌜fun i ↦ numeral (e i)⌝, by simp, by
    intro i hi
    rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    simp [quote_nth_fin (fun i ↦ numeral (e i)) i]⟩

@[simp] lemma toNumVec_nth {n} (e : Fin n → V) (i : Fin n) : (toNumVec e).nth i = ↑(e i) := by ext; simp [toNumVec]

@[simp] lemma toNumVec_val_nth {n} (e : Fin n → V) (i : Fin n) : (toNumVec e).val.[i] = numeral (e i) := by simp [toNumVec]

/-- TODO: move-/
@[simp] lemma coe_coe_lt {n} (i : Fin n) : (i : V) < (n : V) :=
  calc (i : V) < (i : V) + (n - i : V) := by simp
  _  = (n : V) := by simp

@[simp] lemma cast_substs_numVec (p : Semisentence ℒₒᵣ (n + 1)) :
    ((.cast (V := V) (n := ↑(n + 1)) (n' := ↑n + 1) ⌜Rew.embₙ.hom p⌝ (by simp)) ^/[(toNumVec e).q.substs (typedNumeral 0 x).sing]) =
    ⌜Rew.embₙ.hom p⌝ ^/[toNumVec (x :> e)] := by
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
    (t : Semiterm ℒₒᵣ Empty n) → T ⊢ ⌜Rew.embₙ t⌝^ᵗ/[toNumVec e] =' ↑(t.valbm V e)
  | #z                                 => by simpa using eqRefl T (e z)
  | &x                                 => Empty.elim x
  | Semiterm.func Language.Zero.zero v => by simpa using eqRefl T _
  | Semiterm.func Language.One.one v   => by simpa using eqRefl T _
  | Semiterm.func Language.Add.add v   => by
      simp [Rew.func, Semiterm.val_func]
      have ih : T ⊢ (⌜Rew.embₙ (v 0)⌝^ᵗ/[toNumVec e] + ⌜Rew.embₙ (v 1)⌝^ᵗ/[toNumVec e]) =' (↑((v 0).valbm V e) + ↑((v 1).valbm V e)) :=
        addExt T _ _ _ _ ⨀ termEqComplete e (v 0) ⨀ termEqComplete e (v 1)
      have : T ⊢ (↑((v 0).valbm V e) + ↑((v 1).valbm V e)) =' ↑((v 0).valbm V e + (v 1).valbm V e) := addComplete T _ _
      exact eqTrans T _ _ _ ⨀ ih ⨀ this
  | Semiterm.func Language.Mul.mul v   => by
      simp [Rew.func, Semiterm.val_func]
      have ih : T ⊢ (⌜Rew.embₙ (v 0)⌝^ᵗ/[toNumVec e] * ⌜Rew.embₙ (v 1)⌝^ᵗ/[toNumVec e]) =' (↑((v 0).valbm V e) * ↑((v 1).valbm V e)) :=
        mulExt T _ _ _ _ ⨀ termEqComplete e (v 0) ⨀ termEqComplete e (v 1)
      have : T ⊢ (↑((v 0).valbm V e) * ↑((v 1).valbm V e)) =' ↑((v 0).valbm V e * (v 1).valbm V e) := mulComplete T _ _
      exact eqTrans T _ _ _ ⨀ ih ⨀ this

lemma termEq_complete! {n : ℕ} (e : Fin n → V) (t : Semiterm ℒₒᵣ Empty n) :
    T ⊢! ⌜Rew.embₙ t⌝^ᵗ/[toNumVec e] =' ↑(t.valbm V e) := ⟨termEqComplete T e t⟩

open FirstOrder.Arith

theorem boldSigma₁Complete : ∀ {n} {σ : Semisentence ℒₒᵣ n},
    Hierarchy 𝚺 1 σ → ∀ {e}, Semiformula.Evalbm V e σ → T ⊢! ⌜Rew.embₙ.hom σ⌝^/[toNumVec e]
  | _, _, Hierarchy.verum _ _ _,               _, h => by simp only [LogicalConnective.HomClass.map_top,
    Semiformula.codeIn'_verum, Language.TSemiformula.substs_verum, Language.TSemiformula.neg_verum,
    Language.TSemiformula.neg_falsum, verum!, dne'!]
  | _, _, Hierarchy.falsum _ _ _,              _, h => by sorry
  | _, _, Hierarchy.rel _ _ Language.Eq.eq v,  e, h => by sorry
  | _, _, Hierarchy.nrel _ _ Language.Eq.eq v, e, h => by sorry
  | _, _, Hierarchy.rel _ _ Language.LT.lt v,  e, h => by sorry
  | _, _, Hierarchy.nrel _ _ Language.LT.lt v, e, h => by sorry
  | _, _, Hierarchy.and (p := p) (q := q) hp hq,                 e, h => by
    have h : Semiformula.Evalbm V e p ∧ Semiformula.Evalbm V e q := by simpa using h
    simpa using and_intro! (boldSigma₁Complete hp h.1) (boldSigma₁Complete hq h.2)
  | _, _, Hierarchy.or (p := p) (q := q) hp hq,                  e, h => by
    have : Semiformula.Evalbm V e p ∨ Semiformula.Evalbm V e q := by simpa using h
    rcases this with (h | h)
    · simpa using or₁'! (boldSigma₁Complete hp h)
    · simpa using or₂'! (boldSigma₁Complete hq h)
  | _, _, Hierarchy.ball (p := p) pt hp,                e, h => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    simp only [Rew.ball, Rew.q_emb, Rew.hom_finitary2, Rew.emb_bvar, ← Rew.emb_bShift_term,
      Semiformula.codeIn'_ball, substs_ball]
    apply ball_replace! T _ _ _ ⨀ (eq_symm! T _ _ ⨀ termEq_complete! T e t) ⨀ ?_
    apply ball_intro!
    intro x hx
    suffices T ⊢! ⌜Rew.embₙ.hom p⌝^/[toNumVec (x :> e)]  by
      simpa [Language.TSemifromula.substs_substs]
    have : Semiformula.Evalbm V (x :> e) p := by
      simp at h; exact h x hx
    exact boldSigma₁Complete hp this
  | _, _, Hierarchy.bex (p := p) (t := t) pt hp,                 e, h => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    simp only [Rew.bex, Rew.q_emb, Rew.hom_finitary2, Rew.emb_bvar, ← Rew.emb_bShift_term,
      Semiformula.codeIn'_bex, substs_bex]
    apply bex_replace! T _ _ _ ⨀ (eq_symm! T _ _ ⨀ termEq_complete! T e t) ⨀ ?_
    have : ∃ x < t.valbm V e, Semiformula.Evalbm V (x :> e) p := by simpa using h
    rcases this with ⟨x, hx, Hx⟩
    apply bex_intro! T _ _ hx
    simpa [Language.TSemifromula.substs_substs] using boldSigma₁Complete hp Hx
  | _, _, Hierarchy.sigma (p := p) hp,         e, h => by
    have hp : Hierarchy 𝚺 1 p := hp.accum _
    simp only [Rew.ex, Rew.q_emb, Semiformula.codeIn'_ex, Language.TSemiformula.substs_ex]
    have : ∃ x, Semiformula.Evalbm V (x :> e) p := by simpa using h
    rcases this with ⟨x, hx⟩
    apply ex! x
    simpa [Language.TSemifromula.substs_substs] using boldSigma₁Complete hp hx
  | _, _, Hierarchy.ex (p := p) hp,                     e, h => by
    simp only [Rew.ex, Rew.q_emb, Semiformula.codeIn'_ex, Language.TSemiformula.substs_ex]
    have : ∃ x, Semiformula.Evalbm V (x :> e) p := by simpa using h
    rcases this with ⟨x, hx⟩
    apply ex! x
    simpa [Language.TSemifromula.substs_substs] using boldSigma₁Complete hp hx

end TProof

end Formalized

end LO.Arith

end
