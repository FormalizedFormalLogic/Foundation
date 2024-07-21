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
  | _, _, Hierarchy.verum _ _ _,               _, h => by simp
  | _, _, Hierarchy.falsum _ _ _,              _, h => by simp at h
  | _, _, Hierarchy.rel _ _ Language.Eq.eq v,  e, h => by { simp [Rew.rel]; sorry }
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
  | _, _, Hierarchy.ball pt hp,                e, h => by {
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    have := termEqComplete T e t
    simp [←Rew.emb_bShift_term]
    sorry


       }
  | _, _, Hierarchy.bex pt hp,                 e, h => by sorry
  | _, _, Hierarchy.sigma (p := p) hp,         e, h => by sorry
  | _, _, Hierarchy.ex hp,                     e, h => by sorry

end TProof

end Formalized

end LO.Arith

end
