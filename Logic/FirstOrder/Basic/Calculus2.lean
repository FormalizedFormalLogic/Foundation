import Logic.FirstOrder.Basic.Calculus

/-!

# Derivation2

Different characterizations of proof.

-/

namespace LO.FirstOrder

variable {L : Language} [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]

open Semiformula

def SyntacticTheory.close (T : SyntacticTheory L) : Theory L := Semiformula.close '' T

inductive Derivation2 (T : SyntacticTheory L) : Sequent L → Type _
| axL (Γ) {k} (r : L.Rel k) (v) : Derivation2 T (rel r v :: nrel r v :: Γ)
| root (Γ) {p} : p ∈ T → Derivation2 T (p :: Γ)
| verum (Γ)    : Derivation2 T (⊤ :: Γ)
| or {Γ p q}   : Derivation2 T (p :: q :: Γ) → Derivation2 T (p ⋎ q :: Γ)
| and {Γ p q}  : Derivation2 T (p :: Γ) → Derivation2 T (q :: Γ) → Derivation2 T (p ⋏ q :: Γ)
| all {Γ p}    : Derivation2 T (Rew.free.hom p :: Γ⁺) → Derivation2 T ((∀' p) :: Γ)
| ex {Γ p} (t) : Derivation2 T (p/[t] :: Γ) → Derivation2 T ((∃' p) :: Γ)
| wk {Γ Δ}     : Derivation2 T Γ → Γ ⊆ Δ → Derivation2 T Δ
| cut {Γ p}    : Derivation2 T (p :: Γ) → Derivation2 T (~p :: Γ) → Derivation2 T Γ

scoped infix: 45 " ⊢₂ " => Derivation2

abbrev Derivable2 (T : SyntacticTheory L) (Γ : Sequent L) : Prop := Nonempty (T ⊢₂ Γ)

scoped infix: 45 " ⊢₂! " => Derivable2

abbrev Derivation2SingleConseq (T : SyntacticTheory L) (p : SyntacticFormula L) : Type _ := T ⊢₂ [p]

abbrev Derivable2SingleConseq (T : SyntacticTheory L) (p : SyntacticFormula L) : Prop := Nonempty (T ⊢₂ [p])

scoped infix: 45 " ⊢₂. " => Derivation2SingleConseq

scoped infix: 45 " ⊢₂.! " => Derivable2SingleConseq

def Derivation.toDerivation2 : {Γ : Sequent L} → ⊢¹ Γ → T ⊢₂ Γ
  | _, Derivation.axL Δ r v => Derivation2.axL Δ r v
  | _, Derivation.verum Δ   => Derivation2.verum Δ
  | _, Derivation.and dp dq => Derivation2.and (toDerivation2 dp) (toDerivation2 dq)
  | _, Derivation.or dpq    => Derivation2.or (toDerivation2 dpq)
  | _, Derivation.all dp    => Derivation2.all (toDerivation2 dp)
  | _, Derivation.ex t dp   => Derivation2.ex t (toDerivation2 dp)
  | _, Derivation.wk d h    => Derivation2.wk (toDerivation2 d) h
  | _, Derivation.cut d₁ d₂ => Derivation2.cut (toDerivation2 d₁) (toDerivation2 d₂)

lemma Derivable.toDerivable2 {Γ : Sequent L} (h : ⊢¹! Γ) : T ⊢₂! Γ := ⟨Derivation.toDerivation2 <| Classical.choice h⟩

namespace Derivable2

lemma wk! {Γ Δ : Sequent L} (d : T ⊢₂! Γ) (h : Γ ⊆ Δ) : T ⊢₂! Δ := ⟨d.some.wk h⟩

end Derivable2

namespace Derivation2

lemma toDerivable2 {Γ : Sequent L} (d : T ⊢₂ Γ) : T ⊢₂! Γ := ⟨d⟩

def allClosureFixitr {p : SyntacticFormula L} (dp : T ⊢₂. p) : (m : ℕ) → T ⊢₂. ∀* (Rew.fixitr 0 m).hom p
  | 0     => by simpa
  | m + 1 => by
    simp [Semiformula.allClosure_fixitr]
    apply all; simpa using allClosureFixitr dp m

def close {p : SyntacticFormula L} (dp : T ⊢₂. p) : T ⊢₂. Rew.embs.hom p.close := by
  simpa [Semiformula.embs_close] using allClosureFixitr dp p.upper

def cutList : (Δ : Sequent L) → T ⊢₂ Δ ++ Γ → (∀ q ∈ Δ, T ⊢₂ ~q :: Γ) → T ⊢₂ Γ
  | [],     d, _  => d
  | p :: Δ, d, ds =>
    let d : T ⊢₂ Δ ++ p :: Γ := d.wk (by intro x; simp; tauto)
    let dp : T ⊢₂ p :: Γ := cutList Δ d (fun q hq ↦ (ds q (by simp [hq])).wk (by intro x; simp; tauto))
    dp.cut (ds p (by simp))

lemma cutList! (Δ : Sequent L) (h : T ⊢₂! Δ ++ Γ) (H : ∀ q ∈ Δ, T ⊢₂! ~q :: Γ) : T ⊢₂! Γ :=
  ⟨cutList Δ h.some (fun q hq ↦ (H q hq).some)⟩

end Derivation2

open Derivation2

variable {T : SyntacticTheory L}

def Provable.toDerivation2 {σ} (b : T.close ⊢! σ) : T ⊢₂.! Rew.embs.hom σ := by
  let ⟨Γ, hΓ, d⟩ := Gentzen.provable_iff.mp (provable_iff.mp b)
  let b : T ⊢₂! List.map (~·) Γ ++ [Rew.emb.hom σ] := Derivable.toDerivable2 d
  refine cutList! _ b (fun p hp ↦ by
    have : ∃ x ∈ Γ, ~x = p := by simpa using hp
    rcases this with ⟨p, Hp, rfl⟩
    have : ∃ x ∈ T, Rew.embs.hom (x.close) = p := by
      simpa [SyntacticTheory.close] using hΓ p Hp
    rcases this with ⟨p, hpT, rfl⟩
    simpa using (Derivation2.root [] hpT).close.toDerivable2.wk! (by simp))

def Derivation2.toDisjconseqTr : {Γ : Sequent L} → T ⊢₂ Γ → T.close ⊢'' Γ
  | _, axL Δ r v          => Gentzen.Disjconseq.em (Semiformula.rel r v) (by simp) (by simp)
  | _, root Γ (p := p) hp =>
    have : T.close ⊢'' [∀* (Rew.fixitr 0 p.upper).hom p] :=
      Gentzen.Disjconseq.byAxm _ (by simp [SyntacticTheory.close]; exact ⟨p, hp, by simp [Semiformula.embs_close]⟩)
    have : T.close ⊢'' [p] := by simpa using System.specializeVec (fun x ↦ &x) this
    Gentzen.Disjconseq.wk this (by simp)
  | _, verum Γ            => Gentzen.Disjconseq.verum Γ
  | _, and dp dq          => Gentzen.Disjconseq.and (toDisjconseqTr dp) (toDisjconseqTr dq)
  | _, or dpq             => Gentzen.Disjconseq.or (toDisjconseqTr dpq)
  | _, all dp             => System.generalize (toDisjconseqTr dp)
  | _, ex t dp            => System.witness t (toDisjconseqTr dp)
  | _, wk d h             => Gentzen.Disjconseq.wk (toDisjconseqTr d) h
  | _, cut dp dn          => Gentzen.Disjconseq.cut (toDisjconseqTr dp) (toDisjconseqTr dn)

def provable_iff_derivable2 {σ} : T.close ⊢! σ ↔ T ⊢₂.! Rew.embs.hom σ :=
  ⟨Provable.toDerivation2, fun b ↦ provable_iff.mpr ⟨b.some.toDisjconseqTr⟩⟩
