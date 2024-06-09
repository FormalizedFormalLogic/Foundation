import Logic.FirstOrder.Incompleteness.SelfReference
import Logic.Modal.Standard.Deduction

namespace LO

/-
  TODO: 一応，様相論理関連の話題ではあるが，Gödel数のnotationなどがこの名前空間でlocalに定義されているためこの名前空間に置かれている．移したい．
-/
namespace FirstOrder.Arith.SelfReference

open System
open Formula

variable {α : Type*} {a : α} [DecidableEq α]
variable {p q r : LO.Modal.Standard.Formula α}
variable {φ ψ ξ : Sentence ℒₒᵣ}

open LO.Modal.Standard.Formula (atom)

def Realization (α : Type u) := α → Sentence ℒₒᵣ

def Interpretation
  (f : Realization α)
  (pred : Semisentence ℒₒᵣ 1)
  : LO.Modal.Standard.Formula α → Sentence ℒₒᵣ
  | .atom a => f a
  | .box p => pred/[⸢(Interpretation f pred p)⸣]
  | ⊤ => ⊤
  | ⊥ => ⊥
  | p ⟶ q => Interpretation f pred p ⟶ Interpretation f pred q
  | p ⋏ q => Interpretation f pred p ⋏ Interpretation f pred q
  | p ⋎ q => Interpretation f pred p ⋎ Interpretation f pred q
notation f "[" Pr "] " p => Interpretation f Pr p

open LO.FirstOrder.Arith.FirstIncompletenessBySelfReference (provableSentence)

notation "Pr(" T ")" => provableSentence T

noncomputable abbrev TheoryFixedInterpretation (f : Realization α) (T : Theory ℒₒᵣ) := (f[Pr(T)] ·)
notation f "[" T "] " p => TheoryFixedInterpretation f T p

variable {T : Theory ℒₒᵣ}

open System

private noncomputable abbrev AsBox (T : Theory ℒₒᵣ) (σ : Sentence ℒₒᵣ) : Sentence ℒₒᵣ := Pr(T)/[⸢σ⸣]
notation:max "⟦" T "⟧" σ:90 => AsBox T σ

namespace DerivabilityCondition

variable (T U : Theory ℒₒᵣ)

class HBL1 where
  D1 : ∀ {σ : Sentence ℒₒᵣ}, U ⊢! σ → T ⊢! ⟦U⟧σ -- Necessitation

class HBL2 where
  D2 : ∀ {σ π : Sentence ℒₒᵣ}, T ⊢! ⟦U⟧(σ ⟶ π) ⟶ ⟦U⟧σ ⟶ ⟦U⟧π -- Axiom K

class HBL3 where
  D3 : ∀ {σ : Sentence ℒₒᵣ}, T ⊢! ⟦U⟧σ ⟶ ⟦U⟧⟦U⟧σ -- Axiom Four

class Standard extends HBL1 T U, HBL2 T U, HBL3 T U

class FormalizedDT where
  FDT : ∀ {σ π : Sentence ℒₒᵣ}, T ⊢! ⟦U⟧(σ ⟶ π) ⟷ ⟦U.insert σ⟧(π)

class Loeb where
  LT : ∀ {σ : Sentence ℒₒᵣ}, T ⊢! ⟦U⟧σ ⟶ σ → T ⊢! σ

class FormalizedLoeb where
  FLT : ∀ {σ : Sentence ℒₒᵣ}, T ⊢! ⟦U⟧(⟦U⟧σ ⟶ σ) ⟶ ⟦U⟧σ

end DerivabilityCondition


open DerivabilityCondition

variable [Standard T T]
variable [Loeb T T]

open LO.Modal.Standard (reducible_GL_K4Loeb Deduction.inducition_with_nec! Deduction.inducition!)

lemma arithmetical_soundness_K4Loeb (h : 𝐊𝟒(𝐋) ⊢! p) : ∀ f, T ⊢! f[T] p := by
  intro f;
  induction h using Deduction.inducition! with
  | hMaxm hp =>
    rcases hp with (hK | hFour)
    . obtain ⟨p, q, e⟩ := hK; subst_vars; apply HBL2.D2;
    . obtain ⟨p, e⟩ := hFour; subst_vars; apply HBL3.D3;
  | hNec _ ih => exact HBL1.D1 ih;
  | hLoeb _ ih => exact Loeb.LT ih;
  | hHenkin => simp_all only [Bool.false_eq_true];
  | hMdp ihpq ihp =>
    simp at ihpq;
    exact ihpq ⨀ ihp;
  | hDne =>
    dsimp [NegDefinition.neg, TheoryFixedInterpretation, Interpretation]; -- TODO: 単なる二重否定除去であるので直ちに成り立ってほしいが上手く出来ない．
    sorry;
  | _ =>
    dsimp;
    first
    | apply System.verum!;
    | apply System.imply₁!;
    | apply System.imply₂!;
    | apply System.conj₁!;
    | apply System.conj₂!;
    | apply System.conj₃!;
    | apply System.disj₁!;
    | apply System.disj₂!;
    | apply System.disj₃!;

theorem arithmetical_soundness (h : 𝐆𝐋 ⊢! p) : ∀ f, T ⊢! f[T] p := by
  apply arithmetical_soundness_K4Loeb;
  exact (System.reducible_iff.mp reducible_GL_K4Loeb) h;

open System

end FirstOrder.Arith.SelfReference

namespace System

end System

end LO
