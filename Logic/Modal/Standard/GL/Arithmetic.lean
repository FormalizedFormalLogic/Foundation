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

private noncomputable abbrev AsBox (T : Theory ℒₒᵣ) (φ : Sentence ℒₒᵣ) : Sentence ℒₒᵣ := Pr(T)/[⸢φ⸣]
notation:max "⟦" T "⟧" φ:90 => AsBox T φ

namespace DerivabilityCondition

variable (T U : Theory ℒₒᵣ)

class HBL1 where
  D1 : ∀ {φ : Sentence ℒₒᵣ}, U ⊢! φ → T ⊢! ⟦U⟧φ -- Necessitation

class HBL2 where
  D2 : ∀ {φ ψ : Sentence ℒₒᵣ}, T ⊢! ⟦U⟧(φ ⟶ ψ) ⟶ ⟦U⟧φ ⟶ ⟦U⟧ψ -- Axiom K

class HBL3 where
  D3 : ∀ {φ : Sentence ℒₒᵣ}, T ⊢! ⟦U⟧φ ⟶ ⟦U⟧⟦U⟧φ -- Axiom Four

class Standard extends HBL1 T U, HBL2 T U, HBL3 T U

class FormalizedDT where
  FDT : ∀ {φ ψ : Sentence ℒₒᵣ}, T ⊢! ⟦U⟧(φ ⟶ ψ) ⟷ ⟦U.insert φ⟧(ψ)

class Loeb where
  LT : ∀ {φ : Sentence ℒₒᵣ}, T ⊢! ⟦T⟧φ ⟶ φ → T ⊢! φ

class FormalizedLoeb where
  FLT : ∀ {φ : Sentence ℒₒᵣ}, T ⊢! ⟦U⟧(⟦U⟧φ ⟶ φ) ⟶ ⟦U⟧φ

end DerivabilityCondition


open DerivabilityCondition

section

variable (T : Theory ℒₒᵣ) [𝐄𝐐 ≼ T] [𝐏𝐀⁻ ≼ T] [SigmaOneSound T]
variable [Standard T T]

lemma loeb_theorem
  {φ : Sentence ℒₒᵣ} (h : T ⊢! Pr(T)/[⸢φ⸣] ⟶ φ) : T ⊢! φ := by
  have := SelfReference.main T $ pred (T ⊢! · ⟶ φ);
  generalize e : fixpoint (pred (T ⊢! · ⟶ φ)) = K at this;
  sorry;

instance : Loeb T := ⟨loeb_theorem T⟩

noncomputable abbrev consistency_of (T : Theory ℒₒᵣ) := ~⟦T⟧⊥
notation "Con(" T ")" => consistency_of T

lemma goedel2_of_loeb [Loeb T] : System.Consistent T → T ⊬! Con(T) := by
  contrapose;
  intro hC; simp [consistency_of] at hC;
  have : T ⊢! ⟦T⟧⊥ ⟶ ⊥ := by sorry; -- TODO: `T ⊢! ~⟦T⟧⊥`より明らかなはず
  have : T ⊢! ⊥ := Loeb.LT this;
  apply System.not_consistent_iff_inconsistent.mpr;
  apply System.inconsistent_of_provable this;

end


variable [Standard T T]
variable [Loeb T]

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

theorem arithmetical_soundness_GL (h : 𝐆𝐋 ⊢! p) : ∀ f, T ⊢! f[T] p := by
  apply arithmetical_soundness_K4Loeb;
  exact (System.reducible_iff.mp reducible_GL_K4Loeb) h;

class ArithmeticalSoundness (T : Theory ℒₒᵣ) (𝓓 : Modal.Standard.DeductionParameter α) where
  sounds : ∀ {p}, 𝓓 ⊢! p → ∀ f, T ⊢! f[T] p

class ArithmeticalCompleteness (T : Theory ℒₒᵣ) (𝓓 : Modal.Standard.DeductionParameter α) where
  completes : ∀ {p}, (∀ f, T ⊢! f[T] p) → 𝓓 ⊢! p

instance : ArithmeticalSoundness (α := α) T 𝐆𝐋 := ⟨arithmetical_soundness_GL⟩


class IsProvabilityLogicOf (T : Theory ℒₒᵣ) (𝓓 : Modal.Standard.DeductionParameter α) where
  is : System.theory 𝓓 = { p | ∀ f, T ⊢! f[T] p }

instance [ArithmeticalSoundness T 𝓓] [ArithmeticalCompleteness T 𝓓] : IsProvabilityLogicOf T 𝓓 where
  is := by
    apply Set.eq_of_subset_of_subset;
    . intro p hp;
      simp only [Set.mem_setOf_eq];
      exact ArithmeticalSoundness.sounds hp;
    . intro p hp;
      simp at hp;
      exact ArithmeticalCompleteness.completes hp;

end FirstOrder.Arith.SelfReference

end LO
