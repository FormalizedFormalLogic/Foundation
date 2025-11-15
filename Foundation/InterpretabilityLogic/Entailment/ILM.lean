import Foundation.InterpretabilityLogic.Entailment.ILRStar
import Foundation.InterpretabilityLogic.Entailment.ILRW
import Foundation.InterpretabilityLogic.Entailment.ILMinus_M

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

/-- Entailment for interpretability logic with Montagna's principle -/
protected class ILM (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomM 𝓢

variable [Entailment.ILM 𝓢]

instance «IL(M)_⊢_R» : Entailment.HasAxiomR 𝓢 where
  axiomR! {φ ψ χ} := by
    apply deduct';
    apply rhdTrans! (of $ rhdOfLC! $ nec $ IL.lemma₂);
    apply rhdTrans! (of $ axiomJ5!);
    apply axiomM!;

local prefix:80 "♭" => λ φ => φ ⋎ ◇φ
local prefix:80 "♯" => λ φ => φ ⋏ □(∼φ)

def Rhd_AM : 𝓢 ⊢! φ ▷ ♭φ := rhdOfLC! $ nec or₁
def AM_Rhd : 𝓢 ⊢! ♭φ ▷ φ := axiomJ3! ⨀ axiomJ1'! ⨀ axiomJ5!

def C_flat_flat₂ : 𝓢 ⊢! ♭φ ➝ ♭♭φ := or₁
def Rhd_flat_flat₂ : 𝓢 ⊢! ♭φ ▷ ♭♭φ := rhdOfLC! $ nec C_flat_flat₂

def C_flat_flatsharp : 𝓢 ⊢! ♭φ ➝ ♭♯φ := by
  simp;
  have : 𝓢 ⊢! ◇♭φ ➝ ◇φ := CMM_of_Rhd! AM_Rhd;
  sorry;

def Rhd_flat_flatsharp : 𝓢 ⊢! ♭φ ▷ ♭♯φ := rhdOfLC! $ nec C_flat_flatsharp

def C_sharpflat_sharp : 𝓢 ⊢! ♯♭φ ➝ ♯φ := by
  simp;
  have : [φ ⋎ ◇φ, □(∼(φ ⋎ ◇φ))] ⊢[𝓢]! □(∼(φ ⋎ ◇φ)) := FiniteContext.nthAxm 1;
  suffices [φ ⋎ ◇φ, □(∼(φ ⋎ ◇φ))] ⊢[𝓢]! φ ⋏ □(∼φ) by tauto;
  apply K_intro;
  . apply A_cases ?_ ?_ $ FiniteContext.nthAxm 0;
    . apply C_id;
    . apply deduct;
      sorry;
  . sorry;
def Rhd_sharpflat_sharp : 𝓢 ⊢! ♯♭φ ▷ ♯φ := rhdOfLC! $ nec C_sharpflat_sharp


def K6 : 𝓢 ⊢! φ ▷ ♯φ := by
  apply rhdTrans! $ show 𝓢 ⊢! φ ▷ ♭φ by exact Rhd_AM;
  apply rhdTrans! $ show 𝓢 ⊢! ♭φ ▷ ♭♭φ by exact Rhd_flat_flat₂;
  apply rhdTrans! $ show 𝓢 ⊢! ♭♭φ ▷ ♭♯♭φ by exact Rhd_flat_flatsharp;
  apply rhdTrans! $ show 𝓢 ⊢! ♭♯♭φ ▷ ♯♭φ by exact AM_Rhd;
  apply rhdTrans! $ show 𝓢 ⊢! ♯♭φ ▷ ♯φ by exact Rhd_sharpflat_sharp;
  apply axiomJ1'!;

instance «IL(M)_⊢_W» : Entailment.HasAxiomW 𝓢 where
  axiomW! {_ _} := deduct' $ rhdTrans! (of K6) axiomM!

end LO.InterpretabilityLogic.Entailment
