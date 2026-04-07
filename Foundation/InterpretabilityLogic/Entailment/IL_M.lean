module

public import Foundation.InterpretabilityLogic.Entailment.IL_Rstar
public import Foundation.InterpretabilityLogic.Entailment.IL_R_W

@[expose] public section

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

/-- Entailment for interpretability logic with Montagna's principle -/
protected class IL_M (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomM 𝓢

variable [Entailment.IL_M 𝓢]

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

def C_flat_flat₂ : 𝓢 ⊢! ♭φ 🡒 ♭♭φ := or₁
def Rhd_flat_flat₂ : 𝓢 ⊢! ♭φ ▷ ♭♭φ := rhdOfLC! $ nec C_flat_flat₂

def C_flat_flatsharp : 𝓢 ⊢! ♭φ 🡒 ♭♯φ := by
  show 𝓢 ⊢! φ ⋎ ◇φ 🡒 φ ⋏ □(∼φ) ⋎ ◇(φ ⋏ □(∼φ));
  apply left_A_intro;
  . apply deduct';
    apply A_cases ?_ ?_ $ lem (φ := □(∼φ));
    . apply deduct;
      apply A_intro_left;
      apply K_intro <;>
      . apply FiniteContext.byAxm
        simp;
    . apply C_trans (of INLNM!);
      apply C_trans (of diaAxiomL);
      apply deduct;
      apply A_intro_right;
      apply FiniteContext.byAxm;
      simp;
  . apply deduct';
    apply A_intro_right;
    refine (of diaAxiomL) ⨀ ?_;
    apply FiniteContext.byAxm;
    simp;
def Rhd_flat_flatsharp : 𝓢 ⊢! ♭φ ▷ ♭♯φ := rhdOfLC! $ nec C_flat_flatsharp


def C_sharpflat_sharp : 𝓢 ⊢! ♯♭φ 🡒 ♯φ := by
  show [φ ⋎ ◇φ, □(∼(φ ⋎ ◇φ))] ⊢[𝓢]! φ ⋏ □(∼φ);

  have : [φ ⋎ ◇φ, □(∼(φ ⋎ ◇φ))] ⊢[𝓢]! ∼◇φ := by
    apply K_left (ψ := ∼◇◇φ);
    refine CNAKNN ⨀ ?_;
    refine (of $ contra collect_dia_or) ⨀ ?_;
    exact (of CLNNM!) ⨀ (FiniteContext.nthAxm 1);

  apply K_intro;
  . apply A_cases ?_ ?_ $ FiniteContext.nthAxm 0;
    . apply C_id;
    . exact CNC ⨀ this;
  . refine (of CNMLN!) ⨀ this;
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
end
