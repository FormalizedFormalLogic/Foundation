import Logic.FirstOrder.Incompleteness.ProvabilityCondition
import Logic.Modal.Standard.Deduction

namespace LO.Modal.Standard.Provability

open LO.FirstOrder

variable {α : Type*} [DecidableEq α]

/-- Mapping modal prop vars to first-order sentence -/
def realization (L) (α : Type u) := α → FirstOrder.Sentence L

/-- Mapping modal formulae to first-order sentence -/
def interpretation
  [Semiterm.Operator.GoedelNumber L (FirstOrder.Sentence L)]
  (f : realization L α) (β : ProvabilityPredicate L L) : Formula α → FirstOrder.Sentence L
  | .atom a => f a
  | .box p => ⦍β⦎(interpretation f β p)
  | ⊤ => ⊤
  | ⊥ => ⊥
  | p ⟶ q => (interpretation f β p) ⟶ (interpretation f β q)
  | p ⋏ q => (interpretation f β p) ⋏ (interpretation f β q)
  | p ⋎ q => (interpretation f β p) ⋎ (interpretation f β q)
scoped notation f "[" β "] " p => interpretation f β p -- TODO: more good notation

/-
  TODO:
  `ArithmeticalSoundness`と`ArithmeticalCompleteness`を単純にinstance化する際には大抵`T₀`に依存してしまうため型推論が壊れてしまう．
  もう少し良いやり方がありそうな気もするので一旦コメントアウト
section

variable {L : FirstOrder.Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
variable (α) (β : ProvabilityPredicate L L)

class ArithmeticalSoundness (𝓓 : DeductionParameter α) (T : FirstOrder.Theory L) where
  sound : ∀ {p}, (𝓓 ⊢! p) → (∀ f, T ⊢! f[β] p)

class ArithmeticalCompleteness (𝓓 : DeductionParameter α) (T : FirstOrder.Theory L) where
  complete : ∀ {p}, (∀ f, T ⊢! f[β] p) → (𝓓 ⊢! p)

class ProvabilityLogic (𝓓 : DeductionParameter α) (T : FirstOrder.Theory L)where
  is : System.theory 𝓓 = { p | ∀ f, T ⊢! f[β] p }

variable {α β} {𝓓 : DeductionParameter α} {T : FirstOrder.Theory L}

instance [ArithmeticalSoundness α β 𝓓 T] [ArithmeticalCompleteness α β 𝓓 T] : ProvabilityLogic α β 𝓓 T where
  is := by
    apply Set.eq_of_subset_of_subset;
    . intro p hp;
      simp only [Set.mem_setOf_eq];
      exact ArithmeticalSoundness.sound hp;
    . intro p hp;
      simp at hp;
      exact ArithmeticalCompleteness.complete hp;

end
-/

section ArithmeticalSoundness

open System
open ProvabilityPredicate

variable {L : FirstOrder.Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
         [DecidableEq (Sentence L)]
         (T₀ T : FirstOrder.Theory L) [T₀ ≼ T] [Diagonalization T₀]
         (β : ProvabilityPredicate L L) [β.HilbertBernays T₀ T]

open LO.FirstOrder.ProvabilityPredicate

lemma arithmetical_soundness_K4Loeb (h : 𝐊𝟒(𝐋) ⊢! p) : ∀ {f : realization L α}, T ⊢! (f[β] p) := by
  intro f;
  induction h using Deduction.inducition! with
  | hNec _ ih => exact HilbertBernays₁.D1s (T₀ := T₀) ih;
  | hMaxm hp =>
    rcases hp with (hK | hFour)
    . obtain ⟨p, q, e⟩ := hK; subst_vars; apply HilbertBernays₂.D2s (T₀ := T₀);
    . obtain ⟨p, e⟩ := hFour; subst_vars; apply HilbertBernays₃.D3s (T₀ := T₀);
  | hLoeb _ ih => exact Loeb.LT T₀ ih;
  | hHenkin => simp_all only [Bool.false_eq_true];
  | hMdp ihpq ihp =>
    simp [interpretation] at ihpq;
    exact ihpq ⨀ ihp;
  | hDne =>
    dsimp [interpretation];
    exact imp_trans! (conj₁'! $ iffComm'! NegationEquiv.negneg_equiv!) dne!;
  | _ => dsimp [interpretation]; trivial;

theorem arithmetical_soundness_GL (h : 𝐆𝐋 ⊢! p) : ∀ {f : realization L α}, T ⊢! (f[β] p) := by
  apply arithmetical_soundness_K4Loeb (T₀ := T₀);
  exact (System.reducible_iff.mp reducible_GL_K4Loeb) h;

end ArithmeticalSoundness

end Modal.Standard.Provability

end LO
