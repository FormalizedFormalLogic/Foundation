import Logic.FirstOrder.Incompleteness.DerivabilityCondition
import Logic.Modal.Deduction

namespace LO.Modal.Provability

open LO.FirstOrder LO.FirstOrder.DerivabilityCondition

variable {α : Type*} [DecidableEq α]

/-- Mapping modal prop vars to first-order sentence -/
def realization (L) (α : Type u) := α → FirstOrder.Sentence L

/-- Mapping modal formulae to first-order sentence -/
def interpretation
  [Semiterm.Operator.GoedelNumber L (FirstOrder.Sentence L)]
  (f : realization L α) (β : ProvabilityPredicate L L) : Formula α → FirstOrder.Sentence L
  | .atom a => f a
  | □p => ⦍β⦎(interpretation f β p)
  | ⊥ => ⊥
  | p ⟶ q => (interpretation f β p) ⟶ (interpretation f β q)
scoped notation f "[" β "] " p => interpretation f β p -- TODO: more good notation

namespace interpretation

variable [Semiterm.Operator.GoedelNumber L (FirstOrder.Sentence L)]
         {f : realization L α} {β : ProvabilityPredicate L L} {p q : Formula α}
         [NegAbbrev (FirstOrder.Sentence L)]

lemma imp_def : (f[β] (p ⟶ q)) = ((f[β] p) ⟶ (f[β] q)) := by rfl
lemma box_def : (f[β] □p) = ⦍β⦎(f[β] p) := by rfl
lemma neg_def : (f[β] ~p) = (f[β] p) ⟶ ⊥ := by rfl

end interpretation

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
         (β : ProvabilityPredicate L L)

lemma arithmetical_soundness_K4Loeb [β.HBL T₀ T] (h : 𝐊𝟒(𝐋) ⊢! p) : ∀ {f : realization L α}, T ⊢!. (f[β] p) := by
  intro f;
  induction h using Deduction.inducition! with
  | hRules rl hrl hant ih =>
    rcases hrl with (⟨_, rfl⟩ | ⟨_, rfl⟩)
    . simp_all only [List.mem_singleton, forall_eq]; exact D1s (T₀ := T₀) ih;
    . simp_all only [List.mem_singleton, forall_eq]; exact Loeb.LT T₀ ih;
  | hMaxm hp =>
    rcases hp with (⟨_, _, rfl⟩ | ⟨_, rfl⟩)
    . exact D2s (T₀ := T₀);
    . exact D3s (T₀ := T₀);
  | hMdp ihpq ihp =>
    simp [interpretation] at ihpq;
    exact ihpq ⨀ ihp;
  | _ => dsimp [interpretation]; trivial;

theorem arithmetical_soundness_GL [β.HBL T₀ T] (h : 𝐆𝐋 ⊢! p) : ∀ {f : realization L α}, T ⊢!. (f[β] p) := by
  apply arithmetical_soundness_K4Loeb (T₀ := T₀);
  exact (System.weakerThan_iff.mp reducible_GL_K4Loeb) h;


lemma arithmetical_soundness_N [β.HBL T₀ T] (h : 𝐍 ⊢! p) : ∀ {f : realization L α}, T ⊢!. (f[β] p) := by
  intro f;
  induction h using Deduction.inducition! with
  | hMaxm hp => simp at hp;
  | hRules rl hrl hant ih =>
    simp only [Set.mem_setOf_eq] at hrl;
    obtain ⟨p, rfl⟩ := hrl;
    simp_all only [List.mem_singleton, forall_eq];
    exact D1s (T₀ := T₀) ih;
  | hMdp ihpq ihp =>
    simp only [interpretation] at ihpq;
    exact ihpq ⨀ ihp;
  | _ => dsimp [interpretation]; trivial;

end ArithmeticalSoundness

end Modal.Provability

end LO
