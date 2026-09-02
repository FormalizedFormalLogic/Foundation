import Foundation.FirstOrder.SetTheory.Function

/-!
# The continuum hypothesis and related statements
-/

namespace LO.FirstOrder.SetTheory.Axioms

def continuumHypothesisFor : Semisentence ℒₛₑₜ 1 := f“X. ¬(∃ Y, !CardLT.dfn X Y ∧ !CardLT.dfn Y (!power.dfn X))”

def continuumHypothesis : Sentence ℒₛₑₜ := f“!continuumHypothesisFor !isω”

abbrev ContinuumHypothesis : SetTheory := {continuumHypothesis}

notation "𝗖𝗛" => ContinuumHypothesis

abbrev AntiContinuumHypothesis : SetTheory := {∼continuumHypothesis}

notation "¬𝗖𝗛" => AntiContinuumHypothesis

def generalContinuumHypothesis : Sentence ℒₛₑₜ := f“∀ X, !continuumHypothesisFor X”

abbrev GeneralContinuumHypothesis : SetTheory := {generalContinuumHypothesis}

notation "𝗚𝗖𝗛" => GeneralContinuumHypothesis

abbrev AntiGeneralContinuumHypothesis : SetTheory := {∼generalContinuumHypothesis}

notation "¬𝗚𝗖𝗛" => AntiGeneralContinuumHypothesis

instance (T : SetTheory) [𝗭 ⪯ T] : T + 𝗖𝗛 ⪯ T + 𝗚𝗖𝗛 := by sorry

end LO.FirstOrder.SetTheory.Axioms
