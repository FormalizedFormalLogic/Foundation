import Foundation.FirstOrder.ZF.Basic

/-!
# ZFC set theory

reference: Ralf Schindler, "Set Theory, Exploring Independence and Truth"
-/

namespace LO

open FirstOrder SetTheory

def ZermeloFraenkelChoice : Theory ℒₛₑₜ := 𝗭𝗙 + {Axiom.choice}

notation "𝗭𝗙𝗖" => ZermeloFraenkelChoice

namespace ZermeloFraenkelChoice

instance : 𝗭𝗙 ⪯ 𝗭𝗙𝗖 := inferInstanceAs (𝗭𝗙 ⪯ 𝗭𝗙 + ({Axiom.choice} : Theory ℒₛₑₜ))

instance : 𝗘𝗤 ⪯ 𝗭𝗙𝗖 := Entailment.WeakerThan.trans (inferInstanceAs (𝗘𝗤 ⪯ 𝗭𝗙)) inferInstance

end ZermeloFraenkelChoice

end LO
