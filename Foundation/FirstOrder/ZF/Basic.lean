import Foundation.FirstOrder.Z.Basic

/-!
# Zermelo–Fraenkel set theory

reference: Ralf Schindler, "Set Theory, Exploring Independence and Truth"
-/

namespace LO

open FirstOrder SetTheory

inductive ZermeloFraenkel : Theory ℒₛₑₜ
  | equal : ∀ φ ∈ 𝗘𝗤, ZermeloFraenkel φ
  | empty : ZermeloFraenkel Axiom.empty
  | extentionality : ZermeloFraenkel Axiom.extentionality
  | pairing : ZermeloFraenkel Axiom.pairing
  | union : ZermeloFraenkel Axiom.union
  | power : ZermeloFraenkel Axiom.power
  | infinity : ZermeloFraenkel Axiom.infinity
  | foundation : ZermeloFraenkel Axiom.foundation
  | separation (φ : SyntacticSemiformula ℒₛₑₜ 1) : ZermeloFraenkel (Axiom.separationSchema φ)
  | replacement (φ : SyntacticSemiformula ℒₛₑₜ 2) : ZermeloFraenkel (Axiom.replacementSchema φ)

notation "𝗭𝗙" => ZermeloFraenkel

namespace ZermeloFraenkel

instance : 𝗘𝗤 ⪯ 𝗭𝗙 := Entailment.WeakerThan.ofSubset ZermeloFraenkel.equal

end ZermeloFraenkel

end LO
