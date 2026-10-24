module

public import Foundation.FirstOrder.SetTheory.Basic.Misc
public import Foundation.FirstOrder.SetTheory.BST.Basic
public import Foundation.FirstOrder.SetTheory.Schemata

@[expose] public section
/-!
# Basic axioms of ZC set theory
-/

namespace FFL.FirstOrder.SetTheory

namespace Axiom

/-- Axiom of choice. -/
def choice : SetTheorySentence :=
  “∀ 𝓧, (∀ X ∈ 𝓧, !isNonempty X) ∧ (∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ z, z ∈ X ∧ z ∈ Y) → X = Y) →
    ∃ C, ∀ X ∈ 𝓧, ∃! x, x ∈ C ∧ x ∈ X”

end Axiom

/-! ### Zermelo set theory -/

/-- Zermelo set theory. -/
abbrev Zermelo : SetTheory := 𝗕𝗦𝗧 ∪ 𝗦𝗘𝗣

notation "𝗭" => Zermelo

instance : 𝗘𝗤 _ ⪯ 𝗭 :=
  let : 𝗘𝗤 _ ⪯ 𝗕𝗦𝗧 := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance : 𝗕𝗦𝗧 ⪯ 𝗭 := inferInstance

instance : 𝗦𝗘𝗣 ⪯ 𝗭 := inferInstance

/-! ### Zermelo set theory with axiom of choice -/

/-- The theory containing only the axiom of choice. -/
def AxiomOfChoice : SetTheory := {Axiom.choice}

notation "𝗔𝗖" => AxiomOfChoice

/-- Zermelo set theory with axiom of choice. -/
abbrev ZermeloChoice : SetTheory := 𝗭 ∪ 𝗔𝗖

notation "𝗭𝗖" => ZermeloChoice

instance : 𝗭 ⪯ 𝗭𝗖 := inferInstance

instance : 𝗘𝗤 _ ⪯ 𝗭𝗖 :=
  let : 𝗘𝗤 _ ⪯ 𝗭 := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance : 𝗕𝗦𝗧 ⪯ 𝗭𝗖 :=
  let : 𝗕𝗦𝗧 ⪯ 𝗭 := inferInstance
  Entailment.WeakerThan.trans this inferInstance

end FFL.FirstOrder.SetTheory
