module

public import Foundation.FirstOrder.SetTheory.Basic.Misc
public import Foundation.FirstOrder.SetTheory.Z.Basic

@[expose] public section
/-!
# Basic axioms of ZFC set theory

reference: Ralf Schindler, "Set Theory, Exploring Independence and Truth" [Sch14]
-/

namespace FFL.FirstOrder.SetTheory

/-! ### Zermelo-Fraenkel set theory -/

/-- Zermelo-Fraenkel set theory. -/
abbrev ZermeloFraenkel : SetTheory := 𝗭 ∪ 𝗥𝗘𝗣𝗟

notation "𝗭𝗙" => ZermeloFraenkel

instance : 𝗘𝗤 _ ⪯ 𝗭𝗙 :=
  let : 𝗘𝗤 _ ⪯ 𝗭 := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance : 𝗕𝗦𝗧 ⪯ 𝗭𝗙 :=
  let : 𝗕𝗦𝗧 ⪯ 𝗭 := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance : 𝗦𝗘𝗣 ⪯ 𝗭𝗙 :=
  let : 𝗦𝗘𝗣 ⪯ 𝗭 := inferInstance
  Entailment.WeakerThan.trans this inferInstance

lemma z_subset_zf : 𝗭 ⊆ 𝗭𝗙 := Set.subset_union_left

instance : 𝗭 ⪯ 𝗭𝗙 := Entailment.WeakerThan.ofSubset z_subset_zf

lemma repl_subset_zf : 𝗥𝗘𝗣𝗟 ⊆ 𝗭𝗙 := Set.subset_union_right

instance : 𝗥𝗘𝗣𝗟 ⪯ 𝗭𝗙 := Entailment.WeakerThan.ofSubset repl_subset_zf

/-! ### Zermelo-Fraenkel set theory with axiom of choice -/

/-- Zermelo-Fraenkel set theory with axiom of choice. -/
abbrev ZermeloFraenkelChoice : SetTheory := 𝗭𝗙 ∪ 𝗔𝗖

notation "𝗭𝗙𝗖" => ZermeloFraenkelChoice

instance : 𝗭𝗙 ⪯ 𝗭𝗙𝗖 := inferInstance

instance : 𝗘𝗤 _ ⪯ 𝗭𝗙𝗖 :=
  let : 𝗘𝗤 _ ⪯ 𝗭𝗙 := inferInstance
  Entailment.WeakerThan.trans this inferInstance

lemma zc_subset_zfc : 𝗭𝗖 ⊆ 𝗭𝗙𝗖 := Set.union_subset_union_left _ z_subset_zf

instance : 𝗭𝗖 ⪯ 𝗭𝗙𝗖 := Entailment.WeakerThan.ofSubset zc_subset_zfc

instance : 𝗭 ⪯ 𝗭𝗙𝗖 := Entailment.WeakerThan.trans (inferInstance : 𝗭 ⪯ 𝗭𝗙) inferInstance

end FFL.FirstOrder.SetTheory
