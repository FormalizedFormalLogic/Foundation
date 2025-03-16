import Foundation.Modal.Kripke.Basic

namespace LO.Modal.Kripke

namespace Frame

open Relation

variable {F : Frame} {x y z : F.World}


section trans_refl

abbrev RelReflTransGen : _root_.Rel F.World F.World := ReflTransGen (· ≺ ·)
infix:45 " ≺^* " => Frame.RelReflTransGen

namespace RelReflTransGen

lemma single (hxy : x ≺ y) : x ≺^* y := ReflTransGen.single hxy

@[simp]
protected lemma reflexive : Reflexive F.RelReflTransGen := Relation.reflexive_reflTransGen

@[simp]
lemma refl {x : F.World} : x ≺^* x := RelReflTransGen.reflexive x

@[simp]
protected lemma transitive : Transitive F.RelReflTransGen := Relation.transitive_reflTransGen

protected lemma symmetric : Symmetric F.Rel → Symmetric F.RelReflTransGen := ReflTransGen.symmetric

protected lemma exists_itr : x ≺^* y ↔ ∃ n, F.Rel.iterate n x y := ReflTransGen.exists_iterate

end RelReflTransGen

abbrev mkTransReflClosure (F : Frame) : Frame := ⟨F.World, (· ≺^* ·)⟩
postfix:95 "^*" => mkTransReflClosure

namespace mkTransReflClosure

instance [Finite F] : Finite (F^*) := inferInstance
instance [F.IsFinite] : (F^*).IsFinite := inferInstance

end mkTransReflClosure

end trans_refl


section trans

abbrev RelTransGen {F : Frame} : _root_.Rel F.World F.World := TransGen (· ≺ ·)
infix:45 " ≺^+ " => Frame.RelTransGen

namespace RelTransGen

protected lemma single (hxy : x ≺ y) : x ≺^+ y := TransGen.single hxy

protected instance instIsTrans : IsTrans _ F.RelTransGen := ⟨λ _ _ _ => TransGen.trans⟩

protected instance instIsSymm [IsSymm _ F.Rel] : IsSymm _ F.RelTransGen := ⟨by
  intro x y rxy;
  induction rxy with
  | single h => exact TransGen.single $ (IsSymm.symm _ _) h;
  | tail _ hyz ih => exact TransGen.trans (TransGen.single $ (IsSymm.symm _ _) hyz) ih
⟩

lemma exists_itr : x ≺^+ y ↔ ∃ n > 0, F.Rel.iterate n x y := TransGen.exists_iterate

lemma head (Rxy : x ≺ y) (Ryz : y ≺^+ z) : x ≺^+ z := TransGen.head Rxy Ryz
lemma tail (Rxy : x ≺^+ y) (Ryz : y ≺ z) : x ≺^+ z := TransGen.tail Rxy Ryz

end RelTransGen

abbrev mkTransClosure (F : Frame) : Frame := ⟨F.World, (· ≺^+ ·)⟩
postfix:95 "^+" => mkTransClosure

namespace mkTransClosure

instance [Finite F] : Finite (F^+) := inferInstance
instance [F.IsFinite] : (F^+).IsFinite := inferInstance

end mkTransClosure

end trans


section refl

abbrev RelReflGen : _root_.Rel F.World F.World := ReflGen (· ≺ ·)
infix:45 " ≺^= " => Frame.RelReflGen

abbrev mkReflClosure (F : Frame) : Frame := ⟨F.World, (· ≺^= ·)⟩
postfix:95 "^=" => mkReflClosure

namespace mkReflClosure

instance [Finite F] : Finite (F^=) := inferInstance
instance [F.IsFinite] : (F^=).IsFinite := inferInstance

end mkReflClosure

end refl


section irrefl

abbrev RelIrreflGen : _root_.Rel F.World F.World := IrreflGen (· ≺ ·)
scoped infix:45 " ≺^≠ " => Frame.RelIrreflGen

abbrev mkIrreflClosure (F : Frame) : Frame := ⟨F.World, (· ≺^≠ ·)⟩
postfix:95 "^≠" => mkIrreflClosure

namespace mkIrreflClosure

instance [Finite F] : Finite (F^≠) := inferInstance
instance [F.IsFinite] : (F^≠).IsFinite := inferInstance

@[simp]
lemma rel_irreflexive : Irreflexive (F^≠.Rel) := by simp [Irreflexive, Frame.RelIrreflGen, IrreflGen, mkIrreflClosure]

end mkIrreflClosure

end irrefl

end Frame


end LO.Modal.Kripke
