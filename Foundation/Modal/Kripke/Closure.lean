import Foundation.Modal.Kripke.Basic

namespace LO.Modal.Kripke

namespace Frame

open Relation

variable {F : Frame} {x y : F.World}


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

abbrev TransitiveReflexiveClosure (F : Frame) : Frame := ⟨F.World, (· ≺^* ·)⟩
postfix:95 "^*" => Frame.TransitiveReflexiveClosure

end trans_refl


section trans

abbrev RelTransGen {F : Frame} : _root_.Rel F.World F.World := TransGen (· ≺ ·)
infix:45 " ≺^+ " => Frame.RelTransGen

namespace RelTransGen

protected lemma single (hxy : x ≺ y) : x ≺^+ y := TransGen.single hxy

@[simp]
protected lemma transitive : Transitive F.RelTransGen := λ _ _ _ => TransGen.trans

protected lemma symmetric (hSymm : Symmetric F.Rel) : Symmetric F.RelTransGen := by
  intro x y rxy;
  induction rxy with
  | single h => exact TransGen.single $ hSymm h;
  | tail _ hyz ih => exact TransGen.trans (TransGen.single $ hSymm hyz) ih

lemma exists_itr : x ≺^+ y ↔ ∃ n > 0, F.Rel.iterate n x y := TransGen.exists_iterate

end RelTransGen

abbrev TransitiveClosure (F : Frame) : Frame := ⟨F.World, (· ≺^+ ·)⟩
postfix:95 "^+" => Frame.TransitiveClosure

end trans


section refl

abbrev RelReflGen : _root_.Rel F.World F.World := ReflGen (· ≺ ·)
infix:45 " ≺^= " => Frame.RelReflGen

def ReflexiveClosure (F : Frame) : Frame := ⟨F.World, (· ≺^= ·)⟩
postfix:95 "^=" => Frame.ReflexiveClosure

end refl


section irrefl

abbrev RelIrreflGen : _root_.Rel F.World F.World := IrreflGen (· ≺ ·)
scoped infix:45 " ≺^≠ " => Frame.RelIrreflGen

def IrreflexiveClosure (F : Frame) : Frame := ⟨F.World, (· ≺^≠ ·)⟩
postfix:95 "^≠" => Frame.IrreflexiveClosure

namespace IrreflexiveClosure

@[simp]
lemma rel_irreflexive : Irreflexive (F^≠.Rel) := by
  simp [Irreflexive, Frame.RelIrreflGen, IrreflGen, Frame.IrreflexiveClosure]

end IrreflexiveClosure

end irrefl


end Frame


section

instance {F : FiniteFrame} : Finite (F.toFrame^=).World := by simp [Frame.ReflexiveClosure];

abbrev FiniteFrame.ReflexiveClosure (F : FiniteFrame) : FiniteFrame := ⟨F.toFrame^=⟩
postfix:95 "^=" => FiniteFrame.ReflexiveClosure

instance {F : FiniteFrame} : Finite (F.toFrame^≠).World := by simp [Frame.IrreflexiveClosure]

abbrev FiniteFrame.IrreflexiveClosure (F : FiniteFrame) : FiniteFrame := ⟨F.toFrame^≠⟩
postfix:95 "^≠" => FiniteFrame.IrreflexiveClosure

end

end LO.Modal.Kripke
