import Logic.Logic.Kripke.Basic

namespace LO.Kripke

open Relation

abbrev Frame.RelReflTransGen {F : Frame} : _root_.Rel F.World F.World:= ReflTransGen (· ≺ ·)
infix:45 " ≺^* " => Frame.RelReflTransGen

namespace Frame.RelReflTransGen

variable {F : Frame}

@[simp] lemma single {x y : F.World} (hxy : x ≺ y) : x ≺^* y := ReflTransGen.single hxy

@[simp] lemma reflexive : Reflexive F.RelReflTransGen := Relation.reflexive_reflTransGen

@[simp] lemma refl {x : F.World} : x ≺^* x := reflexive x

@[simp] lemma transitive : Transitive F.RelReflTransGen := Relation.transitive_reflTransGen

@[simp] lemma symmetric : Symmetric F.Rel → Symmetric F.RelReflTransGen := ReflTransGen.symmetric

end Frame.RelReflTransGen


abbrev Frame.TransitiveReflexiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^* ·)
postfix:95 "^*" => Frame.TransitiveReflexiveClosure

namespace Frame.TransitiveReflexiveClosure

variable {F : Frame}

lemma single {x y : F.World} (hxy : x ≺ y) : F^*.Rel x y := ReflTransGen.single hxy

lemma rel_reflexive : Reflexive (F^*.Rel) := by intro x; exact ReflTransGen.refl;

lemma rel_transitive : Transitive (F^*.Rel) := by simp;

lemma rel_symmetric : Symmetric F.Rel → Symmetric (F^*) := ReflTransGen.symmetric

end Frame.TransitiveReflexiveClosure



abbrev Frame.RelTransGen {F : Frame} : _root_.Rel F.World F.World := TransGen (· ≺ ·)
infix:45 " ≺^+ " => Frame.RelTransGen

namespace Frame.RelTransGen

variable {F : Frame}

@[simp] lemma single {x y : F.World} (hxy : x ≺ y) : x ≺^+ y := TransGen.single hxy

@[simp]
lemma transitive : Transitive F.RelTransGen := λ _ _ _ => TransGen.trans

@[simp]
lemma symmetric (hSymm : Symmetric F.Rel) : Symmetric F.RelTransGen := by
  intro x y rxy;
  induction rxy with
  | single h => exact TransGen.single $ hSymm h;
  | tail _ hyz ih => exact TransGen.trans (TransGen.single $ hSymm hyz) ih

end Frame.RelTransGen


abbrev Frame.TransitiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^+ ·)
postfix:95 "^+" => Frame.TransitiveClosure

namespace Frame.TransitiveClosure

variable {F : Frame}

lemma single {x y : F.World} (hxy : x ≺ y) : F^+.Rel x y := TransGen.single hxy

lemma rel_transitive : Transitive (F^+) := by simp;

lemma rel_symmetric (hSymm : Symmetric F.Rel) : Symmetric (F^+) := by simp_all

end Frame.TransitiveClosure


protected abbrev Frame.RelReflGen {F : Frame} : _root_.Rel F.World F.World := ReflGen (· ≺ ·)
scoped infix:45 " ≺^= " => Frame.RelReflGen

abbrev Frame.ReflexiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^= ·)
postfix:95 "^=" => Frame.ReflexiveClosure


protected abbrev Frame.RelIrreflGen {F : Frame} : _root_.Rel F.World F.World := IrreflGen (· ≺ ·)
scoped infix:45 " ≺^≠ " => Frame.RelIrreflGen

namespace Frame.RelIrreflGen

variable {F : Frame}

@[simp] lemma rel_irreflexive : Irreflexive F.RelIrreflGen := by simp [Irreflexive, Frame.RelIrreflGen, IrreflGen]

end Frame.RelIrreflGen


abbrev Frame.IrreflexiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^≠ ·)
postfix:95 "^≠" => Frame.IrreflexiveClosure

namespace Frame.IrreflexiveClosure

@[simp] lemma rel_irreflexive : Irreflexive (F^≠.Rel) := by simp [Irreflexive, Frame.RelIrreflGen, IrreflGen]

end Frame.IrreflexiveClosure

end LO.Kripke
