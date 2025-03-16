import Foundation.Modal.Kripke.Basic
import Foundation.Vorspiel.BinaryRelations

namespace LO.Modal.Kripke

namespace Frame

open Relation

variable {F : Frame} {x y z : F.World}


section trans_refl

abbrev RelReflTrans : _root_.Rel F.World F.World := ReflTransGen (· ≺ ·)
infix:50 " ≺^* " => RelReflTrans

abbrev mkTransReflClosure (F : Frame) : Frame := ⟨F.World, (· ≺^* ·)⟩
postfix:95 "^*" => mkTransReflClosure

namespace mkTransReflClosure

instance [Finite F.World] : Finite (F^*).World := inferInstance

instance : IsPreorder _ (F^*).Rel where

instance [IsSymm _ F.Rel] : IsSymm _ (F^*).Rel := ⟨by
  apply ReflTransGen.symmetric;
  exact IsSymm.symm
⟩
instance [IsSymm _ F.Rel] : IsEquiv _ (F^*).Rel where

end mkTransReflClosure

end trans_refl


section trans

abbrev RelTrans : _root_.Rel F.World F.World := TransGen (· ≺ ·)
infix:50 " ≺^+ " => RelTrans

abbrev mkTransClosure (F : Frame) : Frame := ⟨F.World, (· ≺^+ ·)⟩
postfix:95 "^+" => mkTransClosure

namespace mkTransClosure

instance [Finite F] : Finite (F^+) := inferInstance
instance [F.IsFinite] : (F^+).IsFinite := inferInstance

instance : IsTrans _ (F^+).Rel := inferInstance

instance [IsRefl _ F.Rel] : IsRefl _ (F^+).Rel := ⟨fun a => TransGen.single (IsRefl.refl a)⟩

instance [IsRefl _ F.Rel] : IsPreorder _ (F^+).Rel where

instance [IsSymm _ F.Rel] : IsSymm _ (F^+).Rel := ⟨by
  intro x y rxy;
  induction rxy with
  | single h => exact TransGen.single $ (IsSymm.symm _ _) h;
  | tail _ hyz ih => exact TransGen.trans (TransGen.single $ (IsSymm.symm _ _) hyz) ih
⟩

end mkTransClosure

end trans


section refl

abbrev RelRefl : _root_.Rel F.World F.World := ReflGen (· ≺ ·)
infix:50 " ≺^= " => RelRefl

abbrev mkReflClosure (F : Frame) : Frame := ⟨F.World, (· ≺^= ·)⟩
postfix:95 "^=" => mkReflClosure

namespace mkReflClosure

instance [Finite F] : Finite (F^=) := inferInstance
instance [F.IsFinite] : (F^=).IsFinite := inferInstance

instance : IsRefl _ (F^=.Rel) := inferInstance

end mkReflClosure

end refl


section irrefl

abbrev RelIrrefl : _root_.Rel F.World F.World := IrreflGen (· ≺ ·)
infix:50 " ≺^≠ " => RelIrrefl

abbrev mkIrreflClosure (F : Frame) : Frame := ⟨F.World, (· ≺^≠ ·)⟩
postfix:95 "^≠" => mkIrreflClosure

namespace mkIrreflClosure

instance [Finite F] : Finite (F^≠) := inferInstance
instance [F.IsFinite] : (F^≠).IsFinite := inferInstance

instance : IsIrrefl _ (F^≠.Rel) := ⟨by simp [IrreflGen]⟩

end mkIrreflClosure

end irrefl

end Frame


end LO.Modal.Kripke
