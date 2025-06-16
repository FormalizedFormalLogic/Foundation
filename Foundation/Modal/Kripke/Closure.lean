import Foundation.Modal.Kripke.Basic
import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Vorspiel.HRel.Basic

namespace LO.Modal.Kripke

namespace Frame

open Relation

variable {F : Frame} {x y z : F.World}

abbrev ReflRel := F.Rel.ReflGen
infix:50 " ≺^= " => ReflRel

abbrev ReflGen (F : Frame) : Frame := ⟨F.World, (· ≺^= ·)⟩
postfix:95 "^=" => ReflGen

namespace ReflGen

instance : Coe (F.World) (F^=.World) := ⟨id⟩

instance [Finite F] : Finite (F^=) := inferInstance
instance [F.IsFinite] : (F^=).IsFinite := inferInstance

instance : (F^=).IsReflexive := by simp

end ReflGen


abbrev TransRel := F.Rel.TransGen
infix:50 " ≺^+ " => TransRel

abbrev TransGen (F : Frame) : Frame := ⟨F.World, (· ≺^+ ·)⟩
postfix:95 "^+" => TransGen

namespace TransGen

instance : Coe (F.World) (F^+.World) := ⟨id⟩

instance [F.IsFinite] : (F^+).IsFinite := inferInstance

instance : (F^+).IsTransitive := by simp

instance [F.IsReflexive] : F^+.IsReflexive := by simp

instance [F.IsReflexive] : F^+.IsPreorder where

instance isSymmetric [F.IsSymmetric] : F^+.IsSymmetric := by simp

instance [F.IsReflexive] [F.IsSymmetric] : F^+.IsEquivalence where

end TransGen

abbrev ReflTransRel := F.Rel.ReflTransGen
infix:50 " ≺^* " => ReflTransRel

abbrev ReflTransGen (F : Frame) : Frame := ⟨F.World, (· ≺^* ·)⟩
postfix:95 "^*" => ReflTransGen

namespace ReflTransGen

instance : Coe (F.World) (F^*.World) := ⟨id⟩

instance [Finite F.World] : Finite (F^*).World := inferInstance

instance : (F^*).IsPreorder where

instance [F.IsSymmetric] : F^*.IsSymmetric where symm := by simp only; apply IsSymm.symm;

instance [F.IsSymmetric] : F^*.IsEquivalence where

end ReflTransGen


protected abbrev IsIrreflexive (F : Frame) := IsIrrefl _ F

@[simp] lemma irrefl [F.IsIrreflexive] (x : F) : ¬x ≺ x := by apply IsIrrefl.irrefl;

abbrev IrreflGen (F : Frame) : Frame := ⟨F.World, F.Rel.IrreflGen⟩
postfix:95 "^≠" => IrreflGen

namespace IrreflGen

instance : Coe (F.World) (F^≠.World) := ⟨id⟩

instance [Finite F] : Finite (F^≠) := inferInstance
instance [F.IsFinite] : (F^≠).IsFinite := inferInstance

instance : F^≠.IsIrreflexive where irrefl := by apply IsIrrefl.irrefl;

end IrreflGen

end Frame

end LO.Modal.Kripke
