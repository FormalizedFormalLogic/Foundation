import Foundation.Modal.Kripke.Basic
import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Vorspiel.HRel.Basic

namespace LO.Modal.Kripke

namespace Frame

open Relation

variable {F : Frame} {x y z : F.World}


abbrev ReflGen (F : Frame) : Frame := ⟨F.World, F.Rel.ReflGen⟩
postfix:95 "^=" => ReflGen

namespace ReflGen

instance [Finite F] : Finite (F^=) := inferInstance
instance [F.IsFinite] : (F^=).IsFinite := inferInstance

instance : (F^=).IsReflexive where
  refl := by sorry

end ReflGen


abbrev TransGen (F : Frame) : Frame := ⟨F.World, F.Rel.TransGen⟩
postfix:95 "^+" => TransGen

namespace TransGen

instance [Finite F] : Finite (F^+) := inferInstance
instance [F.IsFinite] : (F^+).IsFinite := inferInstance

instance : (F^+).IsTransitive := by sorry

instance [IsRefl _ F.Rel] : IsRefl _ (F^+).Rel := ⟨fun a => TransGen.single (IsRefl.refl a)⟩
instance [IsRefl _ F.Rel] : (F^+).IsPreorder where

protected instance isSymm [IsSymm _ F.Rel] : IsSymm _ (F^+).Rel := ⟨by
  intro x y rxy;
  induction rxy with
  | single h => exact TransGen.single $ (IsSymm.symm _ _) h;
  | tail _ hyz ih => exact TransGen.trans (TransGen.single $ (IsSymm.symm _ _) hyz) ih
⟩

end TransGen


abbrev ReflTransGen (F : Frame) : Frame := ⟨F.World, F.Rel.ReflTransGen⟩
postfix:95 "^*" => ReflTransGen

namespace ReflTransGen

instance [Finite F.World] : Finite (F^*).World := inferInstance

instance : (F^*).IsPreorder where

instance [F.IsSymmetric] : (F^*).IsSymmetric := by sorry
instance [F.IsSymmetric] : (F^*).IsEquiv where

end ReflTransGen


abbrev IrreflGen (F : Frame) : Frame := ⟨F.World, F.Rel.IrreflGen⟩
postfix:95 "^≠" => IrreflGen

namespace IrreflGen

instance [Finite F] : Finite (F^≠) := inferInstance
instance [F.IsFinite] : (F^≠).IsFinite := inferInstance

instance : IsIrrefl _ (F^≠.Rel) := sorry

end IrreflGen

end Frame

end LO.Modal.Kripke
