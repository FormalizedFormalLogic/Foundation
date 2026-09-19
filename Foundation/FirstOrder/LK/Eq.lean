module

public import Foundation.FirstOrder.Tarski.Eq
public import Foundation.FirstOrder.LK.Soundness

@[expose] public section

namespace FFL

namespace FirstOrder

universe u v

variable {L : Language} {ξ : Type*} [Semiformula.Operator.Eq L]

lemma consequence_iff_eq {T : Theory L} [𝗘𝗤 L ⪯ T] {σ : Sentence L} :
    T ⊨[Tarski.Struc.{v, u} L] σ ↔
      (∀ (M : Type v) [Nonempty M] [Tarski.Structure L M] [Tarski.Structure.Eq L M],
        M↓[L] ⊧* T → M↓[L] ⊧ σ) :=
  consequence_iff_eq_of_models_eq (fun _ _ _ hM ↦ models_of_subtheory hM)

lemma consequence_iff_eq' {T : Theory L} [𝗘𝗤 L ⪯ T] {σ : Sentence L} :
    T ⊨[Tarski.Struc.{v, u} L] σ ↔
      (∀ (M : Type v) [Nonempty M] [Tarski.Structure L M] [Tarski.Structure.Eq L M]
        [M↓[L] ⊧* T], M↓[L] ⊧ σ) := by
  rw [consequence_iff_eq]

lemma satisfiable_iff_eq {T : Theory L} [𝗘𝗤 L ⪯ T] :
    Semantics.Satisfiable (Tarski.Struc.{v, u} L) T ↔
      (∃ (M : Type v) (_ : Nonempty M) (_ : Tarski.Structure L M) (_ : Tarski.Structure.Eq L M),
        M↓[L] ⊧* T) :=
  satisfiable_iff_eq_of_models_eq (fun _ _ _ hM ↦ models_of_subtheory hM)

instance {T : Theory L} [𝗘𝗤 L ⪯ T] (sat : Semantics.Satisfiable (Tarski.Struc.{v, u} L) T) :
    (ModelOfSat sat)↓[L] ⊧* 𝗘𝗤 L := models_of_subtheory (ModelOfSat.models sat)

def ModelOfSatEq {T : Theory L} [𝗘𝗤 L ⪯ T]
    (sat : Semantics.Satisfiable (Tarski.Struc.{v, u} L) T) : Type _ :=
  Tarski.Structure.Eq.QuotEq L (ModelOfSat sat)

namespace ModelOfSatEq

variable {T : Theory L} [𝗘𝗤 L ⪯ T] (sat : Semantics.Satisfiable (Tarski.Struc.{v, u} L) T)

noncomputable instance : Nonempty (ModelOfSatEq sat) := Tarski.Structure.Eq.QuotEq.inhabited

noncomputable instance struc : Tarski.Structure L (ModelOfSatEq sat) :=
  Tarski.Structure.Eq.QuotEq.struc

noncomputable instance : Tarski.Structure.Eq L (ModelOfSatEq sat) :=
  Tarski.Structure.Eq.QuotEq.structureEq

lemma models : (ModelOfSatEq sat)↓[L] ⊧* T :=
  have e : ModelOfSatEq sat ≡ₑ[L] ModelOfSat sat :=
    Tarski.Structure.Eq.QuotEq.elementaryEquiv L (ModelOfSat sat)
  e.modelsTheory.mpr (ModelOfSat.models _)

instance mod : (ModelOfSatEq sat)↓[L] ⊧* T := models sat

open Semiterm Semiformula

noncomputable instance [Operator.Zero L] : Zero (ModelOfSatEq sat) :=
  ⟨(@Operator.Zero.zero L _).val ![]⟩

instance strucZero [Operator.Zero L] : Tarski.Structure.Zero L (ModelOfSatEq sat) := ⟨rfl⟩

noncomputable instance [Operator.One L] : One (ModelOfSatEq sat) :=
  ⟨(@Operator.One.one L _).val ![]⟩

instance [Operator.One L] : Tarski.Structure.One L (ModelOfSatEq sat) := ⟨rfl⟩

noncomputable instance [Operator.Add L] : Add (ModelOfSatEq sat) :=
  ⟨fun x y ↦ (@Operator.Add.add L _).val ![x, y]⟩

instance [Operator.Add L] : Tarski.Structure.Add L (ModelOfSatEq sat) := ⟨fun _ _ ↦ rfl⟩

noncomputable instance [Operator.Mul L] : Mul (ModelOfSatEq sat) :=
  ⟨fun x y ↦ (@Operator.Mul.mul L _).val ![x, y]⟩

instance [Operator.Mul L] : Tarski.Structure.Mul L (ModelOfSatEq sat) := ⟨fun _ _ ↦ rfl⟩

instance [Operator.LT L] : LT (ModelOfSatEq sat) :=
  ⟨fun x y ↦ (@Operator.LT.lt L _).val ![x, y]⟩

instance [Operator.LT L] : Tarski.Structure.LT L (ModelOfSatEq sat) := ⟨fun _ _ ↦ iff_of_eq rfl⟩

instance [Operator.Mem L] : Membership (ModelOfSatEq sat) (ModelOfSatEq sat) :=
  ⟨fun x y ↦ (@Operator.Mem.mem L _).val ![y, x]⟩

instance [Operator.Mem L] : Tarski.Structure.Mem L (ModelOfSatEq sat) := ⟨fun _ _ ↦ iff_of_eq rfl⟩

end ModelOfSatEq

end FirstOrder

end FFL

end
