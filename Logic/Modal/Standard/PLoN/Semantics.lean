import Logic.Logic.System
import Logic.Modal.Standard.Formula
import Logic.Modal.Standard.Deduction

universe u v

namespace LO.Modal.Standard

namespace PLoN

protected structure Frame (α) where
  World : Type u
  World_nonempty : Nonempty World := by infer_instance
  Rel : Formula α → World → World → Prop

instance (F : PLoN.Frame α) : Nonempty F.World := F.World_nonempty

abbrev Frame.Rel' {F : PLoN.Frame α} (p : Formula α) (w w' : F.World) := F.Rel p w w'
scoped notation:45 x:90 " ≺[" p "] " y:90 => Frame.Rel' p x y

protected structure FiniteFrame (α) extends PLoN.Frame α where
  World_finite : Finite World := by infer_instance

protected abbrev FrameClass (α) := Set (PLoN.Frame α)

protected abbrev FiniteFrameClass (α) := Set (PLoN.FiniteFrame α)

abbrev FrameCondition (α) := PLoN.Frame α → Prop

abbrev FiniteFrameCondition (α) := PLoN.FiniteFrame α → Prop


abbrev Valuation (W : Type u) (α : Type u) := W → α → Prop

protected structure Model (α) where
  Frame : PLoN.Frame α
  Valuation : Valuation Frame.World α

abbrev Model.World (M : PLoN.Model α) := M.Frame.World
instance : CoeSort (PLoN.Model α) (Type _) where coe := Model.World

end PLoN

open Standard.PLoN

def Formula.PLoN_Satisfies (M : PLoN.Model α) (w : M.World) : Formula α → Prop
  | atom a  => M.Valuation w a
  | verum   => True
  | falsum  => False
  | and p q => (p.PLoN_Satisfies M w) ∧ (q.PLoN_Satisfies M w)
  | or p q  => (p.PLoN_Satisfies M w) ∨ (q.PLoN_Satisfies M w)
  | imp p q => (p.PLoN_Satisfies M w) → (q.PLoN_Satisfies M w)
  | box p   => ∀ w', w ≺[p] w' → (p.PLoN_Satisfies M w')


namespace Formula.PLoN_Satisfies

protected instance instSemantics (M : PLoN.Model α) : Semantics (Formula α) (M.World) := ⟨fun w ↦ Formula.PLoN_Satisfies M w⟩

variable {M : PLoN.Model α} {w : M.World} {p q : Formula α}

@[simp] protected lemma iff_models : w ⊧ p ↔ p.PLoN_Satisfies M w := by rfl

instance : Semantics.Tarski M.World where
  realize_top := by simp [PLoN_Satisfies];
  realize_bot := by simp [PLoN_Satisfies];
  realize_not := by simp [PLoN_Satisfies];
  realize_and := by simp [PLoN_Satisfies];
  realize_or  := by simp [PLoN_Satisfies];
  realize_imp := by simp [PLoN_Satisfies];

end Formula.PLoN_Satisfies


def Formula.PLoN_ValidOnModel (M : PLoN.Model α) (p : Formula α) : Prop := ∀ w : M.World, w ⊧ p

namespace Formula.PLoN_ValidOnModel

instance : Semantics (Formula α) (PLoN.Model α) := ⟨fun M ↦ Formula.PLoN_ValidOnModel M⟩

@[simp]
protected lemma Formula.PLoN_ValidOnModel.iff_models {M : PLoN.Model α} {p : Formula α}
: M ⊧ p ↔ Formula.PLoN_ValidOnModel M p := by rfl

instance : Semantics.Bot (PLoN.Model α) where
  realize_bot _ := by simp [Formula.PLoN_ValidOnModel];

end Formula.PLoN_ValidOnModel


def Formula.PLoN_ValidOnFrame (F : PLoN.Frame α) (p : Formula α) := ∀ V, (Model.mk F V) ⊧ p

namespace Formula.PLoN_ValidOnFrame

instance : Semantics (Formula α) (PLoN.Frame α) := ⟨fun F ↦ Formula.PLoN_ValidOnFrame F⟩

@[simp]
protected lemma Formula.PLoN_ValidOnFrame.iff_models {F : PLoN.Frame α} {p : Formula α}
: F ⊧ p ↔ Formula.PLoN_ValidOnFrame F p := by rfl

instance : Semantics.Bot (PLoN.Frame α) where
  realize_bot _ := by simp [Formula.PLoN_ValidOnFrame];

end Formula.PLoN_ValidOnFrame


def Formula.PLoN_ValidOnFrameClass (𝔽 : PLoN.FrameClass α) (p : Formula α) := ∀ (F : PLoN.Frame α), F ∈ 𝔽 → F ⊧ p

namespace Formula.PLoN_ValidOnFrameClass

instance : Semantics (Formula α) (PLoN.FrameClass α) := ⟨fun 𝔽 ↦ Formula.PLoN_ValidOnFrameClass 𝔽⟩

@[simp]
protected lemma Formula.PLoN_ValidOnFrameClass.iff_models {𝔽 : PLoN.FrameClass α} {p : Formula α}
: 𝔽 ⊧ p ↔ Formula.PLoN_ValidOnFrameClass 𝔽 p := by rfl

end Formula.PLoN_ValidOnFrameClass


namespace PLoN

notation "Th(" 𝓓 ")" => System.theory 𝓓

def DeductionParamterFrameClass (𝓓 : DeductionParameter α) : PLoN.FrameClass α := { F : PLoN.Frame α | F ⊧* Th(𝓓) }
notation "ℕ𝔽(" 𝓓 ")" => PLoN.DeductionParamterFrameClass 𝓓


class Definability (𝓓 : DeductionParameter α) (P : FrameCondition α) where
  defines : ∀ {F}, F ⊧* Th(𝓓) ↔ P F

lemma Definability.defines' (definability : Definability 𝓓 P) : ∀ {F}, F ∈ ℕ𝔽(𝓓) ↔ P F := definability.defines

open Formula

instance Definability.N : Definability (α := α) 𝐍 (λ _ => True) where
  defines := by
    simp [System.theory, PLoN_ValidOnFrame, PLoN_ValidOnModel];
    intro F p hp;
    induction hp using Deduction.inducition_with_nec! with
    | hMaxm h => simp at h;
    | hMdp ihpq ihp =>
      intro V w;
      exact (ihpq V w) (ihp V w)
    | hNec ihp =>
      intro V w w' _;
      exact ihp V w';
    | hDisj₃ =>
      simp_all only [PLoN_Satisfies];
      intros; rename_i hpr hqr hpq;
      cases hpq with
      | inl hp => exact hpr hp;
      | inr hq => exact hqr hq;
    | _ => simp_all [PLoN_Satisfies];

lemma FrameClassNonempty.N : Set.Nonempty (ℕ𝔽(𝐍) : PLoN.FrameClass α) := by
  existsi {World := PUnit, Rel := λ _ _ _ => True};
  apply Definability.defines' Definability.N |>.mpr;
  trivial;

end PLoN

end LO.Modal.Standard
