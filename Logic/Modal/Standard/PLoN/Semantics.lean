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

def Formula.plon_satisfies (M : PLoN.Model α) (w : M.World) : Formula α → Prop
  | atom a  => M.Valuation w a
  | verum   => True
  | falsum  => False
  | and p q => (p.plon_satisfies M w) ∧ (q.plon_satisfies M w)
  | or p q  => (p.plon_satisfies M w) ∨ (q.plon_satisfies M w)
  | imp p q => (p.plon_satisfies M w) → (q.plon_satisfies M w)
  | box p   => ∀ w', w ≺[p] w' → (p.plon_satisfies M w')


namespace Formula.plon_satisfies

protected instance instSemantics (M : PLoN.Model α) : Semantics (Formula α) (M.World) := ⟨fun w ↦ Formula.plon_satisfies M w⟩

variable {M : PLoN.Model α} {w : M.World} {p q : Formula α}

@[simp] protected lemma iff_models : w ⊧ p ↔ p.plon_satisfies M w := by rfl

instance : Semantics.Tarski M.World where
  realize_top := by simp [plon_satisfies];
  realize_bot := by simp [plon_satisfies];
  realize_not := by simp [plon_satisfies];
  realize_and := by simp [plon_satisfies];
  realize_or  := by simp [plon_satisfies];
  realize_imp := by simp [plon_satisfies];

end Formula.plon_satisfies


def Formula.valid_on_PLoNModel (M : PLoN.Model α) (p : Formula α) : Prop := ∀ w : M.World, w ⊧ p

namespace Formula.valid_on_PLoNModel

instance : Semantics (Formula α) (PLoN.Model α) := ⟨fun M ↦ Formula.valid_on_PLoNModel M⟩

@[simp]
protected lemma Formula.valid_on_PLoNModel.iff_models {M : PLoN.Model α} {p : Formula α}
: M ⊧ p ↔ Formula.valid_on_PLoNModel M p := by rfl

instance : Semantics.Bot (PLoN.Model α) where
  realize_bot _ := by simp [Formula.valid_on_PLoNModel];

end Formula.valid_on_PLoNModel


def Formula.valid_on_PLoNFrame (F : PLoN.Frame α) (p : Formula α) := ∀ V, (Model.mk F V) ⊧ p

namespace Formula.valid_on_PLoNFrame

instance : Semantics (Formula α) (PLoN.Frame α) := ⟨fun F ↦ Formula.valid_on_PLoNFrame F⟩

@[simp]
protected lemma Formula.valid_on_PLoNFrame.iff_models {F : PLoN.Frame α} {p : Formula α}
: F ⊧ p ↔ Formula.valid_on_PLoNFrame F p := by rfl

instance : Semantics.Bot (PLoN.Frame α) where
  realize_bot _ := by simp [Formula.valid_on_PLoNFrame];

end Formula.valid_on_PLoNFrame


def Formula.valid_on_PLoNFrameClass (𝔽 : PLoN.FrameClass α) (p : Formula α) := ∀ (F : PLoN.Frame α), F ∈ 𝔽 → F ⊧ p

namespace Formula.valid_on_PLoNFrameClass

instance : Semantics (Formula α) (PLoN.FrameClass α) := ⟨fun 𝔽 ↦ Formula.valid_on_PLoNFrameClass 𝔽⟩

@[simp]
protected lemma Formula.valid_on_PLoNFrameClass.iff_models {𝔽 : PLoN.FrameClass α} {p : Formula α}
: 𝔽 ⊧ p ↔ Formula.valid_on_PLoNFrameClass 𝔽 p := by rfl

end Formula.valid_on_PLoNFrameClass


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
    simp [System.theory, valid_on_PLoNFrame, valid_on_PLoNModel];
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
      simp_all only [plon_satisfies];
      intros; rename_i hpr hqr hpq;
      cases hpq with
      | inl hp => exact hpr hp;
      | inr hq => exact hqr hq;
    | _ => simp_all [plon_satisfies];

lemma FrameClassNonempty.N : Set.Nonempty (ℕ𝔽(𝐍) : PLoN.FrameClass α) := by
  existsi {World := PUnit, Rel := λ _ _ _ => True};
  apply Definability.defines' Definability.N |>.mpr;
  trivial;

end PLoN

end LO.Modal.Standard
