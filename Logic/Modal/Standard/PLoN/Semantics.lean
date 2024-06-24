import Logic.Modal.Standard.Deduction

universe u v

namespace LO.Modal.Standard

namespace PLoN

structure Frame (δ α) where
  [δ_inhabited : Inhabited δ]
  Rel : Formula α → δ → δ → Prop

abbrev Frame.World (_ : PLoN.Frame δ α) := δ

abbrev Frame.default {F : PLoN.Frame δ α} : F.World := F.δ_inhabited.default
scoped notation "﹫" => Frame.default


instance : CoeFun (PLoN.Frame δ α) (λ F => Formula α → F.World → F.World → Prop) := ⟨Frame.Rel⟩

abbrev Frame.Rel' {F : PLoN.Frame δ α} (p : Formula α) (x y : F.World) := F.Rel p x y
scoped notation:45 x:90 " ≺[" p "] " y:90 => Frame.Rel' p x y


structure FiniteFrame (δ α) extends Frame δ α where
  [δ_finite : Finite δ]

instance : Coe (FiniteFrame δ α) (Frame δ α) := ⟨λ F ↦ F.toFrame⟩


abbrev TerminalFrame (α) : FiniteFrame (Fin 1) α where
  Rel := λ _ _ _ => True


abbrev FrameClass (α : Type*) := Set ((δ : Type*) × PLoN.Frame δ α)


abbrev Valuation (F : PLoN.Frame δ α) (α : Type*) := F.World → α → Prop

structure Model (δ α) where
  Frame : PLoN.Frame δ α
  Valuation : PLoN.Valuation Frame α

abbrev Model.World (M : PLoN.Model δ α) := M.Frame.World
instance : CoeSort (PLoN.Model δ α) (Type _) := ⟨Model.World⟩

end PLoN

variable {δ α : Type*}

open Standard.PLoN

def Formula.plon_satisfies (M : PLoN.Model δ α) (w : M.World) : Formula α → Prop
  | atom a  => M.Valuation w a
  | verum   => True
  | falsum  => False
  | and p q => (p.plon_satisfies M w) ∧ (q.plon_satisfies M w)
  | or p q  => (p.plon_satisfies M w) ∨ (q.plon_satisfies M w)
  | imp p q => (p.plon_satisfies M w) → (q.plon_satisfies M w)
  | box p   => ∀ {w'}, w ≺[p] w' → (p.plon_satisfies M w')


namespace Formula.plon_satisfies

protected instance semantics (M : PLoN.Model δ α) : Semantics (Formula α) (M.World) := ⟨fun w ↦ Formula.plon_satisfies M w⟩

variable {M : PLoN.Model δ α} {w : M.World} {p q : Formula α}

@[simp] protected lemma iff_models : w ⊧ p ↔ p.plon_satisfies M w := by rfl

instance : Semantics.Tarski M.World where
  realize_top := by simp [plon_satisfies];
  realize_bot := by simp [plon_satisfies];
  realize_not := by simp [plon_satisfies];
  realize_and := by simp [plon_satisfies];
  realize_or  := by simp [plon_satisfies];
  realize_imp := by simp [plon_satisfies];

end Formula.plon_satisfies


def Formula.valid_on_PLoNModel (M : PLoN.Model δ α) (p : Formula α) : Prop := ∀ w : M.World, w ⊧ p

namespace Formula.valid_on_PLoNModel

instance : Semantics (Formula α) (PLoN.Model δ α) := ⟨fun M ↦ Formula.valid_on_PLoNModel M⟩

@[simp]
protected lemma iff_models {M : PLoN.Model δ α} {p : Formula α}
: M ⊧ p ↔ Formula.valid_on_PLoNModel M p := by rfl

instance : Semantics.Bot (PLoN.Model δ α) where
  realize_bot _ := by
    simp [Formula.valid_on_PLoNModel];
    use ﹫;

end Formula.valid_on_PLoNModel


def Formula.valid_on_PLoNFrame (F : PLoN.Frame δ α) (p : Formula α) := ∀ V, (Model.mk F V) ⊧ p

namespace Formula.valid_on_PLoNFrame

instance : Semantics (Formula α) (PLoN.Frame δ α) := ⟨fun F ↦ Formula.valid_on_PLoNFrame F⟩

@[simp]
protected lemma iff_models {F : PLoN.Frame δ α} {p : Formula α}
: F ⊧ p ↔ Formula.valid_on_PLoNFrame F p := by rfl

variable {F : Frame δ α}

instance : Semantics.Bot (PLoN.Frame δ α) where
  realize_bot _ := by simp [Formula.valid_on_PLoNFrame];

protected lemma nec (h : F ⊧ p) : F ⊧ □p := by
  intro V x y _;
  exact h V y;

protected lemma mdp (hpq : F ⊧ p ⟶ q) (hp : F ⊧ p) : F ⊧ q := by
  intro V x;
  exact (hpq V x) (hp V x);

end Formula.valid_on_PLoNFrame


def Formula.valid_on_PLoNFrameClass (𝔽 : PLoN.FrameClass α) (p : Formula α) := ∀ {δ F}, ⟨δ, F⟩ ∈ 𝔽 → F ⊧ p

namespace Formula.valid_on_PLoNFrameClass

instance : Semantics (Formula α) (PLoN.FrameClass α) := ⟨fun 𝔽 ↦ Formula.valid_on_PLoNFrameClass 𝔽⟩

variable {𝔽 : FrameClass α}

@[simp]
protected lemma iff_models {𝔽 : PLoN.FrameClass α} {p : Formula α} : 𝔽 ⊧ p ↔ Formula.valid_on_PLoNFrameClass 𝔽 p := by rfl

protected lemma nec (h : 𝔽 ⊧ p) : 𝔽 ⊧ □p := by
  intro _ _ hF;
  apply valid_on_PLoNFrame.nec;
  exact h hF;

protected lemma mdp (hpq : 𝔽 ⊧ p ⟶ q) (hp : 𝔽 ⊧ p) : 𝔽 ⊧ q := by
  intro _ _ hF;
  exact valid_on_PLoNFrame.mdp (hpq hF) (hp hF)

end Formula.valid_on_PLoNFrameClass


def DeductionParameter.DefinesPLoNFrameClass (𝓓 : DeductionParameter α) (𝔽 : PLoN.FrameClass α) := ∀ {δ}, ∀ {F : Frame δ α}, F ⊧* 𝓓.theory ↔ ⟨δ, F⟩ ∈ 𝔽

namespace PLoN


abbrev AllFrameClass (α) : FrameClass α := Set.univ

lemma AllFrameClass.nonempty : (AllFrameClass.{_, 0} α).Nonempty := by
  use ⟨Fin 1, TerminalFrame α⟩
  trivial;

open Formula

lemma N_defines : 𝐍.DefinesPLoNFrameClass (AllFrameClass α) := by
  intro δ F;
  simp [DeductionParameter.theory, System.theory, valid_on_PLoNFrame, valid_on_PLoNModel];
  intro p hp;
  induction hp using Deduction.inducition_with_necOnly! with
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

end PLoN

end LO.Modal.Standard
