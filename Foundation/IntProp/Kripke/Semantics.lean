import Foundation.Vorspiel.BinaryRelations
import Foundation.IntProp.Deduction

set_option autoImplicit false
universe u v

namespace LO.IntProp

open System


namespace Kripke

structure Frame where
  World : Type u
  Rel : Rel World World
  [world_nonempty : Nonempty World]
  [rel_po : IsPartialOrder _ Rel]

instance : CoeSort Frame (Type u) := ⟨Frame.World⟩
instance : CoeFun Frame (λ F => F.World → F.World → Prop) := ⟨Frame.Rel⟩
instance {F : Frame} : Nonempty F.World := F.world_nonempty
instance {F : Frame} : IsPartialOrder _ F.Rel := F.rel_po

abbrev Frame.Rel' {F : Frame} (x y : F.World) := F.Rel x y
infix:45 " ≺ " => Frame.Rel'

namespace Frame

variable {F : Frame}

@[trans] lemma rel_trans {x y z : F.World} : x ≺ y → y ≺ z → x ≺ z := IsTrans.trans x y z

@[refl, simp] lemma rel_refl {x : F.World} : x ≺ x := IsRefl.refl x

@[simp] lemma rel_antisymm {x y : F.World} : x ≺ y → y ≺ x → x = y := IsAntisymm.antisymm x y


end Frame

abbrev pointframe : Frame where
  World := PUnit
  Rel := fun _ _ => True

namespace pointframe

lemma is_symmetric : Symmetric pointframe.Rel := by simp [Symmetric]

lemma is_connected : Connected pointframe.Rel := by simp [Connected];

lemma is_confluent : Confluent pointframe.Rel := by simp [Confluent];

end pointframe


abbrev FrameClass := Set (Frame)

section

abbrev AllFrameClass : FrameClass := Set.univ

abbrev SymmetricFrameClass : FrameClass := { F : Kripke.Frame | Symmetric F }

abbrev ConfluentFrameClass : FrameClass := { F : Kripke.Frame | Confluent F }

abbrev ConnectedFrameClass : FrameClass := { F : Kripke.Frame | Connected F }

end


structure Valuation (F : Frame) where
  Val : F.World → ℕ → Prop
  hereditary : ∀ {w₁ w₂ : F.World}, (w₁ ≺ w₂) → ∀ {a}, (Val w₁ a) → (Val w₂ a)
instance {F : Frame} : CoeFun (Valuation F) (λ _ => F.World → ℕ → Prop) := ⟨Valuation.Val⟩

structure Model extends Frame where
  Val : Valuation toFrame
instance : CoeFun (Model) (λ M => M.World → ℕ → Prop) := ⟨fun m => m.Val⟩

end Kripke


open Kripke


open Formula

namespace Formula.Kripke

def Satisfies (M : Kripke.Model) (w : M.World) : Formula ℕ → Prop
  | atom a => M w a
  | ⊤      => True
  | ⊥      => False
  | φ ⋏ ψ  => Satisfies M w φ ∧ Satisfies M w ψ
  | φ ⋎ ψ  => Satisfies M w φ ∨ Satisfies M w ψ
  | ∼φ     => ∀ {w' : M.World}, (w ≺ w') → ¬Satisfies M w' φ
  | φ ➝ ψ => ∀ {w' : M.World}, (w ≺ w') → (Satisfies M w' φ → Satisfies M w' ψ)

namespace Satisfies

instance semantics (M : Kripke.Model) : Semantics (Formula ℕ) (M.World) := ⟨fun w ↦ Formula.Kripke.Satisfies M w⟩

variable {M : Kripke.Model} {w w' : M.World} {a : ℕ} {φ ψ χ : Formula ℕ}

@[simp] protected lemma iff_models : w ⊧ φ ↔ Formula.Kripke.Satisfies M w φ := iff_of_eq rfl

@[simp] lemma atom_def : w ⊧ atom a ↔ M w a := by simp [Satisfies];
@[simp] lemma top_def  : w ⊧ ⊤ ↔ True := by simp [Satisfies];
@[simp] lemma bot_def  : w ⊧ ⊥ ↔ False := by simp [Satisfies];
@[simp] lemma and_def  : w ⊧ φ ⋏ ψ ↔ w ⊧ φ ∧ w ⊧ ψ := by simp [Satisfies];
@[simp] lemma or_def   : w ⊧ φ ⋎ ψ ↔ w ⊧ φ ∨ w ⊧ ψ := by simp [Satisfies];
@[simp] lemma imp_def  : w ⊧ φ ➝ ψ ↔ ∀ {w' : M.World}, (w ≺ w') → (w' ⊧ φ → w' ⊧ ψ) := by simp [Satisfies, imp_iff_not_or];
@[simp] lemma neg_def  : w ⊧ ∼φ ↔ ∀ {w' : M.World}, (w ≺ w') → ¬(w' ⊧ φ) := by simp [Satisfies];

instance : Semantics.Top M.World where
  realize_top := by simp [Satisfies];

instance : Semantics.Bot M.World where
  realize_bot := by simp [Satisfies];

instance : Semantics.And M.World where
  realize_and := by simp [Satisfies];

instance : Semantics.Or M.World where
  realize_or := by simp [Satisfies];

lemma formula_hereditary
  (hw : w ≺ w') : w ⊧ φ → w' ⊧ φ := by
  induction φ using Formula.rec' with
  | hatom => apply M.Val.hereditary hw;
  | himp =>
    intro hpq v hv;
    exact hpq $ M.rel_trans hw hv;
  | hneg =>
    intro hp v hv;
    exact hp $ M.rel_trans hw hv;
  | hor => simp_all [Satisfies]; tauto;
  | _ => simp_all [Satisfies];


lemma neg_equiv : w ⊧ ∼φ ↔ w ⊧ φ ➝ ⊥ := by simp_all [Satisfies];

end Satisfies


open Satisfies


def ValidOnModel (M : Kripke.Model) (φ : Formula ℕ) := ∀ w : M.World, w ⊧ φ

namespace ValidOnModel

instance semantics : Semantics (Formula ℕ) (Model) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

variable {M : Model} {φ ψ χ : Formula ℕ}

@[simp] protected lemma iff_models : M ⊧ φ ↔ Formula.Kripke.ValidOnModel M φ := iff_of_eq rfl

protected lemma verum : M ⊧ ⊤ := by simp_all [ValidOnModel];

protected lemma andElim₁ : M ⊧ φ ⋏ ψ ➝ φ := by simp_all [ValidOnModel, Satisfies];

protected lemma andElim₂ : M ⊧ φ ⋏ ψ ➝ ψ := by simp_all [ValidOnModel, Satisfies];

protected lemma andInst₃ : M ⊧ φ ➝ ψ ➝ φ ⋏ ψ := by
  intro x y _ hp z Ryz hq;
  replace hp : Satisfies M z φ := formula_hereditary Ryz hp;
  exact ⟨hp, hq⟩;

protected lemma orInst₁ : M ⊧ φ ➝ φ ⋎ ψ := by simp_all [ValidOnModel, Satisfies];

protected lemma orInst₂ : M ⊧ ψ ➝ φ ⋎ ψ := by simp_all [ValidOnModel, Satisfies];

protected lemma orElim : M ⊧ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ) := by
  simp_all only [ValidOnModel.iff_models, ValidOnModel, Satisfies.iff_models, Satisfies.imp_def, Satisfies.or_def];
  intro w₁ w₂ _ hpr w₃ hw₂₃ hqr w₄ hw₃₄ hpq;
  cases hpq with
  | inl hp => exact hpr (M.rel_trans hw₂₃ hw₃₄) hp;
  | inr hq => exact hqr hw₃₄ hq;

protected lemma imply₁ : M ⊧ φ ➝ ψ ➝ φ := by
  intro x y _ hp z Ryz _;
  exact formula_hereditary Ryz hp;

protected lemma imply₂ : M ⊧ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := by
  intro x y _ hpqr z Ryz hpq w Rzw hp;
  have Ryw : y ≺ w := by trans z <;> assumption;
  have Rww : w ≺ w := by simp;
  exact hpqr Ryw hp Rww (hpq Rzw hp);

protected lemma mdp (hpq : M ⊧ φ ➝ ψ) (hp : M ⊧ φ) : M ⊧ ψ := by
  intro w;
  exact hpq w Frame.rel_refl $ hp w;

protected lemma bot : ¬M ⊧ ⊥ := by simp [ValidOnModel, Satisfies];

instance : Semantics.Bot (Kripke.Model) := ⟨λ _ => ValidOnModel.bot⟩

protected lemma efq : M ⊧ Axioms.EFQ φ := by simp [ValidOnModel, Satisfies];

protected lemma neg_equiv : M ⊧ Axioms.NegEquiv φ := by
  simp_all [ValidOnModel, Axioms.NegEquiv];
  intro w;
  constructor;
  . intro x _ h y rxy hyp; exact h rxy hyp;
  . intro x _ h y rxy; exact h rxy;

protected lemma lem : Symmetric M.Rel → M ⊧ Axioms.LEM φ := by
  simp_all [ValidOnModel, Satisfies, Symmetric];
  contrapose; push_neg;
  rintro ⟨x, nhxp, ⟨y, Rxy, hyp⟩⟩;
  use x, y;
  constructor;
  . exact Rxy;
  . by_contra Ryx;
    have := formula_hereditary Ryx hyp;
    contradiction;

protected lemma dum : Connected M.Rel → M ⊧ Axioms.Dummett φ ψ := by
  simp [ValidOnModel, Satisfies, Connected];
  contrapose; push_neg;
  rintro ⟨x, ⟨y, Rxy, hyp, nhyq⟩, ⟨z, Ryz, hzq, nhyp⟩⟩;
  use x, y, z;
  refine ⟨Rxy, Ryz, ?_, ?_⟩;
  . by_contra Ryz;
    have := formula_hereditary Ryz hyp;
    contradiction;
  . by_contra Rzy;
    have := formula_hereditary Rzy hzq;
    contradiction;

protected lemma wlem : Confluent M.Rel → M ⊧ Axioms.WeakLEM φ := by
  simp [ValidOnModel, Satisfies, Confluent];
  contrapose; push_neg;
  rintro ⟨x, ⟨y, Rxy, hyp⟩, ⟨z, Rxz, hz⟩⟩;
  use x, y, z;
  refine ⟨Rxy, Rxz, ?_⟩;
  rintro w Ryw;
  by_contra Rzw;
  have := formula_hereditary Ryw hyp;
  have := hz w Rzw;
  contradiction;

end ValidOnModel


def ValidOnFrame (F : Frame) (φ : Formula ℕ) := ∀ {V}, (⟨F, V⟩ : Kripke.Model) ⊧ φ


namespace ValidOnFrame

instance semantics : Semantics (Formula ℕ) (Frame) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

variable {F : Frame} {φ ψ χ : Formula ℕ}

@[simp] protected lemma models_iff : F ⊧ φ ↔ ValidOnFrame F φ := iff_of_eq rfl

protected lemma verum : F ⊧ ⊤ := ValidOnModel.verum

protected lemma andElim₁ : F ⊧ φ ⋏ ψ ➝ φ := ValidOnModel.andElim₁

protected lemma andElim₂ : F ⊧ φ ⋏ ψ ➝ ψ := ValidOnModel.andElim₂

protected lemma andInst₃ : F ⊧ φ ➝ ψ ➝ φ ⋏ ψ := ValidOnModel.andInst₃

protected lemma orInst₁ : F ⊧ φ ➝ φ ⋎ ψ := ValidOnModel.orInst₁

protected lemma orInst₂ : F ⊧ ψ ➝ φ ⋎ ψ := ValidOnModel.orInst₂

protected lemma orElim : F ⊧ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ) := ValidOnModel.orElim

protected lemma imply₁ : F ⊧ φ ➝ ψ ➝ φ := ValidOnModel.imply₁

protected lemma imply₂ : F ⊧ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := ValidOnModel.imply₂

protected lemma mdp (hpq : F ⊧ φ ➝ ψ) (hp : F ⊧ φ) : F ⊧ ψ := ValidOnModel.mdp hpq hp

protected lemma efq : F ⊧ Axioms.EFQ φ := ValidOnModel.efq

protected lemma neg_equiv : F ⊧ Axioms.NegEquiv φ := ValidOnModel.neg_equiv

protected lemma lem (F_symm : Symmetric F.Rel) : F ⊧ Axioms.LEM φ := ValidOnModel.lem F_symm

protected lemma dum (F_conn : Connected F.Rel) : F ⊧ Axioms.Dummett φ ψ := ValidOnModel.dum F_conn

protected lemma wlem (F_conf : Confluent F.Rel) : F ⊧ Axioms.WeakLEM φ := ValidOnModel.wlem F_conf

protected lemma bot : ¬F ⊧ ⊥ := by
  simp [ValidOnFrame.models_iff, ValidOnFrame];
  use ⟨(λ _ _ => True), by tauto⟩;

instance : Semantics.Bot (Frame) := ⟨λ _ => ValidOnFrame.bot⟩

end ValidOnFrame


@[simp] def ValidOnFrameClass (C : FrameClass) (φ : Formula ℕ) := ∀ F, F ∈ C → F ⊧ φ

namespace ValidOnFrameClass

variable {C : FrameClass} {φ ψ χ : Formula ℕ}

instance semantics : Semantics (Formula ℕ) (FrameClass) := ⟨fun C ↦ Kripke.ValidOnFrameClass C⟩

@[simp] protected lemma models_iff : C ⊧ φ ↔ Formula.Kripke.ValidOnFrameClass C φ := iff_of_eq rfl

protected lemma bot (h_nonempty : C.Nonempty) : ¬C ⊧ ⊥ := by
  simp [ValidOnFrameClass.models_iff, ValidOnFrameClass];
  exact h_nonempty;

end ValidOnFrameClass

end Formula.Kripke


namespace Kripke

/--
  A set of formula that valid on frame `F`.
-/
def Frame.theorems (F : Kripke.Frame) : Set (Formula ℕ) := { φ | F ⊧ φ }

namespace Frame.theorems

variable {F : Kripke.Frame}

lemma subset_efq : Axioms.EFQ.set ⊆ F.theorems := by
  rintro _ ⟨φ, rfl⟩ V;
  exact Formula.Kripke.ValidOnFrame.efq;


section

private lemma euclidean_of_subset_lem : (𝗟𝗘𝗠 ⊆ F.theorems) → Euclidean F := by
  simp [Frame.theorems];
  rintro h x y z Rxy Rxz;
  let M : Kripke.Model := ⟨F, λ v _ => z ≺ v, by simp; intro w v _ _; trans w <;> assumption⟩;
  suffices Kripke.Satisfies M y (atom default) by simpa [Kripke.Satisfies] using this;
  apply M.Val.hereditary Rxy;
  have := @h (atom default) M.Val x;
  simp only [Axioms.LEM, Semantics.Realize, Kripke.Satisfies, or_iff_not_imp_right] at this;
  apply this;
  push_neg;
  use z;
  constructor;
  . exact Rxz;
  . simp [Kripke.Satisfies];

/-
private lemma subset_lem_of_equality : Equality F → 𝗟𝗘𝗠 ⊆ F.theorems := by
  intro hEq φ V x;
  induction φ using Formula.rec' with
  | hatom a =>
    simp [Axioms.LEM, Kripke.ValidOnModel, Semantics.Realize, Kripke.Satisfies, or_iff_not_imp_right, Model.Val];
    intro y;
    have := hEq.mp Rxy; subst this;
    assumption;
  | _ => simp_all [Axioms.LEM, Kripke.ValidOnModel, Semantics.Realize, Kripke.Satisfies, Equality]; try tauto;

lemma subset_lem_iff_euclidean [Inhabited ℕ] : 𝗟𝗘𝗠 ⊆ F.theorems (α) ↔ Euclidean F := by
  constructor;
  . exact euclidean_of_subset_lem;
  . intro hEucl;
    exact subset_lem_of_equality $ equality_of_refl_assym_eucl (F.rel_refl) (F.rel_antisymm) hEucl;
-/

end

/-
section

lemma subset_wlem_iff_confluent : 𝗪𝗟𝗘𝗠 ⊆ F.theorems ↔ Confluent F := by
  constructor;
  . rintro h x y z ⟨Rxy, Rxz⟩;
    let M : Kripke.Model := ⟨F, λ {v _} => y ≺ v, by simp; intro w _ _ _; trans w <;> assumption⟩;
    have : ¬Kripke.Satisfies M x (∼(atom default)) := by
      simp [Kripke.Satisfies];
      use y;
      constructor;
      . exact Rxy;
      . apply F.rel_refl;
    have : Kripke.Satisfies M x (∼∼(atom default)) := by
      have := @h (atom default) M.Val x;
      simp only [Axioms.WeakLEM, Semantics.Realize] at this;
      apply or_iff_not_imp_left.mp $ Kripke.Satisfies.or_def.mp this;
      assumption;
    have := this Rxz; simp [Semantics.Realize, Kripke.Satisfies] at this;
    obtain ⟨w, ⟨Rzw, hw⟩⟩ := this;
    use w;
  . intro hCon φ V Vherd x;
    induction φ using Formula.rec' with
    | hatom a =>
      simp [Axioms.WeakLEM, Kripke.ValidOnModel, Semantics.Realize, Kripke.Satisfies, or_iff_not_imp_left];
      intro y Rxy hy z Rxz;
      obtain ⟨w, ⟨Ryw, Rzw⟩⟩ := hCon ⟨Rxy, Rxz⟩;
      use w;
      constructor;
      . exact Rzw;
      . exact Vherd Ryw hy;
    | hverum => sorry
    | hand => sorry;
    | hor φ ψ hφ hψ => sorry;
    | _ => sorry;

end
-/

/-
section

lemma subset_dum_iff_connected [Inhabited ℕ] : 𝗗𝘂𝗺 ⊆ F.theorems (α) ↔ Connected F := by
  simp [Frame.theorems];
  constructor;
  . rintro h x y z ⟨Rxy, Rxz⟩;
    sorry;
    -- let V : Valuation F ℕ := λ {v _} => y ≺ v;
    -- let M : Kripke.Model := ⟨F, V, by simp [V]; intro _ _ R₁ R₂; exact F.rel_trans R₂ R₁⟩;
  . sorry;

end
-/

end Frame.theorems

end Kripke


namespace Hilbert

open Formula.Kripke

variable {C : Kripke.FrameClass}
variable {H : Hilbert ℕ} {φ : Formula ℕ}

namespace Kripke

abbrev frameclassOf (H : Hilbert ℕ) : FrameClass := { F | F ⊧* H.theorems }

lemma sound : H ⊢! φ → (frameclassOf H) ⊧ φ := by
  intro hφ F hF;
  simp [System.theory] at hF;
  exact hF φ hφ;

instance : Sound H (frameclassOf H) := ⟨sound⟩

lemma unprovable_bot (hNonempty : (frameclassOf H).Nonempty) : H ⊬ ⊥ := by
  apply not_imp_not.mpr sound;
  simp [Semantics.Realize];
  obtain ⟨F, hF⟩ := hNonempty;
  use F;
  constructor;
  . exact hF;
  . exact Semantics.Bot.realize_bot (F := Formula ℕ) (M := Frame) F;

instance (h_nonempty : (frameclassOf H).Nonempty) : System.Consistent H := System.Consistent.of_unprovable $ unprovable_bot h_nonempty

class Characterize (H : Hilbert ℕ) (C : Kripke.FrameClass) where
  characterize : C ⊆ (frameclassOf H)
  nonempty : C.Nonempty

lemma sound_of_subset [Characterize H C] : H ⊢! φ → C ⊧ φ := by
  intro h F hF;
  apply sound h;
  exact Characterize.characterize hF;

instance instSoundOfSubset [Characterize H C] : Sound H C := ⟨sound_of_subset⟩

-- TODO: change to `instance`
lemma instConsistentOf [Characterize H C] : H.Consistent := by
  apply System.Consistent.of_unprovable;
  apply Sound.not_provable_of_countermodel (𝓢 := H) (𝓜 := C) (F := Formula ℕ) (φ := ⊥);
  exact Kripke.ValidOnFrameClass.bot $ Characterize.nonempty H;

end Kripke


open Kripke

macro_rules | `(tactic| trivial) => `(tactic|
    first
    | apply ValidOnFrame.verum;
    | apply ValidOnFrame.imply₁;
    | apply ValidOnFrame.imply₂;
    | apply ValidOnFrame.andElim₁;
    | apply ValidOnFrame.andElim₂;
    | apply ValidOnFrame.andInst₃;
    | apply ValidOnFrame.orInst₁;
    | apply ValidOnFrame.orInst₂;
    | apply ValidOnFrame.orElim;
    | apply ValidOnFrame.neg_equiv;
    | exact ValidOnFrame.mdp (by assumption) (by assumption);
  )


namespace Int

lemma Kripke.subset_univ : Set.univ ⊆ frameclassOf (Hilbert.Int ℕ) := by
  intro F _;
  simp [Hilbert.theorems, System.theory];
  intro φ hφ;
  induction hφ using Hilbert.Deduction.rec! with
  | eaxm h => obtain ⟨_, rfl⟩ := h; exact ValidOnFrame.efq;
  | _ => trivial;

instance Kripke.characterize : Characterize (Hilbert.Int ℕ) (Set.univ) := ⟨Kripke.subset_univ, ⟨Kripke.pointframe, by tauto⟩⟩

instance Kripke.sound : Sound (Hilbert.Int ℕ) (AllFrameClass) := instSoundOfSubset (H := Hilbert.Int ℕ) (C := AllFrameClass)

instance Kripke.consistent : (Hilbert.Int ℕ).Consistent := instConsistentOf.{u} (H := Hilbert.Int ℕ) (C := AllFrameClass)

end Int


namespace Cl

lemma Kripke.subset_symmetric : SymmetricFrameClass ⊆ frameclassOf (Hilbert.Cl ℕ) := by
  intro F hF;
  simp at hF;
  simp [Hilbert.theorems, System.theory];
  intro φ hφ;
  induction hφ using Hilbert.Deduction.rec! with
  | eaxm h =>
    rcases h with (⟨_, rfl⟩ | ⟨_, rfl⟩);
    . apply ValidOnFrame.efq;
    . apply ValidOnFrame.lem; exact hF;
  | _ => trivial;

instance Kripke.characterize : Characterize (Hilbert.Cl ℕ) (SymmetricFrameClass) := ⟨subset_symmetric, ⟨pointframe, pointframe.is_symmetric⟩⟩

instance Kripke.sound : Sound (Hilbert.Cl ℕ) (SymmetricFrameClass) := instSoundOfSubset (H := Hilbert.Cl ℕ) (C := SymmetricFrameClass)

instance Kripke.consistent : (Hilbert.Cl ℕ).Consistent := instConsistentOf.{u} (H := Hilbert.Cl ℕ) (C := SymmetricFrameClass)

end Cl


namespace KC

lemma Kripke.subset_concluent : ConfluentFrameClass ⊆ (frameclassOf (Hilbert.KC ℕ)) := by
  intro F hF;
  simp at hF;
  simp [Hilbert.theorems, System.theory];
  intro φ hφ;
  induction hφ using Hilbert.Deduction.rec! with
  | eaxm h =>
    rcases h with (⟨_, rfl⟩ | ⟨_, _, rfl⟩);
    . apply ValidOnFrame.efq;
    . apply ValidOnFrame.wlem; exact hF;
  | _ => trivial;

instance Kripke.characterize : Characterize (Hilbert.KC ℕ) (ConfluentFrameClass) := ⟨subset_concluent, ⟨pointframe, pointframe.is_confluent⟩⟩

instance Kripke.sound : Sound (Hilbert.KC ℕ) (ConfluentFrameClass) := instSoundOfSubset (H := Hilbert.KC ℕ) (C := ConfluentFrameClass)

instance Kripke.consistent : (Hilbert.KC ℕ).Consistent := instConsistentOf.{u} (H := Hilbert.KC ℕ) (C := ConfluentFrameClass)

end KC


namespace LC

lemma Kripke.subset_connected : ConnectedFrameClass ⊆ frameclassOf (Hilbert.LC ℕ) := by
  intro F hF;
  simp at hF;
  simp [Hilbert.theorems, System.theory];
  intro φ hφ;
  induction hφ using Hilbert.Deduction.rec! with
  | eaxm h =>
    rcases h with (⟨_, rfl⟩ | ⟨_, _, rfl⟩);
    . apply ValidOnFrame.efq;
    . apply ValidOnFrame.dum; exact hF;
  | _ => trivial;

instance Kripke.characterize : Characterize (Hilbert.LC ℕ) (ConnectedFrameClass) := ⟨subset_connected, ⟨pointframe, pointframe.is_connected⟩⟩

instance Kripke.sound : Sound (Hilbert.LC ℕ) (ConnectedFrameClass) := instSoundOfSubset (H := Hilbert.LC ℕ) (C := ConnectedFrameClass)

instance Kripke.consistent : (Hilbert.LC ℕ).Consistent := instConsistentOf.{u} (H := Hilbert.LC ℕ) (C := ConnectedFrameClass)

end LC

end Hilbert





/-
section Classical

open LO.Kripke

namespace Formula.Kripke

abbrev ClassicalSatisfies (V : ClassicalValuation ℕ) (φ : Formula ℕ) : Prop := Satisfies (ClassicalModel V) () φ

instance : Semantics (Formula ℕ) (ClassicalValuation ℕ) := ⟨ClassicalSatisfies⟩

namespace ClassicalSatisfies

variable {V : ClassicalValuation ℕ}

@[simp] lemma atom_def : V ⊧ atom a ↔ V a := by simp only [Semantics.Realize, Satisfies]

instance : Semantics.Tarski (ClassicalValuation ℕ) where
  realize_top := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_bot := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_or  := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_and := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_imp := by simp [Semantics.Realize, Satisfies]; tauto;
  realize_not := by simp [Semantics.Realize, Satisfies]; tauto;

end ClassicalSatisfies

end Formula.Kripke


namespace Kripke

open Formula.Kripke (ClassicalSatisfies)

lemma ValidOnClassicalFrame_iff : (Kripke.FrameClassOfHilbert.{u, 0} (Hilbert.Cl ℕ)) ⊧ φ → ∀ (V : ClassicalValuation ℕ), V ⊧ φ := by
  intro h V;
  refine @h (ClassicalFrame) ?_ (λ _ a => V a) (by simp [Valuation.atomic_hereditary]) ();
  . apply @Cl_Characteraizable ℕ |>.characterize;
    refine ⟨ClassicalFrame.reflexive, ClassicalFrame.transitive, ClassicalFrame.symmetric⟩;

lemma notClassicalValid_of_exists_ClassicalValuation : (∃ (V : ClassicalValuation ℕ), ¬(V ⊧ φ)) → ¬(Kripke.FrameClassOfHilbert.{u, 0} (Hilbert.Cl ℕ)) ⊧ φ := by
  contrapose; push_neg;
  have := @ValidOnClassicalFrame_iff ℕ φ;
  exact this;

lemma unprovable_classical_of_exists_ClassicalValuation (h : ∃ (V : ClassicalValuation ℕ), ¬(V ⊧ φ)) : (Hilbert.Cl ℕ) ⊬ φ := by
  apply not_imp_not.mpr $ Kripke.sound.{u, 0};
  apply notClassicalValid_of_exists_ClassicalValuation;
  assumption;

end Kripke

end Classical
-/

end LO.IntProp
