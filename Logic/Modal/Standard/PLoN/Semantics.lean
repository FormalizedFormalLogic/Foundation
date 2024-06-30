import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Deduction

namespace LO.Modal.Standard

namespace PLoN

structure Frame (α) where
  World : Type*
  [World_inhabited : Inhabited World]
  Rel : Formula α → World → World → Prop

abbrev Frame.default {F : PLoN.Frame α} : F.World := F.World_inhabited.default
scoped notation "﹫" => Frame.default


instance : CoeFun (PLoN.Frame α) (λ F => Formula α → F.World → F.World → Prop) := ⟨Frame.Rel⟩

abbrev Frame.Rel' {F : PLoN.Frame α} (p : Formula α) (x y : F.World) := F.Rel p x y
scoped notation:45 x:90 " ≺[" p "] " y:90 => Frame.Rel' p x y


structure FiniteFrame (α) extends Frame α where
  [World_finite : Finite World]

instance : Coe (FiniteFrame α) (Frame α) := ⟨λ F ↦ F.toFrame⟩


abbrev terminalFrame (α) : FiniteFrame α where
  World := Unit
  Rel := λ _ _ _ => True


abbrev FrameClass (α : Type*) := Set (PLoN.Frame α)


abbrev Valuation (F : PLoN.Frame α) (α : Type*) := F.World → α → Prop

structure Model (α) where
  Frame : PLoN.Frame α
  Valuation : PLoN.Valuation Frame α

abbrev Model.World (M : PLoN.Model α) := M.Frame.World
instance : CoeSort (PLoN.Model α) (Type _) := ⟨Model.World⟩



end PLoN

variable {α : Type*}

open Standard.PLoN

def Formula.PLoN.Satisfies (M : PLoN.Model α) (w : M.World) : Formula α → Prop
  | atom a  => M.Valuation w a
  | falsum  => False
  | p ⟶ q => (PLoN.Satisfies M w p) → (PLoN.Satisfies M w q)
  | □p   => ∀ {w'}, w ≺[p] w' → (PLoN.Satisfies M w' p)


namespace Formula.PLoN.Satisfies

protected instance semantics (M : PLoN.Model α) : Semantics (Formula α) (M.World) := ⟨fun w ↦ Formula.PLoN.Satisfies M w⟩

variable {M : PLoN.Model α} {x : M.World} {p q : Formula α}

@[simp] protected lemma iff_models : x ⊧ p ↔ PLoN.Satisfies M x p := by rfl

lemma box_def : x ⊧ □p ↔ ∀ y, x ≺[p] y → y ⊧ p := by simp [PLoN.Satisfies];

lemma not_def : x ⊧ ~p ↔ ¬(x ⊧ p) := by
  induction p using Formula.rec' generalizing x with
  | _ => simp_all [Satisfies]; try tauto;
instance : Semantics.Not (M.World) := ⟨not_def⟩

lemma imp_def : x ⊧ p ⟶ q ↔ (x ⊧ p) → (x ⊧ q) := by tauto;
instance : Semantics.Imp (M.World) := ⟨imp_def⟩

lemma or_def : x ⊧ p ⋎ q ↔ x ⊧ p ∨ x ⊧ q := by simp [Satisfies]; tauto;
instance : Semantics.Or (M.World) := ⟨or_def⟩

lemma and_def : x ⊧ p ⋏ q ↔ x ⊧ p ∧ x ⊧ q := by simp [Satisfies];
instance : Semantics.And (M.World) := ⟨and_def⟩

instance : Semantics.Tarski M.World where
  realize_top := by simp [PLoN.Satisfies];
  realize_bot := by simp [PLoN.Satisfies];

end Formula.PLoN.Satisfies


def Formula.PLoN.ValidOnModel (M : PLoN.Model α) (p : Formula α) : Prop := ∀ w : M.World, w ⊧ p

namespace Formula.PLoN.ValidOnModel

instance : Semantics (Formula α) (PLoN.Model α) := ⟨fun M ↦ Formula.PLoN.ValidOnModel M⟩

@[simp]
protected lemma iff_models {M : PLoN.Model α} {p : Formula α}
: M ⊧ p ↔ Formula.PLoN.ValidOnModel M p := by rfl

instance : Semantics.Bot (PLoN.Model α) where
  realize_bot _ := by
    simp [Formula.PLoN.ValidOnModel];
    use ﹫;

variable {M : PLoN.Model α}

protected lemma imply₁ : M ⊧ (Axioms.Imply₁ p q) := by simp [ValidOnModel]; tauto;

protected lemma imply₂ : M ⊧ (Axioms.Imply₂ p q r) := by simp [ValidOnModel]; tauto;

protected lemma elim_contra : M ⊧ (Axioms.ElimContra p q) := by simp [ValidOnModel]; tauto;

end Formula.PLoN.ValidOnModel


def Formula.PLoN.ValidOnFrame (F : PLoN.Frame α) (p : Formula α) := ∀ V, (Model.mk F V) ⊧ p

namespace Formula.PLoN.ValidOnFrame

instance : Semantics (Formula α) (PLoN.Frame α) := ⟨fun F ↦ Formula.PLoN.ValidOnFrame F⟩

@[simp]
protected lemma iff_models {F : PLoN.Frame α} {p : Formula α}
: F ⊧ p ↔ Formula.PLoN.ValidOnFrame F p := by rfl

variable {F : Frame α}

instance : Semantics.Bot (PLoN.Frame α) where
  realize_bot _ := by simp [Formula.PLoN.ValidOnFrame];

protected lemma nec (h : F ⊧ p) : F ⊧ □p := by
  intro V x y _;
  exact h V y;

protected lemma mdp (hpq : F ⊧ p ⟶ q) (hp : F ⊧ p) : F ⊧ q := by
  intro V x;
  exact (hpq V x) (hp V x);

protected lemma imply₁ : F ⊧ (Axioms.Imply₁ p q) := by simp [ValidOnFrame]; tauto;

protected lemma imply₂ : F ⊧ (Axioms.Imply₂ p q r) := by simp [ValidOnFrame]; tauto;

protected lemma elim_contra : F ⊧ (Axioms.ElimContra p q) := by intro V; exact ValidOnModel.elim_contra;

end Formula.PLoN.ValidOnFrame


def Formula.PLoN.ValidOnFrameClass (𝔽 : PLoN.FrameClass α) (p : Formula α) := ∀ {F}, F ∈ 𝔽 → F ⊧ p

namespace Formula.PLoN.ValidOnFrameClass

instance : Semantics (Formula α) (PLoN.FrameClass α) := ⟨fun 𝔽 ↦ Formula.PLoN.ValidOnFrameClass 𝔽⟩

variable {𝔽 : FrameClass α}

@[simp]
protected lemma iff_models {𝔽 : PLoN.FrameClass α} {p : Formula α} : 𝔽 ⊧ p ↔ Formula.PLoN.ValidOnFrameClass 𝔽 p := by rfl

protected lemma nec (h : 𝔽 ⊧ p) : 𝔽 ⊧ □p := by
  intro _ hF;
  apply PLoN.ValidOnFrame.nec;
  exact h hF;

protected lemma mdp (hpq : 𝔽 ⊧ p ⟶ q) (hp : 𝔽 ⊧ p) : 𝔽 ⊧ q := by
  intro _ hF;
  exact PLoN.ValidOnFrame.mdp (hpq hF) (hp hF)

protected lemma imply₁ : 𝔽 ⊧ (Axioms.Imply₁ p q) := by intro _ _; exact PLoN.ValidOnFrame.imply₁;

protected lemma imply₂ : 𝔽 ⊧ (Axioms.Imply₂ p q r) := by intro _ _; exact PLoN.ValidOnFrame.imply₂;

protected lemma elim_contra : 𝔽 ⊧ (Axioms.ElimContra p q) := by intro _ _; exact PLoN.ValidOnFrame.elim_contra;

end Formula.PLoN.ValidOnFrameClass


def DeductionParameter.CharacterizedByPLoNFrameClass (𝓓 : DeductionParameter α) (𝔽 : PLoN.FrameClass α) := ∀ {F : Frame α}, F ∈ 𝔽 → F ⊧* 𝓓.theory

-- MEMO: `←`方向は成り立たない可能性がある
def DeductionParameter.DefinesPLoNFrameClass (𝓓 : DeductionParameter α) (𝔽 : PLoN.FrameClass α) := ∀ {F : Frame α}, F ⊧* 𝓓.theory ↔ F ∈ 𝔽

namespace PLoN

open Formula.PLoN

abbrev AllFrameClass (α) : FrameClass α := Set.univ

lemma AllFrameClass.nonempty : (AllFrameClass.{_, 0} α).Nonempty := by
  use terminalFrame α
  trivial;

open Formula

lemma N_characterized : 𝐍.CharacterizedByPLoNFrameClass (AllFrameClass α) := by
  intro F;
  simp [DeductionParameter.theory, System.theory, PLoN.ValidOnFrame, PLoN.ValidOnModel];
  intro p hp;
  induction hp using Deduction.inducition_with_necOnly! with
  | hMaxm h => simp at h;
  | hMdp ihpq ihp =>
    intro V w;
    exact (ihpq V w) (ihp V w)
  | hNec ihp =>
    intro V w w' _;
    exact ihp V w';
  | _ =>
    simp_all [PLoN.Satisfies];
    try tauto;


namespace Frame

variable (F : Frame α)

def SerialOnFormula (p : Formula α) : Prop := Serial (F.Rel' p)

def SerialOnTheory (T : Theory α) : Prop := ∀ p ∈ T, F.SerialOnFormula p

protected def Serial : Prop := ∀ p, F.SerialOnFormula p


def TransitiveOnFormula (p : Formula α) : Prop := ∀ {x y z : F.World}, x ≺[□p] y → y ≺[p] z → x ≺[p] z

def TransitiveOnTheory (T : Theory α) : Prop := ∀ p ∈ T, F.SerialOnFormula p

protected def Transitive (F : Frame α) := ∀ p, F.TransitiveOnFormula p

end Frame


open System

lemma validRosserRule_of_serial {p : Formula α} {F : PLoN.Frame α} (hSerial : F.SerialOnFormula p) (h : F ⊧ ~p) : F ⊧ ~(□p) := by
  intro V x;
  obtain ⟨y, hy⟩ := hSerial x;
  simp [Formula.PLoN.Satisfies];
  use y, hy;
  exact h V y;

lemma validAxiomFour_of_transitive {p : Formula α} {F : PLoN.Frame α} (hTrans : F.TransitiveOnFormula p) : F ⊧ Axioms.Four p := by
  dsimp [Axioms.Four];
  intro V x h y rxy z ryz;
  exact h (hTrans rxy ryz);


abbrev TransitiveFrameClass (α) : PLoN.FrameClass α := { F | Frame.Transitive F }

lemma TransitiveFrameClass.nonempty : (TransitiveFrameClass.{_, 0} α).Nonempty := by
  use terminalFrame α;
  simp [Frame.Transitive, Frame.TransitiveOnFormula];


abbrev SerialFrameClass (α) : PLoN.FrameClass α := { F | Frame.Serial F }

lemma SerialFrameClass.nonempty : (SerialFrameClass.{_, 0} α).Nonempty := by
  use terminalFrame α;
  intro p x; use x;


abbrev TransitiveSerialFrameClass (α) : PLoN.FrameClass α := { F | F.Transitive ∧ F.Serial }

lemma TransitiveSerialFrameClass.nonempty : (TransitiveSerialFrameClass.{_, 0} α).Nonempty := by
  use terminalFrame α;
  simp [Frame.Transitive, Frame.Serial, Frame.TransitiveOnFormula, Frame.SerialOnFormula];
  intro p x; use x;


lemma N4_characterized : 𝐍𝟒.CharacterizedByPLoNFrameClass (TransitiveFrameClass α) := by
  intro F;
  simp [DeductionParameter.theory, System.theory, PLoN.ValidOnFrame, PLoN.ValidOnModel];
  intro hTrans p hp;
  induction hp using Deduction.inducition_with_necOnly! with
  | hMaxm h =>
    obtain ⟨p, e⟩ := h; subst e;
    exact validAxiomFour_of_transitive (hTrans p);
  | hMdp ihpq ihp => exact PLoN.ValidOnFrame.mdp ihpq ihp;
  | hNec ihp => exact PLoN.ValidOnFrame.nec ihp;
  | hOrElim => exact PLoN.ValidOnFrame.disj₃;
  | _ => simp_all [PLoN.Satisfies];

lemma NRosser_characterized : 𝐍(𝐑).CharacterizedByPLoNFrameClass (SerialFrameClass α) := by
  intro F;
  simp [DeductionParameter.theory, System.theory, PLoN.ValidOnFrame, PLoN.ValidOnModel];
  intro hSerial p hp;
  induction hp using Deduction.inducition! with
  | hMaxm h => simp at h;
  | hMdp ihpq ihp => exact PLoN.ValidOnFrame.mdp ihpq ihp;
  | hRules rl hrl hant ih =>
    rcases hrl with (hNec | hRosser)
    . obtain ⟨p, e⟩ := hNec; subst e; simp_all;
      exact PLoN.ValidOnFrame.nec ih;
    . obtain ⟨p, e⟩ := hRosser; subst e; simp_all;
      exact validRosserRule_of_serial (hSerial _) ih;
  | hOrElim => exact PLoN.ValidOnFrame.disj₃;
  | _ => simp_all [PLoN.Satisfies];

-- TODO: `theory 𝐍𝟒 ∪ theory 𝐍(𝐑) = theory 𝐍𝟒(𝐑)`という事実を示せば共通部分だけで簡単に特徴づけられる気がする
lemma N4Rosser_characterized : 𝐍𝟒(𝐑).CharacterizedByPLoNFrameClass (TransitiveSerialFrameClass α) := by
  intro F;
  simp [DeductionParameter.theory, System.theory, PLoN.ValidOnFrame, PLoN.ValidOnModel];
  intro hTrans hSerial p hp;
  induction hp using Deduction.inducition! with
  | hMaxm h =>
    obtain ⟨p, e⟩ := h; subst e;
    exact validAxiomFour_of_transitive (hTrans p);
  | hMdp ihpq ihp => exact PLoN.ValidOnFrame.mdp ihpq ihp;
  | hRules rl hrl hant ih =>
    rcases hrl with (hNec | hRosser)
    . obtain ⟨p, e⟩ := hNec; subst e; simp_all;
      exact PLoN.ValidOnFrame.nec ih;
    . obtain ⟨p, e⟩ := hRosser; subst e; simp_all;
      exact validRosserRule_of_serial (hSerial _) ih;
  | hOrElim => exact PLoN.ValidOnFrame.disj₃;
  | _ => simp_all [PLoN.Satisfies];

end PLoN

end LO.Modal.Standard
