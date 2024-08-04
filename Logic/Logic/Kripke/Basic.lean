import Logic.Logic.Kripke.RelItr
import Logic.Logic.Semantics
import Logic.Logic.System
import Logic.Vorspiel.BinaryRelations

universe u v
-- set_option autoImplicit false

namespace LO.Kripke

structure Frame where
  World : Type u
  Rel : Rel World World
  [World_nonempty : Nonempty World]

instance : CoeSort Frame (Type u) := ⟨Frame.World⟩
instance : CoeFun Frame (λ F => F.World → F.World → Prop) := ⟨Frame.Rel⟩

instance {F : Frame} : Nonempty F.World := F.World_nonempty

abbrev Frame.Rel' {F : Frame} (x y : F.World) := F.Rel x y
scoped infix:45 " ≺ " => Frame.Rel'

protected abbrev Frame.RelItr' {F : Frame} (n : ℕ) := F.Rel.iterate n
scoped notation x:45 " ≺^[" n "] " y:46 => Frame.RelItr' n x y

-- TODO: `Rel.iterate`上で示せるはず
namespace Frame.RelItr'

lemma congr {F : Frame} {x y : F.World} {n m : ℕ} (h : x ≺^[n] y) (he : n = m := by omega) : x ≺^[m] y := by
  subst_vars; exact h;

lemma forward {F : Frame} {x y : F.World} : x ≺^[n + 1] y ↔ ∃ z, x ≺^[n] z ∧ z ≺ y := Rel.iterate.forward

lemma comp {F : Frame} {x y : F.World} {n m : ℕ} : (∃ z, x ≺^[n] z ∧ z ≺^[m] y) ↔ x ≺^[n + m] y := by
  constructor;
  . rintro ⟨z, hzx, hzy⟩;
    induction n generalizing x with
    | zero => simp_all;
    | succ n ih =>
      suffices x ≺^[(n + m + 1)] y by apply congr this;
      obtain ⟨w, hxw, hwz⟩ := hzx;
      use w;
      constructor;
      . exact hxw;
      . exact @ih w hwz;
  . rintro h;
    induction n generalizing x with
    | zero => simp_all;
    | succ n ih =>
      have rxy : x ≺^[n + m + 1] y := congr h;
      obtain ⟨w, rxw, rwy⟩ := rxy;
      obtain ⟨u, rwu, ruy⟩ := @ih w rwy;
      use u;
      constructor;
      . use w;
      . assumption;

lemma comp' {F : Frame} {x y : F.World} {n m : ℕ+} : (∃ z, x ≺^[n] z ∧ z ≺^[m] y) ↔ x ≺^[n + m] y := comp

end Frame.RelItr'


noncomputable abbrev Frame.default {F : Frame} : F.World := Classical.choice F.World_nonempty
notation "﹫" => Frame.default


set_option linter.unusedVariables false in
abbrev Frame.Dep (α : Type v) := Frame.{u}

abbrev Frame.alt (F : Frame.{u}) (α : Type v) : Frame.Dep α := F
notation F:max "#" α:max => Frame.alt F α


structure FiniteFrame extends Frame where
  [World_finite : Finite World]

instance {F : FiniteFrame} : Finite (F.World) := F.World_finite
instance : Coe (FiniteFrame) (Frame) := ⟨λ F ↦ F.toFrame⟩


open Relation (ReflTransGen TransGen)


abbrev Frame.RelReflTransGen {F : Frame} : _root_.Rel F.World F.World:= ReflTransGen (· ≺ ·)
scoped infix:45 " ≺^* " => Frame.RelReflTransGen

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
postfix:max "^*" => Frame.TransitiveReflexiveClosure

namespace Frame.TransitiveReflexiveClosure

variable {F : Frame}

lemma single {x y : F.World} (hxy : x ≺ y) : F^*.Rel x y := ReflTransGen.single hxy

lemma rel_reflexive : Reflexive F^*.Rel := by intro x; exact ReflTransGen.refl;

lemma rel_transitive : Transitive F^*.Rel := by simp;

lemma rel_symmetric : Symmetric F.Rel → Symmetric F^* := ReflTransGen.symmetric

end Frame.TransitiveReflexiveClosure



abbrev Frame.RelTransGen {F : Frame} : _root_.Rel F.World F.World := TransGen (· ≺ ·)
scoped infix:45 " ≺^+ " => Frame.RelTransGen

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
scoped postfix:max "^+" => Frame.TransitiveClosure

namespace Frame.TransitiveClosure

variable {F : Frame}

lemma single {x y : F.World} (hxy : x ≺ y) : F^+ x y := TransGen.single hxy

lemma rel_transitive : Transitive F^+ := by simp;

lemma rel_symmetric (hSymm : Symmetric F.Rel) : Symmetric F.TransitiveClosure := by simp_all

end Frame.TransitiveClosure


abbrev FrameClass := Set (Frame)

set_option linter.unusedVariables false in
abbrev FrameClass.Dep (α : Type v) := FrameClass.{u}

abbrev FrameClass.alt (𝔽 : FrameClass) (α) : FrameClass.Dep α := 𝔽
notation 𝔽:max "#" α:max => FrameClass.alt 𝔽 α


abbrev FiniteFrameClass := Set (FiniteFrame)

@[simp] def FiniteFrameClass.toFrameClass (𝔽 : FiniteFrameClass) : FrameClass := { F | ∃ F', F' ∈ 𝔽 ∧ F'.toFrame = F }
instance : Coe (FiniteFrameClass) (FrameClass) := ⟨FiniteFrameClass.toFrameClass⟩

@[simp] def FrameClass.toFiniteFrameClass (𝔽 : FrameClass) : FiniteFrameClass := { F | F.toFrame ∈ 𝔽 }
instance : Coe (FrameClass) (FiniteFrameClass) := ⟨FrameClass.toFiniteFrameClass⟩

@[simp] abbrev FrameClass.restrictFinite (𝔽 : FrameClass) : FrameClass := FiniteFrameClass.toFrameClass ↑𝔽
postfix:max "ꟳ" => FrameClass.restrictFinite

lemma FrameClass.iff_mem_restrictFinite {𝔽 : FrameClass} {F : Frame} (h : F ∈ 𝔽) (F_finite : Finite F.World) : F ∈ 𝔽ꟳ := by
  simp;
  use { toFrame := F, World_finite := F_finite };


section

/-- FrameClass for `𝐊` -/
abbrev AllFrameClass : FrameClass := Set.univ

/-- FrameClass for `𝐈𝐧𝐭` and `𝐒𝟒` -/
abbrev ReflexiveTransitiveFrameClass : FrameClass := λ F => Reflexive F ∧ Transitive F

/-- FrameClass for `𝐊𝐂` and `𝐒𝟒.𝟐` -/
abbrev ReflexiveTransitiveConfluentFrameClass : FrameClass := λ F => Reflexive F ∧ Transitive F ∧ Confluent F

/-- FrameClass for `𝐋𝐂` and `𝐒𝟒.𝟑` -/
abbrev ReflexiveTransitiveConnectedFrameClass : FrameClass := λ F => Reflexive F ∧ Transitive F ∧ Connected F

/-- FrameClass for `𝐂𝐥` and `𝐊𝐓𝟒𝐁` (`𝐒𝟓`) -/
abbrev ReflexiveTransitiveSymmetricFrameClass : FrameClass := λ F => Reflexive F ∧ Transitive F ∧ Symmetric F

end

/-- `𝔽₁` is characterized by `𝔽₂` -/
class FrameClass.Characteraizable (𝔽₁ : FrameClass) (𝔽₂ : outParam (FrameClass)) where
  characterize : ∀ {F}, F ∈ 𝔽₂ → F ∈ 𝔽₁
  nonempty : 𝔽₂.Nonempty

class FrameClass.DefinedBy (𝔽₁ : FrameClass) (𝔽₂ : outParam (FrameClass)) where
  define : ∀ {F}, F ∈ 𝔽₁ ↔ F ∈ 𝔽₂
  nonempty : 𝔽₂.Nonempty

instance {𝔽₁ 𝔽₂ : FrameClass} [defines : 𝔽₁.DefinedBy 𝔽₂] : FrameClass.Characteraizable 𝔽₁ 𝔽₂ where
  characterize hF := defines.define.mpr hF
  nonempty := defines.nonempty

abbrev Valuation (F : Frame) (α : Type*) := F.World → α → Prop

abbrev Valuation.atomic_hereditary (V : Valuation F α) : Prop := ∀ {w₁ w₂ : F.World}, (w₁ ≺ w₂) → ∀ {a}, (V w₁ a) → (V w₂ a)


structure Model (α) where
  Frame : Frame
  Valuation : Valuation Frame α

abbrev Model.World (M : Model α) := M.Frame.World
instance : CoeSort (Model α) (Type u) := ⟨Model.World⟩


section Classical

abbrev ClassicalFrame : Kripke.Frame where
  World := Unit
  Rel _ _ := True

namespace ClassicalFrame

@[simp] lemma transitive : Transitive ClassicalFrame := by simp [Transitive];

@[simp] lemma reflexive : Reflexive ClassicalFrame := by simp [Reflexive];

@[simp] lemma euclidean : Euclidean ClassicalFrame := by simp [Euclidean];

@[simp] lemma symmetric : Symmetric ClassicalFrame := by simp [Symmetric];

@[simp] lemma extensive : Extensive ClassicalFrame := by simp [Extensive];

@[simp] lemma universal : Universal ClassicalFrame := by simp [Universal];

end ClassicalFrame

abbrev ClassicalValuation (α : Type*) := α → Prop

abbrev ClassicalModel (V : ClassicalValuation α) : Kripke.Model α where
  Frame := ClassicalFrame
  Valuation _ a := V a

end Classical


/-- Frame with single world and identiy relation -/
abbrev terminalFrame : FiniteFrame where
  World := Unit;
  Rel := λ _ _ => True

@[simp]
lemma terminalFrame.iff_rel' {x y : terminalFrame.World} : x ≺ y ↔ x = y := by
  simp [Frame.Rel'];

@[simp]
lemma terminalFrame.iff_relItr' {x y : terminalFrame.World} : x ≺^[n] y ↔ x = y := by
  induction n with
  | zero => simp;
  | succ n ih => simp_all;



abbrev PointFrame : FiniteFrame where
  World := Unit
  Rel := (λ _ _ => False)

@[simp]
lemma PointFrame.iff_rel' {x y : PointFrame.World} : ¬(x ≺ y) := by simp [Frame.Rel'];


end LO.Kripke
