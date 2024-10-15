import Foundation.Logic.Kripke.RelItr
import Foundation.Logic.Semantics
import Foundation.Logic.System
import Foundation.Vorspiel.BinaryRelations

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
infix:45 " ≺ " => Frame.Rel'

protected abbrev Frame.RelItr' {F : Frame} (n : ℕ) := F.Rel.iterate n
notation x:45 " ≺^[" n "] " y:46 => Frame.RelItr' n x y

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


abbrev FrameClass := Set (Frame)

set_option linter.unusedVariables false in
abbrev FrameClass.Dep (α : Type v) := FrameClass.{u}

abbrev FrameClass.alt (𝔽 : FrameClass) (α : Type v) : FrameClass.Dep.{u} α := 𝔽
notation:max 𝔽:max "#" α:max => FrameClass.alt 𝔽 α


abbrev FiniteFrameClass := Set (FiniteFrame)

set_option linter.unusedVariables false in
abbrev FiniteFrameClass.Dep (α : Type v) := FiniteFrameClass.{u}

abbrev FiniteFrameClass.alt (𝔽 : FiniteFrameClass) (α : Type v) : FiniteFrameClass.Dep.{u} α := 𝔽
notation:max 𝔽:max "#" α:max => FiniteFrameClass.alt 𝔽 α


abbrev FiniteFrameClass.toFrameClass (𝔽 : FiniteFrameClass) : FrameClass := 𝔽.image FiniteFrame.toFrame
-- instance : Coe (FiniteFrameClass) (FrameClass) := ⟨FiniteFrameClass.toFrameClass⟩

abbrev FrameClass.toFiniteFrameClass (𝔽 : FrameClass) : FiniteFrameClass := { FF | FF.toFrame ∈ 𝔽 }
postfix:max "ꟳ" => FrameClass.toFiniteFrameClass


lemma FrameClass.iff_mem_restrictFinite {𝔽 : FrameClass} {F : Frame} (h : F ∈ 𝔽) [Finite F.World] : ⟨F⟩ ∈ 𝔽ꟳ := by simpa;

section

/-- FrameClass for `𝐊` -/
abbrev AllFrameClass : FrameClass := Set.univ

/-- FrameClass for `𝐊𝐓` -/
abbrev ReflexiveFrameClass : FrameClass := { F | Reflexive F.Rel }

/-- FrameClass for `𝐊𝐃` -/
abbrev SerialFrameClass : FrameClass := { F | Serial F.Rel }

/-- FrameClass for `𝐊𝟒` -/
abbrev TransitiveFrameClass : FrameClass := { F | Transitive F.Rel }

/-- FrameClass for `𝐊𝐓𝟓` (`𝐒𝟓`) -/
abbrev ReflexiveEuclideanFrameClass : FrameClass := { F | Reflexive F.Rel ∧ Euclidean F.Rel }

/-- FrameClass for `𝐊𝐓𝐁` -/
abbrev ReflexiveSymmetricFrameClass : FrameClass := { F | Reflexive F ∧ Symmetric F }

/-- FrameClass for `𝐒𝟓` -/
abbrev UniversalFrameClass : FrameClass := { F | Universal F }

/-- FrameClass for `𝐊.𝟑` -/
abbrev ConnectedFrameClass : FrameClass := { F | Connected F }

/-- FrameClass for `𝐈𝐧𝐭` and `𝐒𝟒` -/
abbrev ReflexiveTransitiveFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F }
alias PreorderFrameClass := ReflexiveTransitiveFrameClass

/-- FrameClass for `𝐊𝐂` and `𝐒𝟒.𝟐` -/
abbrev ReflexiveTransitiveConfluentFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Confluent F }

/-- FrameClass for `𝐋𝐂` and `𝐒𝟒.𝟑` -/
abbrev ReflexiveTransitiveConnectedFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Connected F }

/-- FrameClass for `𝐂𝐥` and `𝐊𝐓𝟒𝐁` (`𝐒𝟓`) -/
abbrev ReflexiveTransitiveSymmetricFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Symmetric F }
alias EquivalenceFrameClass := ReflexiveTransitiveSymmetricFrameClass

/-- FrameClass for `𝐆𝐋` -/
abbrev TransitiveConverseWellFoundedFrameClass : FrameClass := { F | Transitive F ∧ ConverseWellFounded F }

/-- FrameClass for `𝐆𝐋` (Finite version) -/
abbrev TransitiveIrreflexiveFrameClass : FrameClass := { F | Transitive F ∧ Irreflexive F }

/-- FrameClass for `𝐆𝐫𝐳` -/
abbrev ReflexiveTransitiveWeaklyConverseWellFoundedFrameClass : FrameClass := { F | Reflexive F.Rel ∧ Transitive F ∧ WeaklyConverseWellFounded F }

/-- FrameClass for `𝐆𝐫𝐳` (Finite version) -/
abbrev ReflexiveTransitiveAntisymmetricFrameClass : FrameClass := { F | Reflexive F.Rel ∧ Transitive F ∧ Antisymmetric F }

end

/-- `𝔽₁` is characterized by `𝔽₂` -/
class FrameClass.Characteraizable (𝔽₁ : FrameClass) (𝔽₂ : outParam (FrameClass)) where
  characterize : ∀ {F}, F ∈ 𝔽₂ → F ∈ 𝔽₁
  nonempty : 𝔽₂.Nonempty

/-- `𝔽₁` is defined by `𝔽₂` -/
class FrameClass.DefinedBy (𝔽₁ : FrameClass) (𝔽₂ : outParam (FrameClass)) where
  define : ∀ {F}, F ∈ 𝔽₁ ↔ F ∈ 𝔽₂
  nonempty : 𝔽₂.Nonempty

instance {𝔽₁ 𝔽₂ : FrameClass} [defines : 𝔽₁.DefinedBy 𝔽₂] : FrameClass.Characteraizable 𝔽₁ 𝔽₂ where
  characterize hF := defines.define.mpr hF
  nonempty := defines.nonempty


class FiniteFrameClass.Characteraizable (𝔽₁ : FiniteFrameClass) (𝔽₂ : outParam (FiniteFrameClass)) where
  characterize : ∀ {F}, F ∈ 𝔽₂ → F ∈ 𝔽₁
  nonempty : 𝔽₂.Nonempty

class FiniteFrameClass.DefinedBy (𝔽₁ : FiniteFrameClass) (𝔽₂ : outParam (FiniteFrameClass)) where
  define : ∀ {F}, F ∈ 𝔽₁ ↔ F ∈ 𝔽₂
  nonempty : 𝔽₂.Nonempty

instance {𝔽₁ 𝔽₂ : FiniteFrameClass} [defines : 𝔽₁.DefinedBy 𝔽₂] : FiniteFrameClass.Characteraizable 𝔽₁ 𝔽₂ where
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
