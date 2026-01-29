module

public import Foundation.Modal.Formula.Basic
public import Foundation.Modal.Logic.Basic
public import Foundation.Modal.Algebra.Basic
public import Foundation.Modal.Kripke.Basic
public import Foundation.Modal.Kripke.Algebra
public import Foundation.Vorspiel.Set.Cofinite

@[expose] public section

namespace LO.Modal

variable {α : Type*}

namespace General

protected structure Frame where
  World : Type*
  [world_nonempty : Nonempty World]
  Rel : _root_.Rel World World
  Pos : Set (Set World)
  [pos_ma : ModalAlgebra Pos]
  pos_box_def (A : Pos) : □A = { x | ∀ y, Rel x y → y ∈ A.1 }

namespace Frame

variable {F : General.Frame}

instance : Nonempty F.World := F.world_nonempty
instance : ModalAlgebra F.Pos := F.pos_ma
instance : CoeSort General.Frame Type* := ⟨Frame.World⟩

abbrev Rel' := F.Rel
infix:45 " ≺ " => Frame.Rel'

end Frame

protected structure Model (α) extends General.Frame where
  Val : α → Pos

namespace Model

@[grind]
def truthset (M : General.Model α) : Modal.Formula α → M.Pos
  | .atom p => M.Val p
  | ⊥ => ⊥
  | φ ➝ ψ => (M.truthset φ) ⇨ (M.truthset ψ)
  | □φ => □(M.truthset φ)

instance : CoeFun (General.Model α) (λ M => Formula α → M.Pos) := ⟨λ M => truthset M⟩

variable {M : General.Model α} {a : α} {φ ψ : Formula α}

@[grind =] lemma eq_atom   : M (.atom a) = M.Val a := rfl
@[grind =] lemma eq_falsum : M ⊥ = ⊥ := rfl
@[grind =] lemma eq_imply  : M (φ ➝ ψ) = M φ ⇨ M ψ := rfl
@[grind =] lemma eq_and    : M (φ ⋏ ψ) = M φ ⊓ M ψ := by simp [truthset];
@[grind =] lemma eq_or     : M (φ ⋎ ψ) = M φ ⊔ M ψ := by simp [truthset, BooleanAlgebra.himp_eq, sup_comm];
@[grind =] lemma eq_neg    : M (∼φ) = ￢(M φ) := by simp only [truthset, himp_bot, hnot_eq_compl];
@[grind =] lemma eq_verum  : M ⊤ = ⊤ := by simp [truthset];
@[grind =] lemma eq_box    : M (□φ) = □(M φ) := rfl
@[grind =] lemma eq_dia    : M (◇φ) = ◇(M φ) := by simp [ModalAlgebra.dual_dia, truthset];

/-
@[grind =]
lemma iff_mem_neg_truthset_not_mem_truthset {x : M.World} : x ∈ (M.truthset (∼φ) : Set M.World) ↔ x ∉ (M.truthset φ : Set M.World) := by
  simp [eq_neg];
  constructor;
  . intro h;
    sorry;
  . intro h;
    sorry;

@[simp, grind =] lemma def_box : M (□φ) = { x : M.World | ∀ y, x ≺ y → y ∈ (M φ).1 } := by
  rw [eq_box, M.pos_box_def];

@[simp, grind =] lemma def_dia : M (◇φ) = { x : M.World | ∃ y, x ≺ y ∧ y ∈ (M φ).1 } := by
  ext x;
  have := (Set.ext_iff.mp $ def_box (M := M) (φ := ∼φ)) x |>.not;
  rw [←iff_mem_neg_truthset_not_mem_truthset] at this;
  grind;
-/

end Model

end General


namespace Formula.General

def Forces {M : General.Model α} (x : M.World) (φ : Formula α) := x ∈ (M.truthset φ).1

def ValidOnModel (M : General.Model α) (φ : Formula α) := ∀ x : M.World, Forces x φ

def ValidOnFrame (F : General.Frame) (φ : Formula α) := ∀ V, ValidOnModel ⟨F, V⟩ φ

end Formula.General


section vB

abbrev General.VB : General.Frame :=
  let W := ℕ ⊕ Fin 2;
  let R : Rel W W := λ x y =>
      match x, y with
      | .inl n, .inl m => n > m
      | .inr 1, .inr 0
      | .inr 0, .inr 0
      | .inr 0, .inl _ => True
      | _, _ => False;
  let P : Set (Set W) := λ X => (X.Finite ∧ (.inr 0 ∉ X)) ∨ (X.Cofinite ∧ (.inr 0) ∈ X);
  haveI : BooleanAlgebra P := {
    top := ⟨Set.univ, by right; grind⟩,
    bot := ⟨∅, by left; grind⟩,
    inf := λ A B => ⟨A.1 ∩ B.1, by
      rcases A with ⟨A, (⟨hA₁, hA₂⟩ | ⟨hA₁, hA₂⟩)⟩ <;>
      rcases B with ⟨B, (⟨hB₁, hB₂⟩ | ⟨hB₁, hB₂⟩)⟩;
      case inr.inr => right; grind;
      all_goals
      . left; grind [Set.Finite.inter_of_left, Set.Finite.inter_of_right]
    ⟩
    sup := λ A B => ⟨A.1 ∪ B.1, by
      rcases A with ⟨A, (⟨hA₁, hA₂⟩ | ⟨hA₁, hA₂⟩)⟩ <;>
      rcases B with ⟨B, (⟨hB₁, hB₂⟩ | ⟨hB₁, hB₂⟩)⟩;
      case inl.inl =>
        left;
        constructor;
        . apply Set.Finite.union hA₁ hB₁
        . grind;
      all_goals
      . right; grind;
    ⟩
    compl := λ A => ⟨A.1ᶜ, by
      rcases A with ⟨A, (⟨hA₁, hA₂⟩ | ⟨hA₁, hA₂⟩)⟩;
      . right; grind;
      . left; grind;
    ⟩,

    le_top := by intro A x; simp,
    bot_le := by intro A x h; simp at h;
    inf_le_left := by intro A B x; grind;
    inf_le_right := by intro A B x; grind;
    le_sup_left := by intro A B x; grind;
    le_sup_right := by intro A B x; grind;
    sup_le := by
      rintro A B C hAB hAC x (hA | hB);
      . apply hAB hA;
      . apply hAC hB;
    le_inf := by
      intro A B C hAB hAC x hxA;
      simp_all [@hAB x hxA, @hAC x hxA];
    le_sup_inf := by
      rintro A B C x ⟨(_ | _), (_ | _)⟩;
      . left; assumption;
      . left; assumption;
      . left; assumption;
      . right; constructor <;> assumption;
    inf_compl_le_bot := by
      rintro A x ⟨_, _⟩;
      grind;
    top_le_sup_compl := by
      rintro A x _;
      by_cases hA : x ∈ A.1;
      . left; assumption;
      . right; assumption;
  }
  haveI : ModalAlgebra P := by sorry;
  {
    World := W,
    Rel := R,
    Pos := P,
    pos_box_def := by sorry
  }


end vB


end LO.Modal

end
