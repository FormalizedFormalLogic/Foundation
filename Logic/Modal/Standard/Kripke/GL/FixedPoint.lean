import Logic.Modal.Standard.Kripke.GL.Tree

namespace LO.Modal.Standard

variable [Inhabited α] [DecidableEq α]

open System
open Classical
open Formula (atom)
open Formula.Kripke (Satisfies)
open Formula.Kripke.Satisfies
open Kripke Kripke.FiniteTransitiveTreeModel Kripke.FiniteTransitiveTree


namespace Formula

def boxed₀ (a : α) (f : Prop) : Formula α → Prop
  | atom b => if a = b then f else True
  | □p     => p.boxed₀ a True
  | p ⋏ q  => p.boxed₀ a f ∧ q.boxed₀ a f
  | p ⋎ q  => p.boxed₀ a f ∧ q.boxed₀ a f
  | p ⟶ q  => p.boxed₀ a f ∧ q.boxed₀ a f
  | ~p     => p.boxed₀ a f
  | ⊤      => True
  | ⊥      => True

abbrev boxed (a : α) : Formula α → Prop := boxed₀ a false

variable {a : α} {p q : Formula α}

lemma boxed_atom (a : α) : ¬((atom a).boxed a) := by simp [boxed₀]
lemma boxed_box (a : α) : (□(atom a)).boxed a := by simp [boxed, boxed₀]
lemma iff_atom_boxed {a b : α} : (atom b).boxed a ↔ a ≠ b := by simp [boxed₀]

@[simp] lemma boxed_and : (p ⋏ q).boxed a → p.boxed a ∧ q.boxed a := by simp [boxed, boxed₀];
@[simp] lemma boxed_or : (p ⋎ q).boxed a → p.boxed a ∧ q.boxed a := by simp [boxed, boxed₀];
@[simp] lemma boxed_imply : (p ⟶ q).boxed a → p.boxed a ∧ q.boxed a := by simp [boxed, boxed₀];


section Substitution

variable [DecidableEq α]

def subst (p : Formula α) (a : α) (t : Formula α) : Formula α :=
  match p with
  | ⊥ => ⊥
  | ⊤ => ⊤
  | atom b => if b = a then t else atom b
  | ~p => ~(p.subst a t)
  | p ⋏ q => (p.subst a t) ⋏ (q.subst a t)
  | p ⋎ q => (p.subst a t) ⋎ (q.subst a t)
  | p ⟶ q => (p.subst a t)  ⟶ (q.subst a t)
  | box p => □(p.subst a t)

end Substitution


end Formula


namespace Formula.Kripke.Satisfies

variable {M : Kripke.Model α} {x : M.World} {p q : Formula α}

lemma imp_def_notor : x ⊧ p ⟶ q ↔ x ⊧ ~p ⋎ q := by simp [Satisfies, imp_iff_not_or]

lemma iff_def : Satisfies M x (p ⟷ q) ↔ (Satisfies M x p ↔ Satisfies M x q) := by
  simp [Satisfies];
  aesop;

private lemma satisfies_lemma₁ : ~(Satisfies M x (p₁ ⟶ p₂)) ↔ (Satisfies M x (p₁ ⋏ ~p₂)) := by simp [Satisfies];

private lemma satisfies_lemma₂ : ¬(Satisfies M x (p₁ ⟶ p₂ ⟶ p₃)) ↔ (Satisfies M x (p₁ ⋏ p₂ ⋏ ~p₃)) := by simp [Satisfies];

end Formula.Kripke.Satisfies

namespace Kripke


variable {a : α} {p f : Formula α}

private lemma boxdot_lemma (h : 𝐆𝐋 ⊢! ⊡p ⟶ (□f ⟶ f)) : 𝐆𝐋 ⊢! ⊡p ⟶ ⊡f := by
  have := imply_box_box_of_imply_boxdot_axiomT! h;
  have := GL_imply_boxdot_plain_of_imply_box_box this;
  exact imply_boxdot_boxdot_of_imply_boxdot_plain! this;

@[simp]
lemma FiniteTransitiveTree.not_root_from_not_root {F : FiniteTransitiveTree} {x y : F.World} (hnr : x ≠ F.root) (Rxy : x ≺ y) : y ≠ F.root := by
  by_contra hC; subst_vars;
  have := F.rel_assymetric Rxy;
  have := F.root_rooted x hnr;
  contradiction;


lemma goldfarb_lemma
  (hp : p.boxed a) (hq : a ∉ 𝒜 f)
  : 𝐆𝐋 ⊢! ⊡((atom a) ⟷ p) ⟶ ((atom a) ⟷ f) → 𝐆𝐋 ⊢! ⊡((atom a) ⟷ f) ⟷ ⊡((atom a) ⟷ p) := by
  suffices 𝐆𝐋 ⊢! ⊡((atom a) ⟷ p) ⟶ ((atom a) ⟷ f) → 𝐆𝐋 ⊢! ⊡((atom a) ⟷ f) ⟶ (□((atom a) ⟷ p) ⟶ ((atom a) ⟷ p)) by
    intro h;
    exact and₃'! (boxdot_lemma (this h)) (imply_boxdot_boxdot_of_imply_boxdot_plain! h);
  contrapose;
  intro H;
  obtain ⟨M, hs⟩ := iff_unprovable_GL_exists_unsatisfies_at_root_on_FiniteTransitiveTree.mp H;
  replace hs : M.root ⊧ ⊡(atom a ⟷ f) ⋏ □(atom a ⟷ p) ⋏ ~(atom a ⟷ p) := satisfies_lemma₂.mp hs;

  let M' : FiniteTransitiveTreeModel α := ⟨M.Tree,
    λ w b => if w = M.root ∧ b = atom a then ¬(M.Valuation w b) else M.Valuation w b
  ⟩;

  apply iff_unprovable_GL_exists_unsatisfies_at_root_on_FiniteTransitiveTree.mpr;
  use M';
  apply satisfies_lemma₁.mpr;

  have h₁ : ∀ p₂, ∀ x ≠ M.root, Satisfies M.toModel x p₂ ↔ Satisfies M'.toModel x p₂ := by
    intro p₂ x hx;
    induction p₂ using Formula.rec' generalizing x with
    | hbox p ih =>
      simp [Satisfies];
      constructor;
      . intro h y Rxy; exact @ih y (not_root_from_not_root hx Rxy) |>.mp $ h Rxy;
      . intro h y Rxy; exact @ih y (not_root_from_not_root hx Rxy) |>.mpr $ h Rxy;
    | hatom => simp_all [Satisfies];
    | _ => simp_all only [Formula.mem_atoms_iff_mem_subformulae, ne_eq, Satisfies, not_false_eq_true];
  have h₂ : ∀ p₂, a ∉ 𝒜 p₂ → (Satisfies M.toModel M.root p₂ ↔ Satisfies M'.toModel M.root p₂) := by
    intro p₂ hA;
    induction p₂ using Formula.rec' with
    | hbox p ih =>
      simp [Satisfies];
      constructor;
      . intro h y Rxy;
        apply @h₁ p y (by sorry) |>.mp;
        apply h Rxy;
      . intro h y Rxy;
        apply @h₁ p y (by sorry) |>.mpr;
        apply h Rxy;
    | hatom => sorry; -- simp_all [Satisfies, Formula.Subformulas]; split <;> simp_all;
    | _ => sorry; -- simp_all [Satisfies, Formula.Subformulas];
  have h₃ : Satisfies M.toModel M.root p ↔ Satisfies M'.toModel M'.root p := by
    induction p using Formula.rec' with
    | hverum => simp [Satisfies];
    | hfalsum => simp [Satisfies];
    | hatom b =>
      have := Formula.iff_atom_boxed.mp hp;
      apply h₂;
      simp_all [Formula.atom, Formula.Subformulas]
    | hand p₁ p₂ ih₁ ih₂ =>
      sorry;
      -- apply h₂;
      -- have ⟨hp₁, hp₂⟩ := Formula.boxed_and hp;
      -- replace ih₁ := ih₁ hp₁ (by sorry) (by sorry);
      -- replace ih₂ := ih₂ hp₂ (by sorry) (by sorry);
      -- constructor;
      -- . rintro ⟨hs₁, hs₂⟩; exact ⟨ih₁.mp hs₁, ih₂.mp hs₂⟩;
      -- . rintro ⟨hs₁, hs₂⟩; exact ⟨ih₁.mpr hs₁, ih₂.mpr hs₂⟩;
    | hor p₁ p₂ ih₁ ih₂ =>
      sorry;
      /-
      have ⟨hp₁, hp₂⟩ := Formula.boxed_or hp;
      replace ih₁ := ih₁ hp₁ (by sorry) (by sorry);
      replace ih₂ := ih₂ hp₂ (by sorry) (by sorry);
      constructor;
      . rintro (hs₁ | hs₂);
        . left; apply ih₁.mp hs₁;
        . right; apply ih₂.mp hs₂;
      . rintro (hs₁ | hs₂);
        . left; apply ih₁.mpr hs₁;
        . right; apply ih₂.mpr hs₂;
      -/
    | himp p₁ p₂ ih₁ ih₂ =>
      sorry;
      /-
      have ⟨hp₁, hp₂⟩ := Formula.boxed_imply hp;
      replace ih₁ := ih₁ hp₁ (by sorry) (by sorry);
      replace ih₂ := ih₂ hp₂ (by sorry) (by sorry);
      constructor;
      . rintro h h₁; exact ih₂.mp $ h $ ih₁.mpr h₁;
      . rintro h h₁; exact ih₂.mpr $ h $ ih₁.mp h₁;
      -/
    | hneg p ih =>
      sorry;
      -- apply h₂;
    | hbox p =>
      constructor;
      . intro h x Rx;
        apply h₁ p x (by sorry) |>.mp;
        apply h Rx;
      . intro h x Rx;
        apply h₁ p x (by sorry) |>.mpr;
        apply h Rx;

  refine ⟨⟨?_, ?_⟩, ?_⟩;
  . apply Satisfies.iff_def.mpr;
    simp [Satisfies];
    sorry;
  . intro x Rx;
    simp [Satisfies];
    sorry;
  . sorry;

lemma GL_existance_fixpoint (hp : p.boxed a) : ∃ f, 𝒜 f ⊆ (𝒜 p) \ {a} ∧ 𝐆𝐋 ⊢! f ⟷ (p.subst a f) := by sorry;

lemma GL_uniqueness_fixpoint {a b} (hp : p.boxed a) (hq : b ∉ 𝒜 p)
  : 𝐆𝐋 ⊢! (⊡((atom a) ⟷ p) ⋏ ⊡((atom b) ⟷ p.subst a (atom b))) ⟶ ((atom a) ⟷ (atom b)) := by sorry;

-- TODO: move
lemma remove_and_right! (hpq : 𝐆𝐋 ⊢! p ⋏ q ⟶ r) (hp : 𝐆𝐋 ⊢! p) : 𝐆𝐋 ⊢! q ⟶ r := and_imply_iff_imply_imply'!.mp hpq ⨀ hp

-- TODO: move
lemma remove_and_left! (hpq : 𝐆𝐋 ⊢! p ⋏ q ⟶ r) (hq : 𝐆𝐋 ⊢! q) : 𝐆𝐋 ⊢! p ⟶ r := by
  apply remove_and_right! (p := q) (q := p);
  . exact imply_left_and_comm'! hpq;
  . exact hq;

/--
  Sambin's fixpoint theorem of `𝐆𝐋`
-/
theorem GL_fixpoint_theorem
  (hp : p.boxed a)
  (hp_atom : ∃ b, b ∉ 𝒜 p)
  : ∃ f, 𝒜 f ⊆ (𝒜 p) \ {a} ∧ 𝐆𝐋 ⊢! ⊡(atom a ⟷ p) ⟷ ⊡(atom a ⟷ f) := by
  obtain ⟨f, _, hf⟩ := GL_existance_fixpoint hp;
  use f;
  constructor;
  . assumption;
  . obtain ⟨b, hb⟩ := hp_atom;
    have := @GL_uniqueness_fixpoint α _ p a b hp hb;
    have : 𝐆𝐋 ⊢! ⊡(atom a ⟷ p) ⋏ ⊡(f ⟷ p.subst a f) ⟶ atom a ⟷ f := by sorry;
    have : 𝐆𝐋 ⊢! ⊡(atom a ⟷ p) ⟶ atom a ⟷ f := remove_and_left! this $ boxdot_nec! hf;
    exact iff_comm'! $ goldfarb_lemma hp (by sorry) this;

end Kripke

end LO.Modal.Standard
