module

public import Foundation.ProvabilityLogic.Logic
public import Foundation.ProvabilityLogic.Sequent
public import Foundation.Logic.Semantics
public import Foundation.Vorspiel.Rel.WCWF

/-!
# Kripke semantics

Kripke models and forcing, overwriting the valuation of a model, the Kripke soundness of normal
logics, and the forcing of sequents.
-/

@[expose] public section

namespace FFL.ProvabilityLogic

namespace Kripke

structure Model (κ : Type*) [Nonempty κ] (α : Type*) where
  Rel' : κ → κ → Prop
  Val' : κ → α → Prop

namespace Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α}

abbrev World (_ : Model κ α) := κ

abbrev Rel {M : Model κ α} : M.World → M.World → Prop := M.Rel'
scoped infix:60 " ≺ " => Rel

@[grind]
def RelItr : ℕ → M.World → M.World → Prop
  |     0 => (· = ·)
  | n + 1 => fun x y ↦ ∃ z, x ≺ z ∧ RelItr n z y

scoped notation x:45 " ≺^[" n:0 "] " y:46 => RelItr n x y

section RelItr

variable {x y : M.World} {n : ℕ}

@[simp, grind =]
lemma relItr_zero : x ≺^[0] y ↔ x = y := Iff.rfl

@[simp, grind =]
lemma relItr_one : x ≺^[1] y ↔ x ≺ y := by simp [RelItr];

@[grind =]
lemma relItr_succ : x ≺^[n + 1] y ↔ ∃ z, x ≺ z ∧ z ≺^[n] y := Iff.rfl

abbrev NotRel {M : Model κ α} : M.World → M.World → Prop := fun x y => ¬(x ≺ y)
scoped infix:60 " ⊀ " => NotRel

abbrev NotRelItr {M : Model κ α} (n : ℕ) : M.World → M.World → Prop := fun x y => ¬(x ≺^[n] y)
scoped notation x:45 " ⊀^[" n:0 "] " y:46 => NotRelItr n x y

@[simp, grind =]
lemma notRelItr_iff : x ⊀^[n] y ↔ ¬x ≺^[n] y := Iff.rfl

end RelItr

abbrev Val {M : Model κ α} : M.World → α → Prop := M.Val'

instance : CoeFun (Model κ α) (fun M ↦ M.World → α → Prop) := ⟨fun M ↦ M.Val⟩

class IsGL (M : Model κ α) extends IsTrans _ M.Rel, IsConverseWellFounded _ M.Rel

class IsFiniteGL (M : Model κ α) extends IsTrans _ M.Rel, Std.Irrefl M.Rel where
  [finite : Finite M.World]

instance [M.IsFiniteGL] : Finite M.World := IsFiniteGL.finite

instance [M.IsFiniteGL] : M.IsGL where

instance [M.IsGL] : Std.Irrefl M.Rel := ConverseWellFounded.irrefl

class IsGrz (M : Model κ α) extends
    Std.Refl M.Rel, IsTrans _ M.Rel, IsWeaklyConverseWellFounded _ M.Rel

class IsFiniteGrz (M : Model κ α) extends Std.Refl M.Rel, IsTrans _ M.Rel, Std.Antisymm M.Rel where
  [finite : Finite M.World]

instance [M.IsFiniteGrz] : Finite M.World := IsFiniteGrz.finite

instance [M.IsFiniteGrz] : M.IsGrz where

abbrev pointModel (v : α → Prop) : Model (Fin 1) α where
  Rel' _ _ := False
  Val' _ := v

instance (v : α → Prop) : (pointModel v).IsFiniteGL where
  trans := by tauto;
  irrefl := by tauto;

noncomputable def terminalOf (M : Model κ α) [IsConverseWellFounded _ M.Rel] (X : Set M.World)
    (hX : X.Nonempty) :
    { t // t ∈ X ∧ ∀ x ∈ X, t ⊀ x } :=
  have h := ConverseWellFounded.iff_has_max.mp IsConverseWellFounded.cwf X hX;
  ⟨h.choose, h.choose_spec⟩

end Model

namespace Model.World

open Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {x : M.World} {A B : Formula α} {n : ℕ}

@[grind]
def Forces (M : Model κ α) (x : M.World) : Formula α → Prop
  | #a    => M x a
  | ⊥     => False
  | A 🡒 B => Forces M x A → Forces M x B
  | □A    => ∀ y, x ≺ y → Forces M y A

scoped notation:55 x:56 " ⊩[" M "] " A:56 => Forces M x A

scoped notation:55 x:56 " ⊮[" M "] " A:56 => ¬Forces M x A

scoped notation:55 x:56 " ⊩ " A:56 => Forces _ x A

scoped notation:55 x:56 " ⊮ " A:56 => ¬Forces _ x A

@[simp, grind =] lemma forces_atom {a : α} : x ⊩ #a ↔ M x a := Iff.rfl
@[simp, grind .] lemma not_forces_bot : x ⊮ ⊥ := id
@[simp, grind .] lemma forces_top : x ⊩ ⊤ := id
@[grind =] lemma forces_imp : x ⊩ A 🡒 B ↔ x ⊮ A ∨ x ⊩ B := imp_iff_not_or
@[grind =] lemma forces_and : x ⊩ A ⋏ B ↔ x ⊩ A ∧ x ⊩ B := by
  change ((_ → _ → False) → False) ↔ _; tauto;
@[grind =] lemma forces_or : x ⊩ A ⋎ B ↔ x ⊩ A ∨ x ⊩ B := by
  change ((_ → False) → _) ↔ _; tauto;
@[grind =] lemma forces_neg : x ⊩ ∼A ↔ x ⊮ A := Iff.rfl
@[grind =] lemma forces_iff : x ⊩ A 🡘 B ↔ (x ⊩ A ↔ x ⊩ B) := by
  simp only [LogicalConnective.iff, forces_and]; grind;
@[grind =] lemma forces_box : x ⊩ □A ↔ ∀ y, x ≺ y → y ⊩ A := Iff.rfl
@[grind =] lemma forces_boxdot : x ⊩ ⊡A ↔ x ⊩ A ∧ ∀ y, x ≺ y → y ⊩ A := forces_and
@[grind =] lemma forces_dia : x ⊩ ◇A ↔ ∃ y, x ≺ y ∧ y ⊩ A := by
  change ((∀ y, x ≺ y → y ⊩ A → False) → False) ↔ _; grind;

@[grind =] lemma not_forces_imp : x ⊮ A 🡒 B ↔ x ⊩ A ∧ x ⊮ B := by grind;
@[grind =] lemma not_forces_box : x ⊮ □A ↔ ∃ y, x ≺ y ∧ y ⊮ A := by grind;

@[grind =]
lemma forces_boxItr : x ⊩ □^[n]A ↔ ∀ y, x ≺^[n] y → y ⊩ A := by
  induction n generalizing x <;> grind;

section boxItr_bot

variable {m : ℕ}

lemma forces_boxItr_succ : x ⊩ □^[n + 1]A ↔ ∀ y, x ≺ y → y ⊩ □^[n]A :=
  Formula.boxItr_succ ▸ forces_box

lemma forces_boxItr_bot_of_le (hmn : m ≤ n) (h : x ⊩ □^[m]⊥) : x ⊩ □^[n]⊥ := by
  induction m generalizing x n with
  | zero => exact absurd h not_forces_bot;
  | succ m ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one.mpr (show 0 < n by omega);
    exact forces_boxItr_succ.mpr fun y R ↦ ih (by omega) (forces_boxItr_succ.mp h y R);

lemma not_forces_boxItr_bot_of_le (hmn : m ≤ n) (h : x ⊮ □^[n]⊥) : x ⊮ □^[m]⊥ :=
  fun h' ↦ h (forces_boxItr_bot_of_le hmn h')

lemma exists_depth_of_forces_boxItr_bot (h : x ⊩ □^[n]⊥) :
    ∃ m, x ⊮ □^[m]⊥ ∧ x ⊩ □^[m + 1]⊥ := by
  induction n with
  | zero => exact absurd h not_forces_bot;
  | succ n ih =>
    by_cases hn : x ⊩ □^[n]⊥;
    · exact ih hn;
    · exact ⟨n, hn, h⟩;

lemma exists_rel_depth [M.IsGL] (h : x ⊮ □^[n + 1]⊥) :
    ∃ y, x ≺ y ∧ y ⊮ □^[n]⊥ ∧ y ⊩ □^[n + 1]⊥ := by
  obtain ⟨y, Rxy, hy⟩ := not_forces_box.mp fun h' ↦ h (forces_boxItr_succ.mpr h');
  obtain ⟨t, ⟨Rxt, ht⟩, hmax⟩ := M.terminalOf {y | x ≺ y ∧ y ⊮ □^[n]⊥} ⟨y, Rxy, hy⟩;
  exact ⟨t, Rxt, ht, forces_boxItr_succ.mpr fun z Rtz ↦
    by_contra fun hz ↦ hmax z ⟨IsTrans.trans _ _ _ Rxt Rtz, hz⟩ Rtz⟩;

end boxItr_bot

lemma forces_conj₂ : {l : List (Formula α)} → (x ⊩ ⋀l ↔ ∀ B ∈ l, x ⊩ B)
  | [] => by simp
  | [B] => by simp
  | B :: C :: l => by simp [forces_and, forces_conj₂ (l := C :: l)]

@[simp]
lemma forces_conj {Γ : FormulaFinset α} : x ⊩ Γ.conj ↔ ∀ B ∈ Γ, x ⊩ B := by
  simp [Finset.conj, forces_conj₂];

lemma forces_disj₂ : {l : List (Formula α)} → (x ⊩ ⋁l ↔ ∃ B ∈ l, x ⊩ B)
  | [] => by simp
  | [B] => by simp
  | B :: C :: l => by simp [forces_or, forces_disj₂ (l := C :: l)]

@[simp]
lemma forces_disj {Γ : FormulaFinset α} : x ⊩ Γ.disj ↔ ∃ B ∈ Γ, x ⊩ B := by
  simp [Finset.disj, forces_disj₂];

end Model.World

namespace Model

open Formula World

variable {κ α β : Type*} [Nonempty κ]

/-- The model on the frame of `M` in which an atom `a` holds where `s a` is forced in `M`. -/
def subst (M : Model κ α) (s : Substitution β α) : Model κ β where
  Rel' := M.Rel'
  Val' x a := x ⊩[M] s a

variable {M : Model κ α} {s : Substitution β α}

lemma forces_subst {x : M.World} {A : Formula β} : x ⊩[M.subst s] A ↔ x ⊩[M] A⟦s⟧ := by
  induction A generalizing x with
  | atom | falsum => rfl;
  | imp A B ihA ihB => exact imp_congr ihA ihB;
  | box A ih => exact forall_congr' fun y ↦ imp_congr_right fun _ ↦ ih;

instance [M.IsGL] : (M.subst s).IsGL where
  toIsTrans := inferInstanceAs (IsTrans _ M.Rel)
  toIsConverseWellFounded := inferInstanceAs (IsConverseWellFounded _ M.Rel)

lemma forces_congr {N : Model κ α} (hR : M.Rel' = N.Rel') (hV : ∀ x a, M x a ↔ N x a)
    {x : M.World} {A : Formula α} : x ⊩[M] A ↔ x ⊩[N] A := by
  induction A generalizing x with
  | atom a => exact hV x a;
  | falsum => rfl;
  | imp A B ihA ihB => exact imp_congr ihA ihB;
  | box A ih =>
    change (∀ y, M.Rel' x y → _) ↔ (∀ y, N.Rel' x y → _);
    rw [hR];
    exact forall_congr' fun y ↦ imp_congr_right fun _ ↦ ih;

lemma forces_congr_of_atoms [DecidableEq α] {N : Model κ α} (hR : M.Rel' = N.Rel') {A : Formula α}
    (hV : ∀ x, ∀ a ∈ A.atoms, M x a ↔ N x a) {x : M.World} : x ⊩[M] A ↔ x ⊩[N] A := by
  induction A generalizing x with
  | atom a => exact hV x a (by simp);
  | falsum => rfl;
  | imp A B ihA ihB =>
    exact imp_congr (ihA fun x a ha ↦ hV x a (by simp [ha]))
      (ihB fun x a ha ↦ hV x a (by simp [ha]));
  | box A ih =>
    change (∀ y, M.Rel' x y → _) ↔ (∀ y, N.Rel' x y → _);
    rw [hR];
    exact forall_congr' fun y ↦ imp_congr_right fun _ ↦ ih hV;

end Model

namespace Model

variable {κ α : Type*} [Nonempty κ]

instance : Semantics (Model κ α) (Formula α) := ⟨fun M A ↦ ∀ x : M.World, World.Forces M x A⟩

lemma models_iff {M : Model κ α} {A : Formula α} : M ⊧ A ↔ ∀ x : M.World, World.Forces M x A :=
  Iff.rfl

end Model

/-! ### Overwriting the valuation -/

namespace Model

open Formula World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {V : M.World → α → Prop}

def overwrite (M : Model κ α) (V : M.World → α → Prop) : Model κ α := ⟨M.Rel', V⟩

-- Not an instance: `Finite M.World` is searched through `M.IsFiniteGL` with `M` undetermined,
-- and an instance for `M.overwrite V` makes that search diverge.
lemma overwrite.isFiniteGL [M.IsFiniteGL] : (M.overwrite V).IsFiniteGL where
  trans := IsTrans.trans (r := M.Rel)
  irrefl := Std.Irrefl.irrefl (r := M.Rel)
  finite := IsFiniteGL.finite (M := M)

lemma forces_overwrite_subst {s : Substitution α α} {x : M.World} {A : Formula α} :
    x ⊩[M.overwrite fun y a ↦ y ⊩[M] s a] A ↔ x ⊩[M] A⟦s⟧ := by
  induction A generalizing x with
  | atom | falsum => rfl;
  | imp _ _ ihA ihB => exact imp_congr ihA ihB;
  | box _ ih => exact forall_congr' fun _ ↦ imp_congr_right fun _ ↦ ih;

end Model

end Kripke

/-! ### Kripke soundness of normal logics -/

namespace Logic.normalOf

open Kripke Kripke.Model Kripke.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {𝔸 : Set (Formula α)} {A : Formula α}

theorem sound (h𝔸 : ∀ A ∈ 𝔸, M ⊧ A) (h : normalOf 𝔸 ⊢ A) : M ⊧ A := by
  intro x;
  induction h generalizing x with
  | axm hA => exact h𝔸 _ hA x;
  | mdp _ _ ih₁ ih₂ => exact ih₁ x (ih₂ x);
  | _ => grind;

end Logic.normalOf

/-! ### Forcing of sequents -/

namespace Kripke

open Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {Γ Γ' Δ Δ' : FormulaFinset α} {A B : Formula α}

def Model.World.ForcesSequent (M : Model κ α) (x : M.World) (S : Sequent α) : Prop :=
  (∀ C ∈ S.ant, x ⊩ C) → ∃ D ∈ S.suc, x ⊩ D

scoped[FFL.ProvabilityLogic.Kripke.Model.World]
  notation:55 x:56 " ⊩[" M "] " S:56 => Model.World.ForcesSequent M x S

scoped[FFL.ProvabilityLogic.Kripke.Model.World]
  notation:55 x:56 " ⊩ " S:56 => Model.World.ForcesSequent _ x S

def Model.ValidateSequent (M : Model κ α) (S : Sequent α) : Prop := ∀ x : M.World, x ⊩ S

scoped[FFL.ProvabilityLogic.Kripke.Model]
  infix:45 " ⊧ " => Model.ValidateSequent

namespace Model.World

variable {x : M.World}

@[grind .] lemma forcesSequent_axm : x ⊩ ({A} ⟹ {A}) := fun hx ↦ ⟨A, by simp, hx A (by simp)⟩

@[grind .] lemma forcesSequent_botL : x ⊩ ({⊥} ⟹ ∅) := fun hx ↦ (hx ⊥ (by simp)).elim

@[grind →]
lemma forcesSequent_wkL (h : x ⊩ (Γ ⟹ Δ)) (hΓ : Γ ⊆ Γ') : x ⊩ (Γ' ⟹ Δ) :=
  fun hx ↦ h fun C hC ↦ hx C (hΓ hC)

@[grind →]
lemma forcesSequent_wkR (h : x ⊩ (Γ ⟹ Δ)) (hΔ : Δ ⊆ Δ') : x ⊩ (Γ ⟹ Δ') :=
  fun hx ↦ (h hx).imp fun _ hD ↦ ⟨hΔ hD.1, hD.2⟩

end Model.World

section

variable [DecidableEq α]

namespace Model.World

variable {x : M.World}

@[grind →]
lemma forcesSequent_impL (h₁ : x ⊩ (Γ ⟹ insert A Δ)) (h₂ : x ⊩ (insert B Γ ⟹ Δ)) :
    x ⊩ (insert (A 🡒 B) Γ ⟹ Δ) := by
  intro hx;
  have hΓ : ∀ C ∈ Γ, x ⊩ C := fun C hC ↦ hx C (by simp [hC]);
  by_cases hA : x ⊩ A;
  · exact h₂ (by simpa [hx _ (Finset.mem_insert_self _ _) hA] using hΓ);
  · obtain ⟨D, hD, hxD⟩ := h₁ hΓ;
    grind;

@[grind →]
lemma forcesSequent_impR (h : x ⊩ (insert A Γ ⟹ insert B Δ)) :
    x ⊩ (Γ ⟹ insert (A 🡒 B) Δ) := by
  intro hx;
  by_cases hA : x ⊩ A;
  · obtain ⟨D, hD, hxD⟩ := h (by simpa [hA] using hx);
    rcases Finset.mem_insert.mp hD with rfl | hD;
    · exact ⟨A 🡒 D, by simp, fun _ ↦ hxD⟩;
    · grind;
  · exact ⟨A 🡒 B, by simp, fun h ↦ absurd h hA⟩;

@[grind →]
lemma forcesSequent_cut {Γ₁ Γ₂ Δ₁ Δ₂ : FormulaFinset α}
    (h₁ : x ⊩ (Γ₁ ⟹ insert A Δ₁)) (h₂ : x ⊩ (insert A Γ₂ ⟹ Δ₂)) :
    x ⊩ (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂) := by
  intro hx;
  obtain ⟨D, hD, hxD⟩ := h₁ fun C hC ↦ hx C (by simp [hC]);
  rcases Finset.mem_insert.mp hD with rfl | hD;
  · obtain ⟨E, hE, hxE⟩ := h₂ (by
      intro C hC;
      rcases Finset.mem_insert.mp hC with rfl | hC;
      · exact hxD;
      · exact hx C (by simp [hC]));
    exact ⟨E, by simp [hE], hxE⟩;
  · exact ⟨D, by simp [hD], hxD⟩;

end Model.World

end

namespace Model

lemma validateSequent_singleton_iff :
    M ⊧ (Γ ⟹ {A}) ↔ ∀ x : M.World, (∀ C ∈ Γ, x ⊩ C) → x ⊩ A := by
  simp [ValidateSequent, ForcesSequent];

/-! #### Soundness of the propositional rules -/

@[grind .]
lemma validateSequent_axm : M ⊧ ({A} ⟹ {A}) := fun _ ↦ forcesSequent_axm

@[grind .]
lemma validateSequent_botL : M ⊧ ({⊥} ⟹ ∅) := fun _ ↦ forcesSequent_botL

@[grind →]
lemma validateSequent_wkL (h : M ⊧ (Γ ⟹ Δ)) (hΓ : Γ ⊆ Γ') : M ⊧ (Γ' ⟹ Δ) :=
  fun x ↦ forcesSequent_wkL (h x) hΓ

@[grind →]
lemma validateSequent_wkR (h : M ⊧ (Γ ⟹ Δ)) (hΔ : Δ ⊆ Δ') : M ⊧ (Γ ⟹ Δ') :=
  fun x ↦ forcesSequent_wkR (h x) hΔ

variable [DecidableEq α]

@[grind →]
lemma validateSequent_impL (h₁ : M ⊧ (Γ ⟹ insert A Δ)) (h₂ : M ⊧ (insert B Γ ⟹ Δ)) :
    M ⊧ (insert (A 🡒 B) Γ ⟹ Δ) := fun x ↦ forcesSequent_impL (h₁ x) (h₂ x)

@[grind →]
lemma validateSequent_impR (h : M ⊧ (insert A Γ ⟹ insert B Δ)) : M ⊧ (Γ ⟹ insert (A 🡒 B) Δ) :=
  fun x ↦ forcesSequent_impR (h x)

end Model

end Kripke

end FFL.ProvabilityLogic

end
