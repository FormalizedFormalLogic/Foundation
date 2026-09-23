module

public import Foundation.ProvabilityLogic.Kripke.Cone
public import Foundation.ProvabilityLogic.Kripke.Unravelling

/-!
# `P`-simplification of Kripke models

## References

- [Bek90, §4, Lemma 6, Lemma 8]
-/

@[expose] public section

namespace FFL.ProvabilityLogic.Kripke

open Model Model.World

universe u

variable {κ α : Type*} [Nonempty κ]

namespace RootedModel

variable {M : RootedModel κ α} {P : Finset α}

/-- `a` is `P`-redundant if every predecessor of `a` sees a point incomparable with `a` whose
cone is `P`-bisimilar to that of `a`.

- [Bek90, §4]
-/
def Redundant (M : RootedModel κ α) (P : Finset α) (a : M.NonRoot) : Prop :=
  ∀ x, x ≺ a.1 → ∃ (y : M.World) (Bi : M.toModel ⇄[P] M.toModel),
    x ≺ y ∧ y ⊀ a.1 ∧ a.1 ⊀ y ∧ y ≠ a.1 ∧ Bi y a.1

/-- - [Bek90, §4] -/
def IsSimpleUnder (M : RootedModel κ α) (P : Finset α) : Prop := ∀ a, ¬M.Redundant P a

section

variable [IsTrans _ M.Rel] [Std.Irrefl M.Rel]

/-- - [Bek90, Lemma 1] -/
lemma Redundant.insert_of_root_forces_box [DecidableEq α] {p : α} {a : M.NonRoot}
    (h : M.Redundant P a) (hp : M.root ⊩[M.toModel] □#p) : M.Redundant (insert p P) a := by
  intro x R;
  obtain ⟨y, Bi, Rxy, h₁, h₂, h₃, hy⟩ := h x R;
  let Bi' : M.toModel ⇄[insert p P] M.toModel := {
    toRel u v := Bi u v ∧ u ≠ M.root ∧ v ≠ M.root
    atomic := by
      rintro u v q hq ⟨h, hu, hv⟩;
      rcases Finset.mem_insert.mp hq with rfl | hq;
      . exact iff_of_true (hp u (M.root_rel u hu)) (hp v (M.root_rel v hv));
      . exact Bi.atomic hq h;
    forth := by
      rintro u u' v ⟨h, -, -⟩ R;
      obtain ⟨v', h', R'⟩ := Bi.forth h R;
      exact ⟨v', ⟨h', fun e ↦ not_rel_root (e ▸ R), fun e ↦ not_rel_root (e ▸ R')⟩, R'⟩;
    back := by
      rintro u v v' ⟨h, -, -⟩ R;
      obtain ⟨u', h', R'⟩ := Bi.back h R;
      exact ⟨u', ⟨h', fun e ↦ not_rel_root (e ▸ R'), fun e ↦ not_rel_root (e ▸ R)⟩, R'⟩;
  };
  exact ⟨y, Bi', Rxy, h₁, h₂, h₃, hy, by rintro rfl; exact not_rel_root Rxy, a.2⟩;

/-- - [Bek90, Lemma 1] -/
lemma IsSimpleUnder.of_insert_of_root_forces_box [DecidableEq α] {p : α}
    (h : M.IsSimpleUnder (insert p P)) (hp : M.root ⊩[M.toModel] □#p) : M.IsSimpleUnder P :=
  fun a ha ↦ h a (ha.insert_of_root_forces_box hp)

lemma not_root_isInConeOf (a : M.NonRoot) : ¬IsInConeOf (M := M.toModel) M.root a.1 := by
  rintro (h | h);
  . exact a.2 h.symm;
  . exact not_rel_root h;

instance (a : M.NonRoot) : Nonempty { x : M.World // ¬x.IsInConeOf a.1 } :=
  ⟨⟨M.root, not_root_isInConeOf a⟩⟩

/-- `M` without the cone above `a`.

- [Bek90, §4]
-/
def removeCone (M : RootedModel κ α) [IsTrans _ M.Rel] [Std.Irrefl M.Rel] (a : M.NonRoot) :
    RootedModel { x : M.World // ¬x.IsInConeOf a.1 } α where
  Rel' x y := x.1 ≺ y.1
  Val' x := M.Val x.1
  root := ⟨M.root, not_root_isInConeOf a⟩
  root_rel x hx := M.root_rel x.1 fun h ↦ hx (Subtype.ext h)

namespace removeCone

variable {a : M.NonRoot}

instance : IsTrans _ (M.removeCone a).Rel := ⟨fun x y z ↦ IsTrans.trans (r := M.Rel) x.1 y.1 z.1⟩

instance : Std.Irrefl (M.removeCone a).Rel := ⟨fun x ↦ Std.Irrefl.irrefl (r := M.Rel) x.1⟩

instance [M.IsTree] : (M.removeCone a).IsTree where
  tree h₁ h₂ := by
    rcases IsTree.tree (M := M.toModel) h₁ h₂ with h | h | h;
    . exact .inl (Subtype.ext h);
    . exact .inr (.inl h);
    . exact .inr (.inr h);

instance [Finite M.World] : (M.removeCone a).IsFiniteGL where
  finite := Subtype.finite

lemma card_lt [Fintype M.World] [Fintype (M.removeCone a).World] :
    Fintype.card (M.removeCone a).World < Fintype.card M.World :=
  Fintype.card_subtype_lt (p := fun x : M.World ↦ ¬x.IsInConeOf a.1) (x := a.1)
    (by simp [IsInConeOf])

/-- Removing the cone above a `P`-redundant point of a tree preserves the forcing of formulas
in `P`.

- [Bek90, Lemma 6]
-/
theorem forces_iff [DecidableEq α] [M.IsTree] (hred : M.Redundant P a) {C : Formula α}
    (hC : C.atoms ⊆ P) (x : (M.removeCone a).World) :
    x ⊩[(M.removeCone a).toModel] C ↔ x.1 ⊩[M.toModel] C := by
  induction C generalizing x with
  | atom | falsum => rfl;
  | imp B C ihB ihC => exact imp_congr (ihB (by grind) x) (ihC (by grind) x);
  | box B ih =>
    replace hC : B.atoms ⊆ P := hC;
    obtain ⟨x, hx⟩ := x;
    constructor;
    . intro h z Rxz;
      by_cases hz : z.IsInConeOf a.1;
      . have Rxa : x ≺ a.1 := by
          rcases hz with rfl | Raz;
          . exact Rxz;
          . rcases IsTree.tree (M := M.toModel) Rxz Raz with rfl | h | h;
            . exact absurd (.inl rfl) hx;
            . exact h;
            . exact absurd (.inr h) hx;
        obtain ⟨y, Bi, Rxy, hya, hay, hy, hBi⟩ := hred x Rxa;
        have hy' : ¬y.IsInConeOf a.1 := by rintro (rfl | h); exacts [hy rfl, hay h];
        have haB : a.1 ⊩[M.toModel] B :=
          (Bi.forces_iff hBi hC).mp ((ih hC ⟨y, hy'⟩).mp (h ⟨y, hy'⟩ Rxy));
        rcases hz with rfl | Raz;
        . exact haB;
        . obtain ⟨z', hBi', Ryz'⟩ := Bi.back hBi Raz;
          have hz' : ¬z'.IsInConeOf a.1 := by
            rintro (rfl | Raz');
            . exact hya Ryz';
            . rcases IsTree.tree (M := M.toModel) Ryz' Raz' with h | h | h;
              . exact hy h;
              . exact hya h;
              . exact hay h;
          exact (Bi.forces_iff hBi' hC).mp
            ((ih hC ⟨z', hz'⟩).mp (h ⟨z', hz'⟩ (show x ≺ z' from IsTrans.trans _ _ _ Rxy Ryz')));
      . exact (ih hC ⟨z, hz⟩).mp (h ⟨z, hz⟩ Rxz);
    . exact fun h z Rxz ↦ (ih hC z).mpr (h z.1 Rxz);

end removeCone

end

namespace graft

variable {a : M.NonRoot}

lemma not_redundant_inr (i : ℕ) : ¬(M.graft a ℕ).Redundant P ⟨.inr i, Sum.inr_ne_inl⟩ := by
  intro hred;
  obtain ⟨u, -, R, -, hnR, hne, -⟩ := hred (.inr (i + 1)) (show i < i + 1 by omega);
  rcases u with z | j;
  . exact hnR R;
  . have : j < i + 1 := R;
    have : j ≠ i := fun h ↦ hne (by rw [h]);
    exact hnR (show j < i by omega);

lemma not_redundant_inl_a (hm : Sum.inl a.1 ≠ (M.graft a ℕ).root) :
    ¬(M.graft a ℕ).Redundant P ⟨.inl a.1, hm⟩ := by
  intro hred;
  obtain ⟨u, -, R, -, hnR, hne, -⟩ := hred (.inr 0) (.inl rfl);
  rcases u with z | j;
  . rcases R with rfl | R;
    . exact hne rfl;
    . exact hnR R;
  . exact absurd R (Nat.not_lt_zero _);

lemma exists_of_redundant {w : (M.graft a ℕ).NonRoot} (hred : (M.graft a ℕ).Redundant P w) :
    ∃ m, ∃ hm : m ≠ M.root, m ≠ a.1 ∧ w = ⟨.inl m, fun h ↦ hm (Sum.inl.inj h)⟩ := by
  obtain ⟨m | i, hw⟩ := w;
  . exact ⟨m, fun h ↦ hw (congrArg Sum.inl h),
      by rintro rfl; exact not_redundant_inl_a hw hred, rfl⟩;
  . exact absurd hred (not_redundant_inr i);

lemma isTree [M.IsTree] {ι : Type*} [LinearOrder ι] (hcov : ∀ x, x ≺ a.1 → x = M.root) :
    (M.graft a ι).IsTree where
  tree {x y z} h₁ h₂ := by
    have := M.root_rel a.1 a.2;
    have htree : ∀ {x y z : M.World}, x ≺ z → y ≺ z → x = y ∨ x ≺ y ∨ y ≺ x :=
      IsTree.tree (M := M.toModel);
    rcases x with x | i <;> rcases y with y | j <;> rcases z with z | k <;>
    simp only [rel_inl_inl, rel_inl_inr, rel_inr_inl, rel_inr_inr, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, false_or] at * <;> grind;

lemma not_isInConeOf_of_redundant (hcov : ∀ x, x ≺ a.1 → x = M.root) {m : M.World}
    (hm : m ≠ M.root) (hred : (M.graft a ℕ).Redundant P ⟨.inl m, fun h ↦ hm (Sum.inl.inj h)⟩) :
    ¬a.1.IsInConeOf m := by
  rintro (rfl | h);
  . exact not_redundant_inl_a _ hred;
  . exact hm (hcov m h);

variable [IsTrans _ M.Rel] [Std.Irrefl M.Rel]

/-- Removing a cone commutes with grafting. -/
def removeConeMap {m : M.World} (hm : m ≠ M.root) (hma : ¬a.1.IsInConeOf m) :
    ((M.graft a ℕ).removeCone ⟨.inl m, fun h ↦ hm (Sum.inl.inj h)⟩).toModel →ₚ
    ((M.removeCone ⟨m, hm⟩).graft
      ⟨⟨a.1, hma⟩, fun h ↦ a.2 (congrArg Subtype.val h)⟩ ℕ).toModel where
  toFun
    | ⟨.inl x, hx⟩ => .inl ⟨x, fun h ↦ hx (by simpa [IsInConeOf] using h)⟩
    | ⟨.inr i, _⟩ => .inr i
  forth {x y} R := by
    obtain ⟨x | i, hx⟩ := x <;> obtain ⟨y | j, hy⟩ := y;
    . exact R;
    . exact Subtype.ext R;
    . rcases R with rfl | R;
      . exact .inl rfl;
      . exact .inr R;
    . exact R;
  back {x v} h := by
    obtain ⟨x | i, hx⟩ := x <;> rcases v with ⟨y, hy⟩ | j;
    . exact ⟨⟨.inl y, fun h ↦ hy (by simpa [IsInConeOf] using h)⟩, rfl, h⟩;
    . exact ⟨⟨.inr j, by simp [IsInConeOf, hm]⟩, rfl, congrArg Subtype.val h⟩;
    . exact ⟨⟨.inl y, fun h ↦ hy (by simpa [IsInConeOf] using h)⟩, rfl,
        h.imp (congrArg Subtype.val) id⟩;
    . exact ⟨⟨.inr j, by simp [IsInConeOf, hm]⟩, rfl, h⟩;
  atomic {x} := by
    obtain ⟨x | i, hx⟩ := x <;> exact Iff.rfl;

end graft

variable [DecidableEq α]

/-- - [Bek90, Lemma 8] -/
theorem exists_simplificationUnder_graft_aux (P : Finset α) (n : ℕ) :
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [Fintype M.World] [M.IsFiniteGL] [M.IsTree]
      (a : M.NonRoot), (∀ x, x ≺ a.1 → x = M.root) → Fintype.card M.World = n →
    ∃ (κ' : Type u) (_ : Nonempty κ') (M' : RootedModel κ' α) (_ : M'.IsFiniteGL) (_ : M'.IsTree)
      (a' : M'.NonRoot), (∀ x, x ≺ a'.1 → x = M'.root) ∧
      ((∀ x, M.root ≺ x → x.IsInConeOf a.1) → ∀ x, M'.root ≺ x → x.IsInConeOf a'.1) ∧
      (M'.graft a' ℕ).IsSimpleUnder P ∧
      ∀ C : Formula α, C.atoms ⊆ P →
        ((M.graft a ℕ).root ⊩[(M.graft a ℕ).toModel] C ↔
          (M'.graft a' ℕ).root ⊩[(M'.graft a' ℕ).toModel] C) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro κ _ M _ _ _ a hcov hcard;
  have : (M.graft a ℕ).IsTree := graft.isTree hcov;
  by_cases hex : ∃ w, (M.graft a ℕ).Redundant P w;
  . obtain ⟨w, hred⟩ := hex;
    obtain ⟨m, hm, -, rfl⟩ := graft.exists_of_redundant hred;
    have hma := graft.not_isInConeOf_of_redundant hcov hm hred;
    have : Fintype (M.removeCone ⟨m, hm⟩).World := Fintype.ofFinite _;
    obtain ⟨κ', _, M', _, _, a', hcov', hlat, hsimp, heq⟩ :=
      ih _ (hcard ▸ removeCone.card_lt) (M.removeCone ⟨m, hm⟩)
        ⟨⟨a.1, hma⟩, fun h ↦ a.2 (congrArg Subtype.val h)⟩
        (fun x R ↦ Subtype.ext (hcov x.1 R)) rfl;
    use κ', inferInstance, M', inferInstance, inferInstance, a', hcov';
    and_intros;
    . intro h;
      apply hlat;
      rintro ⟨x, hx⟩ R;
      rcases h x R with rfl | h;
      . exact .inl rfl;
      . exact .inr h;
    . exact hsimp;
    . intro C hC;
      exact (removeCone.forces_iff hred hC _).symm.trans
        (((graft.removeConeMap hm hma).forces_iff
          (x := ((M.graft a ℕ).removeCone ⟨.inl m, _⟩).root)).trans (heq C hC));
  . push Not at hex;
    exact ⟨κ, inferInstance, M, inferInstance, inferInstance, a, hcov, id, hex, fun _ _ ↦ Iff.rfl⟩;

/-- A grafted model over a finite tree at a point covering the root has a `P`-simple form of
the same shape.

- [Bek90, Lemma 8]
-/
theorem exists_simplificationUnder_graft {κ : Type u} [Nonempty κ] {M : RootedModel κ α}
    [M.IsFiniteGL] [M.IsTree] {a : M.NonRoot} (hcov : ∀ x, x ≺ a.1 → x = M.root) (P : Finset α) :
    ∃ (κ' : Type u) (_ : Nonempty κ') (M' : RootedModel κ' α) (_ : M'.IsFiniteGL) (_ : M'.IsTree)
      (a' : M'.NonRoot), (∀ x, x ≺ a'.1 → x = M'.root) ∧
      ((∀ x, M.root ≺ x → x.IsInConeOf a.1) → ∀ x, M'.root ≺ x → x.IsInConeOf a'.1) ∧
      (M'.graft a' ℕ).IsSimpleUnder P ∧
      ∀ C : Formula α, C.atoms ⊆ P →
        ((M.graft a ℕ).root ⊩[(M.graft a ℕ).toModel] C ↔
          (M'.graft a' ℕ).root ⊩[(M'.graft a' ℕ).toModel] C) :=
  have : Fintype M.World := Fintype.ofFinite _;
  exists_simplificationUnder_graft_aux P _ M a hcov rfl

end RootedModel

end FFL.ProvabilityLogic.Kripke

end
