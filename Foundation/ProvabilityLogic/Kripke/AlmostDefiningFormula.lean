module

public import Foundation.ProvabilityLogic.Kripke.DefiningFormula
public import Foundation.ProvabilityLogic.Kripke.Graft
public import Foundation.ProvabilityLogic.Kripke.Tail
public import Foundation.ProvabilityLogic.S.Basic

/-!
# Almost defining formulas

## References

- [Bek90, §4 Lemma 4, Lemma 9, Remark 1, Remark 2]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Formula Kripke Kripke.Model Kripke.Model.World

variable {κ κ' α : Type*} [Nonempty κ] [Nonempty κ']

namespace Kripke

namespace Model

section Modalized

variable {K K' : Model κ α} {r : κ} (hR : K.Rel' = K'.Rel') (hr : ∀ x, ¬K.Rel' x r)
  (hV : ∀ x ≠ r, ∀ a, K.Val x a ↔ K'.Val x a)
include hR hr hV

lemma forces_congr_of_ne {z : κ} (hz : z ≠ r) {C : Formula α} : z ⊩[K] C ↔ z ⊩[K'] C := by
  induction C generalizing z with
  | atom a => exact hV z hz a;
  | falsum => rfl;
  | imp A B ihA ihB => exact imp_congr (ihA hz) (ihB hz);
  | box A ih =>
    change (∀ y, K.Rel' z y → _) ↔ (∀ y, K'.Rel' z y → _);
    rw [← hR];
    exact forall_congr' fun y ↦ imp_congr_right fun R ↦ ih fun h ↦ hr z (h ▸ R);

lemma forces_congr_of_modalized {C : Formula α} (hC : C.Modalized) : r ⊩[K] C ↔ r ⊩[K'] C := by
  induction C with
  | atom a => exact (hC a rfl).elim;
  | falsum => rfl;
  | imp A B ihA ihB => exact imp_congr (ihA fun p ↦ (hC p).1) (ihB fun p ↦ (hC p).2);
  | box A =>
    change (∀ y, K.Rel' r y → _) ↔ (∀ y, K'.Rel' r y → _);
    rw [← hR];
    exact forall_congr' fun y ↦ imp_congr_right fun R ↦
      forces_congr_of_ne hR hr hV fun h ↦ hr r <| by subst h; exact R;

end Modalized

section Depth

variable {M : Model κ α} {x : M.World} {m n : ℕ}

lemma forces_boxItr_succ {A : Formula α} :
    x ⊩[M] □^[n + 1]A ↔ ∀ y, x ≺ y → y ⊩[M] □^[n]A := by
  rw [boxItr_succ, forces_box];

lemma forces_boxItr_bot_of_le (hmn : m ≤ n) (h : x ⊩[M] □^[m]⊥) : x ⊩[M] □^[n]⊥ := by
  induction m generalizing x n with
  | zero => exact absurd h not_forces_bot;
  | succ m ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one.mpr (show 0 < n by omega);
    exact forces_boxItr_succ.mpr fun y R ↦ ih (by omega) (forces_boxItr_succ.mp h y R);

lemma exists_depth_of_forces_boxItr_bot (h : x ⊩[M] □^[n]⊥) :
    ∃ m, x ⊮[M] □^[m]⊥ ∧ x ⊩[M] □^[m + 1]⊥ := by
  induction n with
  | zero => exact absurd h not_forces_bot;
  | succ n ih =>
    by_cases hn : x ⊩[M] □^[n]⊥;
    · exact ih hn;
    · exact ⟨n, hn, h⟩;

lemma exists_rel_depth [M.IsGL] (h : x ⊮[M] □^[n + 1]⊥) :
    ∃ y, x ≺ y ∧ y ⊮[M] □^[n]⊥ ∧ y ⊩[M] □^[n + 1]⊥ := by
  obtain ⟨y, Rxy, hy⟩ := not_forces_box.mp fun h' ↦ h (forces_boxItr_succ.mpr h');
  obtain ⟨t, ⟨Rxt, ht⟩, hmax⟩ := M.terminalOf {y | x ≺ y ∧ y ⊮[M] □^[n]⊥} ⟨y, Rxy, hy⟩;
  exact ⟨t, Rxt, ht, forces_boxItr_succ.mpr fun z Rtz ↦
    by_contra fun hz ↦ hmax z ⟨IsTrans.trans _ _ _ Rxt Rtz, hz⟩ Rtz⟩;

end Depth

end Model

namespace RootedModel

lemma graft.exists_forces_boxItr_bot {N : RootedModel κ α} [N.IsFiniteGL] {a : N.NonRoot}
    {z : (N.graft a ℕ).World} (hz : z ≠ (N.graft a ℕ).root) :
    ∃ n, z ⊩[(N.graft a ℕ).toModel] □^[n]⊥ := by
  have : Fintype N.World := Fintype.ofFinite _;
  have h₁ : ∀ k x, x ≠ N.root → x ⊩[N.toModel] □^[k]⊥ →
      Sum.inl x ⊩[(N.graft a ℕ).toModel] □^[k]⊥ := by
    intro k;
    induction k with
    | zero => exact fun _ _ h ↦ absurd h not_forces_bot;
    | succ k ih =>
      rintro x hx h;
      apply forces_boxItr_succ.mpr;
      rintro (y | i) R;
      · exact ih y (fun h ↦ not_rel_root (h ▸ R)) (forces_boxItr_succ.mp h y R);
      · exact absurd R hx;
  have h₂ : ∀ x, x ≠ N.root → Sum.inl x ⊩[(N.graft a ℕ).toModel] □^[N.height + 1]⊥ :=
    fun x hx ↦ h₁ _ x hx <| forces_boxItr_bot_iff.mpr <| Nat.lt_add_one_of_le rank_le_height;
  have h₃ : ∀ i : ℕ, Sum.inr i ⊩[(N.graft a ℕ).toModel] □^[i + N.height + 2]⊥ := by
    intro i;
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      apply forces_boxItr_succ.mpr;
      rintro (y | j) R;
      · apply forces_boxItr_bot_of_le (by omega) (h₂ y _);
        rcases R with rfl | R;
        exacts [a.2, fun h ↦ not_rel_root (h ▸ R)];
      · exact forces_boxItr_bot_of_le (by grind) (ih j R);
  rcases z with x | i;
  · exact ⟨_, h₂ x fun h ↦ hz (h ▸ rfl)⟩;
  · exact ⟨_, h₃ i⟩;

variable [DecidableEq α] (P : Finset α) (M : RootedModel κ α) [Fintype M.World] [M.IsGL]

open Classical in
/-- The almost defining formula of `M` over `P`.

- [Bek90, §4 Remark 1]
-/
noncomputable def almostDefiningFormula : Formula α :=
  □(∼□^[M.height + 1]⊥ 🡒
    ◇charFormulaUnder (M := M.toModel) P M.root ⋏ valuationConj (M := M.toModel) P M.root) ⋏
  □(□^[M.height + 1]⊥ 🡒 (Finset.univ.image fun y : M.World ↦ y.charFormulaUnder P).disj)

variable {P M}

section Use

variable {K : RootedModel κ' α} (hΦ : K.root ⊩[K.toModel] almostDefiningFormula P M)
  {z : K.World}
include hΦ

lemma forces_dia_and_valuationConj_of_forces_almostDefiningFormula (hz : K.Rel K.root z)
    (h : z ⊮[K.toModel] □^[M.height + 1]⊥) :
    z ⊩[K.toModel]
      ◇charFormulaUnder (M := M.toModel) P M.root ⋏ valuationConj (M := M.toModel) P M.root :=
  (forces_and.mp hΦ).1 z hz h

lemma exists_forces_charFormulaUnder_of_forces_boxItr (hz : K.Rel K.root z)
    (h : z ⊩[K.toModel] □^[M.height + 1]⊥) :
    ∃ y : M.World, z ⊩[K.toModel] y.charFormulaUnder P := by
  obtain ⟨_, hB, hzB⟩ := forces_disj.mp <| (forces_and.mp hΦ).2 z hz h;
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hB;
  exact ⟨y, hzB⟩;

lemma exists_rel_forces_charFormulaUnder [K.IsGL] (hz : K.Rel K.root z)
    (h : z ⊮[K.toModel] □^[M.height + 1]⊥) (x : M.World) :
    ∃ z', K.Rel z z' ∧ z' ⊩[K.toModel] x.charFormulaUnder P := by
  obtain ⟨z₀, R₀, h₀⟩ := forces_dia.mp <|
    (forces_and.mp <| forces_dia_and_valuationConj_of_forces_almostDefiningFormula hΦ hz h).1;
  by_cases hx : x = M.root;
  · exact ⟨z₀, R₀, hx ▸ h₀⟩;
  · obtain ⟨z', R', h'⟩ := (forces_charFormulaUnder_iff.mp h₀).2.1 x (M.root_rel x hx);
    exact ⟨z', IsTrans.trans _ _ _ R₀ R', h'⟩;

lemma exists_root_rel_forces_charFormulaUnder [K.IsGL]
    (hr : K.root ⊮[K.toModel] □^[M.height + 2]⊥)
    (x : M.World) : ∃ z', K.Rel K.root z' ∧ z' ⊩[K.toModel] x.charFormulaUnder P := by
  obtain ⟨y, Ry, hy, -⟩ := exists_rel_depth hr;
  obtain ⟨z', R', h'⟩ := exists_rel_forces_charFormulaUnder hΦ Ry hy x;
  exact ⟨z', IsTrans.trans _ _ _ Ry R', h'⟩;

end Use

lemma atoms_almostDefiningFormula : (almostDefiningFormula P M).atoms ⊆ P := by
  sorry

lemma modalized_almostDefiningFormula : (almostDefiningFormula P M).Modalized := by
  sorry

lemma pseudoTail_forces_almostDefiningFormula (o : α → Prop) :
    Sum.inr ⊤ ⊩[(M.toPseudoTail o).toModel] almostDefiningFormula P M := by
  sorry

/-- If the root of a rooted GL-model `K` without depth, all of whose other points have a depth,
forces the almost defining formula of `M` and agrees with `o` on `P`, then it is `P`-bisimilar to
the root of the pseudo-tail of `M` with root valuation `o`.

- [Bek90, §4 Lemma 9, Remark 2]
-/
theorem exists_bisimulation_of_forces_almostDefiningFormula {K : RootedModel κ' α} [K.IsGL]
    (hr : ∀ n, K.root ⊮[K.toModel] □^[n]⊥)
    (hK : ∀ z ≠ K.root, ∃ n, z ⊩[K.toModel] □^[n]⊥)
    (hΦ : K.root ⊩[K.toModel] almostDefiningFormula P M) {o : α → Prop}
    (ho : ∀ a ∈ P, (o a ↔ K.Val K.root a)) :
    ∃ Bi : (M.toPseudoTail o).toModel ⇄[P] K.toModel, Bi (.inr ⊤) K.root := by
  sorry

end RootedModel

end Kripke

/-- A modalized formula forced at the root of a free tail is not refuted by `𝐒`.

- [Bek90, §4 Lemma 4]
-/
theorem Logic.S.not_provable_neg_of_forces_freeTail {M : Model κ α} [M.IsGL] {V : ℕ∞ → α → Prop}
    {C : Formula α} (hC : C.Modalized) (h : Sum.inr ⊤ ⊩[(M.toFreeTail V).toModel] C) :
    𝐒 ⊬ ∼C := by
  sorry

end FFL.ProvabilityLogic

end
