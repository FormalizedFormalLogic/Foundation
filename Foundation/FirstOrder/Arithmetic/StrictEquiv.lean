module

public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy
public import Foundation.FirstOrder.Arithmetic.BoundedCollection

/-!
# `T`-provable strict hierarchy equivalence

`StrictEquiv T Γ s φ` witnesses that `φ` is `T`-provably equivalent to some formula in
`StrictHierarchy Γ s`, and `nonempty_strictEquiv` produces such a witness for every
`Hierarchy Γ s` formula.
-/

@[expose] public section

open LO
open LO.FirstOrder

namespace LO.FirstOrder.Arithmetic

lemma provable_iff_of_models_iff {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {n} {φ ψ : ArithmeticSemiformula Empty n}
    (h : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ) :
    T ⊢ ∀¹* (φ 🡘 ψ) := by
  apply Arithmetic.complete T _;
  intro V _ _;
  simpa [models_iff] using h V;

lemma models_iff_of_provable_iff {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {n} {φ ψ : ArithmeticSemiformula Empty n}
    (h : T ⊢ ∀¹* (φ 🡘 ψ)) (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) :
    V ⊧/e φ ↔ V ⊧/e ψ := by
  have := consequence_iff.mp (Theory.Proof.sound h) V inferInstance;
  simp only [models_iff, Semiformula.eval_allClosure] at this;
  simpa using this e;

-- Pinning `V` to `Type` keeps `simp` from stalling on an unsolved universe metavariable when the
-- result is stored unapplied.
lemma models_iff_of_provable_iff' {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {n} {φ ψ : ArithmeticSemiformula Empty n}
    (h : T ⊢ ∀¹* (φ 🡘 ψ)) :
    ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ :=
  models_iff_of_provable_iff h

structure StrictEquiv (T : ArithmeticTheory) (Γ : Polarity) (s : ℕ) {n : ℕ}
    (φ : ArithmeticSemiformula Empty n) where
  witness : ArithmeticSemiformula Empty n
  hierarchy : StrictHierarchy Γ s witness
  provable : T ⊢ ∀¹* (φ 🡘 witness)

namespace StrictEquiv

variable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {Γ : Polarity} {s : ℕ} {n : ℕ}
  {φ : ArithmeticSemiformula Empty n}

lemma iff_models (d : StrictEquiv T Γ s φ) (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T]
    (e : Fin n → V) : V ⊧/e φ ↔ V ⊧/e d.witness :=
  models_iff_of_provable_iff d.provable V e

def refl (h : StrictHierarchy Γ s φ) : StrictEquiv T Γ s φ :=
  ⟨φ, h, provable_iff_of_models_iff fun _ _ _ _ => Iff.rfl⟩

def of_iff {ψ : ArithmeticSemiformula Empty n} (h : StrictEquiv T Γ s φ)
    (hiff : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ) :
    StrictEquiv T Γ s ψ :=
  ⟨h.witness, h.hierarchy, provable_iff_of_models_iff fun V _ _ e => (hiff V e).symm.trans (h.iff_models V e)⟩

def neg (h : StrictEquiv T Γ s φ) : StrictEquiv T Γ.alt s (∼φ) :=
  ⟨∼h.witness, h.hierarchy.neg, provable_iff_of_models_iff fun V _ _ e => by simp [h.iff_models V e]⟩

def alt_up (h : StrictEquiv T Γ s φ) : StrictEquiv T Γ.alt (s + 1) φ := by
  rcases Γ with _ | _;
  . use ∀¹ (Rew.bShift ▹ h.witness);
    . exact (h.hierarchy.rew Rew.bShift).pi;
    . apply provable_iff_of_models_iff;
      intro V _ _ e;
      have : Nonempty V := ⟨0⟩;
      simp [h.iff_models V e];
  . use ∃¹ (Rew.bShift ▹ h.witness);
    . exact (h.hierarchy.rew Rew.bShift).sigma;
    . apply provable_iff_of_models_iff;
      intro V _ _ e;
      simp [h.iff_models V e];

def of_deltaZero (hp : Hierarchy 𝚺 0 φ) : StrictEquiv T Γ s φ := by
  induction s generalizing Γ with
  | zero => exact refl (StrictHierarchy.zero hp);
  | succ s ih => simpa using alt_up (ih (Γ := Γ.alt));

def exs_of_pi {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquiv T 𝚷 s φ) :
    StrictEquiv T 𝚺 (s + 1) (∃¹ φ) := by
  use ∃¹ h.witness;
  . exact h.hierarchy.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp only [Semiformula.eval_ex];
    exact exists_congr (fun x => h.iff_models V (x :> e));

def all_of_sigma {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquiv T 𝚺 s φ) :
    StrictEquiv T 𝚷 (s + 1) (∀¹ φ) := by
  use ∀¹ h.witness;
  . exact h.hierarchy.pi;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp only [Semiformula.eval_all];
    exact forall_congr' (fun x => h.iff_models V (x :> e));

end StrictEquiv

open StrictEquiv (refl neg alt_up of_deltaZero exs_of_pi all_of_sigma)

structure Closure (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] (s : ℕ) : Prop where
  ball : ∀ Γ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → Nonempty (StrictEquiv T Γ s φ) →
        Nonempty (StrictEquiv T Γ s (∀¹[“x. x < !!t”] φ))
  bexs : ∀ Γ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → Nonempty (StrictEquiv T Γ s φ) →
        Nonempty (StrictEquiv T Γ s (∃¹[“x. x < !!t”] φ))
  and : ∀ Γ {n} {φ ψ : ArithmeticSemiformula Empty n},
      Nonempty (StrictEquiv T Γ s φ) → Nonempty (StrictEquiv T Γ s ψ) →
        Nonempty (StrictEquiv T Γ s (φ ⋏ ψ))
  or : ∀ Γ {n} {φ ψ : ArithmeticSemiformula Empty n},
      Nonempty (StrictEquiv T Γ s φ) → Nonempty (StrictEquiv T Γ s ψ) →
        Nonempty (StrictEquiv T Γ s (φ ⋎ ψ))

variable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {s : ℕ}

lemma closure_zero : Closure T 0 where
  ball := by
    rintro Γ n φ t ht ⟨hφ⟩;
    exact ⟨∀¹[“x. x < !!t”] hφ.witness,
      StrictHierarchy.zero (Hierarchy.ball ht (StrictHierarchy.zero_iff.mp hφ.hierarchy)),
      provable_iff_of_models_iff fun V _ _ e => by
        simp only [Semiformula.eval_ball];
        exact forall_congr' (fun x => imp_congr Iff.rfl (hφ.iff_models V (x :> e)))⟩
  bexs := by
    rintro Γ n φ t ht ⟨hφ⟩;
    exact ⟨∃¹[“x. x < !!t”] hφ.witness,
      StrictHierarchy.zero (Hierarchy.bexs ht (StrictHierarchy.zero_iff.mp hφ.hierarchy)),
      provable_iff_of_models_iff fun V _ _ e => by
        simp only [Semiformula.eval_bexs];
        exact exists_congr (fun x => and_congr Iff.rfl (hφ.iff_models V (x :> e)))⟩
  and := by
    rintro Γ n φ ψ ⟨hφ⟩ ⟨hψ⟩;
    exact ⟨hφ.witness ⋏ hψ.witness,
      StrictHierarchy.zero
        (Hierarchy.and (StrictHierarchy.zero_iff.mp hφ.hierarchy) (StrictHierarchy.zero_iff.mp hψ.hierarchy)),
      provable_iff_of_models_iff fun V _ _ e => by simp [hφ.iff_models V e, hψ.iff_models V e]⟩
  or := by
    rintro Γ n φ ψ ⟨hφ⟩ ⟨hψ⟩;
    exact ⟨hφ.witness ⋎ hψ.witness,
      StrictHierarchy.zero
        (Hierarchy.or (StrictHierarchy.zero_iff.mp hφ.hierarchy) (StrictHierarchy.zero_iff.mp hψ.hierarchy)),
      provable_iff_of_models_iff fun V _ _ e => by simp [hφ.iff_models V e, hψ.iff_models V e]⟩

lemma bexs_sigma_step (ih : Closure T s) :
    ∀ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → Nonempty (StrictEquiv T 𝚺 (s + 1) φ) →
        Nonempty (StrictEquiv T 𝚺 (s + 1) (∃¹[“x. x < !!t”] φ)) := by
  rintro n φ t ht ⟨⟨φ', hφ', hprov'⟩⟩;
  obtain ⟨u, rfl⟩ := Rew.positive_iff.mp ht;
  have hiff' := models_iff_of_provable_iff' hprov';
  obtain ⟨ψ₀, rfl, hψ₀⟩ := hφ'.sigma_succ_elim;
  set v : Fin (n + 2) → ArithmeticSemiterm Empty (n + 2) :=
    #1 :> #0 :> fun i => #(i.succ.succ) with hv;
  set ψ₀' : ArithmeticSemiformula Empty (n + 2) := Rew.subst v ▹ ψ₀;
  have hψ₀'strict : StrictHierarchy 𝚷 s ψ₀' := hψ₀.rew (Rew.subst v);
  obtain ⟨⟨χ, hχ, hχprov⟩⟩ := ih.bexs 𝚷 (t := Rew.bShift (Rew.bShift u))
    (by simp) ⟨refl hψ₀'strict⟩;
  have hχiff := models_iff_of_provable_iff' hχprov;
  have hχiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 1) → V),
      V ⊧/e (ψ₀'.bexsLT (Rew.bShift u)) ↔ V ⊧/e χ := hχiff;
  use ∃¹ χ;
  . exact hχ.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    have hswap : ∀ (a b : V) (e : Fin n → V),
        V ⊧/(b :> a :> e) ψ₀' ↔ V ⊧/(a :> b :> e) ψ₀ := by
      intro a b e;
      show V ⊧/(b :> a :> e) (Rew.subst v ▹ ψ₀) ↔ V ⊧/(a :> b :> e) ψ₀;
      rw [Semiformula.eval_rew];
      have hA : (Semiterm.val (M := V) (b :> a :> e) Empty.elim) ∘ (Rew.subst v) ∘ Semiterm.bvar
          = (a :> b :> e : Fin (n + 2) → V) := by
        funext i;
        cases i using Fin.cases with
        | zero => simp [hv];
        | succ i =>
          cases i using Fin.cases with
          | zero => simp [hv];
          | succ i => simp [hv];
      have hB : (Semiterm.val (M := V) (b :> a :> e) Empty.elim) ∘ (Rew.subst v) ∘ Semiterm.fvar
          = (Empty.elim : Empty → V) := by
        funext i; exact i.elim;
      rw [hA, hB];
    have hφiff : ∀ b : V, V ⊧/(b :> e) φ ↔ ∃ a, V ⊧/(a :> b :> e) ψ₀ := fun b =>
      (hiff' V (b :> e)).trans Semiformula.eval_ex;
    show V ⊧/e (φ.bexsLT u) ↔ V ⊧/e (∃¹ χ);
    simp only [Semiformula.eval_bexsLT, Semiformula.eval_ex, ← hχiff', Semiterm.val_bShift,
      hswap, hφiff];
    grind;

lemma ball_sigma_step (hT : 𝗜𝚺 (s + 1) ⪯ T) (ih : Closure T s) :
    ∀ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → Nonempty (StrictEquiv T 𝚺 (s + 1) φ) →
        Nonempty (StrictEquiv T 𝚺 (s + 1) (∀¹[“x. x < !!t”] φ)) := by
  have := hT;
  rintro n φ t ht ⟨⟨φ', hφ', hprov'⟩⟩;
  obtain ⟨u, rfl⟩ := Rew.positive_iff.mp ht;
  have hiff' := models_iff_of_provable_iff' hprov';
  obtain ⟨ψ₀, rfl, hψ₀⟩ := hφ'.sigma_succ_elim;
  have hψ₀qq : StrictHierarchy 𝚷 s (ψ₀ ⇜ (#0 :> #1 :> (#·.succ.succ.succ))) := hψ₀.rew (Rew.subst _);
  obtain ⟨⟨A, hA, hAprov⟩⟩ := ih.bexs 𝚷
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) ⟨refl hψ₀qq⟩;
  have hAiff := models_iff_of_provable_iff' hAprov;
  obtain ⟨⟨D, hD, hDprov⟩⟩ := ih.ball 𝚷
    (t := Rew.bShift (Rew.bShift u)) (by simp) ⟨refl hA⟩;
  have hDiff := models_iff_of_provable_iff' hDprov;
  use ∃¹ D;
  . exact hD.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := models_of_subtheory (T := 𝗜𝚺 (s + 1)) (U := T) inferInstance;
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s + 1);
    have hAeval : ∀ x w : V, V ⊧/(x :> w :> e) A ↔ ∃ y ≤ w, V ⊧/(y :> x :> e) ψ₀ := by
      intro x w;
      rw [← hAiff V (x :> w :> e)];
      simp [Semiformula.eval_insert2, Arithmetic.lt_succ_iff_le, -Semiformula.eval_substs];
    have hDeval : ∀ w : V, V ⊧/(w :> e) D ↔ ∀ x < u.valb e, ∃ y ≤ w, V ⊧/(y :> x :> e) ψ₀ := by
      intro w;
      rw [← hDiff V (w :> e)];
      simp [hAeval];
    have hφeval : ∀ x : V, V ⊧/(x :> e) φ ↔ ∃ y, V ⊧/(y :> x :> e) ψ₀ := fun x =>
      (hiff' V (x :> e)).trans Semiformula.eval_ex;
    show V ⊧/e (φ.ballLT u) ↔ V ⊧/e (∃¹ D);
    simp only [Semiformula.eval_ballLT, Semiformula.eval_ex, hDeval, hφeval];
    constructor;
    . intro h;
      have hθ : Hierarchy 𝚺 (s + 1) ψ₀ := hψ₀.hierarchy.accum 𝚺;
      exact sigma_exists_bound_witness hθ e (u.valb e) h;
    . rintro ⟨w, hw⟩ x hx;
      obtain ⟨y, -, hy⟩ := hw x hx;
      exact ⟨y, hy⟩;

lemma or_sigma_step (ih : Closure T s) :
    ∀ {n} {φ ψ : ArithmeticSemiformula Empty n},
      Nonempty (StrictEquiv T 𝚺 (s + 1) φ) → Nonempty (StrictEquiv T 𝚺 (s + 1) ψ) →
        Nonempty (StrictEquiv T 𝚺 (s + 1) (φ ⋎ ψ)) := by
  rintro n φ ψ ⟨⟨φ', hφ', hφprov⟩⟩ ⟨⟨ψ', hψ', hψprov⟩⟩;
  have hφiff := models_iff_of_provable_iff' hφprov;
  have hψiff := models_iff_of_provable_iff' hψprov;
  obtain ⟨φ₀, rfl, hφ₀⟩ := hφ'.sigma_succ_elim;
  obtain ⟨ψ₀, rfl, hψ₀⟩ := hψ'.sigma_succ_elim;
  obtain ⟨⟨χ, hχ, hχprov⟩⟩ := ih.or 𝚷 ⟨refl hφ₀⟩ ⟨refl hψ₀⟩;
  have hχiff := models_iff_of_provable_iff' hχprov;
  use ∃¹ χ;
  . exact hχ.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    have hφiff' : V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) φ₀ := (hφiff V e).trans Semiformula.eval_ex;
    have hψiff' : V ⊧/e ψ ↔ ∃ x, V ⊧/(x :> e) ψ₀ := (hψiff V e).trans Semiformula.eval_ex;
    simp only [LogicalConnective.HomClass.map_or, Semiformula.eval_ex, hφiff', hψiff'];
    constructor;
    . rintro (⟨x, hx⟩ | ⟨x, hx⟩);
      . exact ⟨x, (hχiff V (x :> e)).mp (by left; exact hx)⟩;
      . exact ⟨x, (hχiff V (x :> e)).mp (by right; exact hx)⟩;
    . rintro ⟨x, hx⟩;
      rcases (hχiff V (x :> e)).mpr hx with h | h;
      . left; exact ⟨x, h⟩;
      . right; exact ⟨x, h⟩;

lemma and_sigma_step (hT : 𝗜𝚺 (s + 1) ⪯ T) (ih : Closure T s) :
    ∀ {n} {φ ψ : ArithmeticSemiformula Empty n},
      Nonempty (StrictEquiv T 𝚺 (s + 1) φ) → Nonempty (StrictEquiv T 𝚺 (s + 1) ψ) →
        Nonempty (StrictEquiv T 𝚺 (s + 1) (φ ⋏ ψ)) := by
  have : 𝗜𝚺₀ ⪯ T := Entailment.WeakerThan.trans (ISigma_weakerThan_of_le (Nat.zero_le (s + 1))) hT;
  rintro n φ ψ ⟨⟨φ', hφ', hφprov⟩⟩ ⟨⟨ψ', hψ', hψprov⟩⟩;
  have hφiff := models_iff_of_provable_iff' hφprov;
  have hψiff := models_iff_of_provable_iff' hψprov;
  obtain ⟨φ₀, rfl, hφ₀⟩ := hφ'.sigma_succ_elim;
  obtain ⟨ψ₀, rfl, hψ₀⟩ := hψ'.sigma_succ_elim;
  have hφ₀' : StrictHierarchy 𝚷 s (φ₀ ⇜ (#0 :> (#·.succ.succ))) := hφ₀.rew (Rew.subst _);
  have hψ₀' : StrictHierarchy 𝚷 s (ψ₀ ⇜ (#0 :> (#·.succ.succ))) := hψ₀.rew (Rew.subst _);
  obtain ⟨⟨A, hA, hAprov⟩⟩ := ih.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) ⟨refl hφ₀'⟩;
  obtain ⟨⟨B, hB, hBprov⟩⟩ := ih.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) ⟨refl hψ₀'⟩;
  have hAiff := models_iff_of_provable_iff' hAprov;
  have hBiff := models_iff_of_provable_iff' hBprov;
  obtain ⟨⟨χ, hχ, hχprov⟩⟩ := ih.and 𝚷 ⟨refl hA⟩ ⟨refl hB⟩;
  have hχiff := models_iff_of_provable_iff' hχprov;
  use ∃¹ χ;
  . exact hχ.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance;
    have hA_eval : ∀ z : V, V ⊧/(z :> e) A ↔ ∃ x ≤ z, V ⊧/(x :> e) φ₀ := fun z => by
      rw [← hAiff V (z :> e)];
      show V ⊧/(z :> e)
        ((φ₀ ⇜ (#0 :> (#·.succ.succ)) : ArithmeticSemiformula Empty (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [Semiformula.eval_insert1, -Semiformula.eval_substs];
    have hB_eval : ∀ z : V, V ⊧/(z :> e) B ↔ ∃ x ≤ z, V ⊧/(x :> e) ψ₀ := fun z => by
      rw [← hBiff V (z :> e)];
      show V ⊧/(z :> e)
        ((ψ₀ ⇜ (#0 :> (#·.succ.succ)) : ArithmeticSemiformula Empty (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [Semiformula.eval_insert1, -Semiformula.eval_substs];
    have hφiff' : V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) φ₀ := (hφiff V e).trans Semiformula.eval_ex;
    have hψiff' : V ⊧/e ψ ↔ ∃ x, V ⊧/(x :> e) ψ₀ := (hψiff V e).trans Semiformula.eval_ex;
    simp only [LogicalConnective.HomClass.map_and, Semiformula.eval_ex, hφiff', hψiff',
      ← hχiff, hA_eval, hB_eval];
    constructor;
    . rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
      exact ⟨max x y, ⟨x, le_max_left x y, hx⟩, ⟨y, le_max_right x y, hy⟩⟩;
    . rintro ⟨z, ⟨x, _, hx⟩, ⟨y, _, hy⟩⟩;
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;

lemma closure_succ (hT : 𝗜𝚺 (s + 1) ⪯ T) (ih : Closure T s) : Closure T (s + 1) where
  ball := by
    rintro Γ n φ t ht hφ;
    rcases Γ with _ | _;
    . exact ball_sigma_step hT ih ht hφ;
    . simpa using (bexs_sigma_step ih ht (hφ.map neg)).map neg;
  bexs := by
    rintro Γ n φ t ht hφ;
    rcases Γ with _ | _;
    . exact bexs_sigma_step ih ht hφ;
    . simpa using (ball_sigma_step hT ih ht (hφ.map neg)).map neg;
  and := by
    rintro Γ n φ ψ hφ hψ;
    rcases Γ with _ | _;
    . exact and_sigma_step hT ih hφ hψ;
    . simpa [Semiformula.imp_eq] using (or_sigma_step ih (hφ.map neg) (hψ.map neg)).map neg;
  or := by
    rintro Γ n φ ψ hφ hψ;
    rcases Γ with _ | _;
    . exact or_sigma_step ih hφ hψ;
    . simpa [Semiformula.imp_eq] using (and_sigma_step hT ih (hφ.map neg) (hψ.map neg)).map neg;

lemma closure (hT : 𝗜𝚺 s ⪯ T) : Closure T s := by
  induction s with
  | zero => exact closure_zero;
  | succ s ih =>
    exact closure_succ hT (ih (ISigma_weakerThan_of_le_trans (by omega) hT));

lemma exs (hT : 𝗜𝚺 s ⪯ T) (c : Closure T s) {n : ℕ}
    {φ : ArithmeticSemiformula Empty (n + 1)} (h : Nonempty (StrictEquiv T 𝚺 (s + 1) φ)) :
    Nonempty (StrictEquiv T 𝚺 (s + 1) (∃¹ φ)) := by
  have : 𝗜𝚺₀ ⪯ T := Entailment.WeakerThan.trans (ISigma_weakerThan_of_le (Nat.zero_le s)) hT;
  obtain ⟨⟨φ', hφ', hprov'⟩⟩ := h;
  have hiff' := models_iff_of_provable_iff' hprov';
  obtain ⟨ψ₀, rfl, hψ₀⟩ := hφ'.sigma_succ_elim;
  have hψ₀' : StrictHierarchy 𝚷 s (ψ₀ ⇜ (#0 :> #1 :> (#·.succ.succ.succ))) := hψ₀.rew (Rew.subst _);
  obtain ⟨⟨A, hA, hAprov⟩⟩ := c.bexs 𝚷
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) ⟨refl hψ₀'⟩;
  obtain ⟨⟨B, hB, hBprov⟩⟩ := c.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) ⟨refl hA⟩;
  have hAiff := models_iff_of_provable_iff' hAprov;
  have hBiff := models_iff_of_provable_iff' hBprov;
  have hAiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 2) → V),
      V ⊧/e ((ψ₀ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)) : ArithmeticSemiformula Empty (n + 3)).bexsLTSucc
        (‘#1’ : ArithmeticSemiterm Empty (n + 2))) ↔ V ⊧/e A := hAiff;
  have hBiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 1) → V),
      V ⊧/e (A.bexsLTSucc (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ V ⊧/e B := hBiff;
  use ∃¹ B;
  . exact hB.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance;
    have hAeval : ∀ y z : V, V ⊧/(y :> z :> e) A ↔ ∃ x ≤ z, V ⊧/(x :> y :> e) ψ₀ := by
      intro y z;
      rw [← hAiff' V (y :> z :> e)];
      simp [Semiformula.eval_insert2, -Semiformula.eval_substs];
    have hBeval : ∀ z : V, V ⊧/(z :> e) B ↔ ∃ y ≤ z, V ⊧/(y :> z :> e) A := by
      intro z;
      rw [← hBiff' V (z :> e)];
      simp;
    have hφeval : ∀ y : V, V ⊧/(y :> e) φ ↔ ∃ x, V ⊧/(x :> y :> e) ψ₀ := fun y =>
      (hiff' V (y :> e)).trans Semiformula.eval_ex;
    simp only [Semiformula.eval_ex, hφeval, hBeval, hAeval];
    constructor;
    . rintro ⟨y, x, hx⟩;
      exact ⟨max x y, y, le_max_right x y, x, le_max_left x y, hx⟩;
    . rintro ⟨z, y, -, x, -, hx⟩;
      exact ⟨y, x, hx⟩;

lemma all (hT : 𝗜𝚺 s ⪯ T) (c : Closure T s) {n : ℕ}
    {φ : ArithmeticSemiformula Empty (n + 1)} (h : Nonempty (StrictEquiv T 𝚷 (s + 1) φ)) :
    Nonempty (StrictEquiv T 𝚷 (s + 1) (∀¹ φ)) := by
  simpa using (exs hT c (h.map neg)).map neg;

variable {Γ : Polarity} {n : ℕ}

theorem nonempty_strictEquiv {φ : ArithmeticSemiformula Empty n}
    (h : Hierarchy Γ s φ) (hT : 𝗜𝚺 s ⪯ T) : Nonempty (StrictEquiv T Γ s φ) := by
  induction h with
  | verum Γ s n => exact ⟨of_deltaZero (Hierarchy.verum 𝚺 0 n)⟩;
  | falsum Γ s n => exact ⟨of_deltaZero (Hierarchy.falsum 𝚺 0 n)⟩;
  | rel Γ s r v => exact ⟨of_deltaZero (Hierarchy.rel 𝚺 0 r v)⟩;
  | nrel Γ s r v => exact ⟨of_deltaZero (Hierarchy.nrel 𝚺 0 r v)⟩;
  | and _ _ ihp ihq => exact (closure hT).and _ (ihp hT) (ihq hT);
  | or _ _ ihp ihq => exact (closure hT).or _ (ihp hT) (ihq hT);
  | ball pos _ ih => exact (closure hT).ball _ pos (ih hT);
  | bexs pos _ ih => exact (closure hT).bexs _ pos (ih hT);
  | @exs s n φ _ ih =>
    have hT' : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact exs hT' (closure hT') (ih hT);
  | @all s n φ _ ih =>
    have hT' : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact all hT' (closure hT') (ih hT);
  | @sigma s n φ hp ih =>
    rcases s with _ | s;
    . exact ⟨refl (StrictHierarchy.sigma (StrictHierarchy.zero (Hierarchy.zero_iff.mp hp)))⟩;
    . exact (ih (ISigma_weakerThan_of_le_trans (by omega) hT)).map exs_of_pi;
  | @pi s n φ hp ih =>
    rcases s with _ | s;
    . exact ⟨refl (StrictHierarchy.pi (StrictHierarchy.zero (Hierarchy.zero_iff.mp hp)))⟩;
    . exact (ih (ISigma_weakerThan_of_le_trans (by omega) hT)).map all_of_sigma;
  | @dummy_sigma s n φ hp ih =>
    have hT' : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact (all hT' (closure hT') (ih (ISigma_weakerThan_of_le_trans (by omega) hT))).map alt_up;
  | @dummy_pi s n φ hp ih =>
    have hT' : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact (exs hT' (closure hT') (ih (ISigma_weakerThan_of_le_trans (by omega) hT))).map alt_up;

end LO.FirstOrder.Arithmetic
