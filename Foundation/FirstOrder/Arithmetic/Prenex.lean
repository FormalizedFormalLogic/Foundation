module

public import Foundation.FirstOrder.Arithmetic.Basic.Model
public import Foundation.FirstOrder.Arithmetic.BoundedCollection
public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy

/-!
# Prenex normal form for the arithmetical hierarchy

For `𝗜𝚺 s ⪯ T`, every `Hierarchy Γ s` formula `φ` is `T`-provably equivalent to `φ₀.toPrenex Γ s`
for some `φ₀ : ArithmeticSemisentence (n + s)` in `Hierarchy 𝚺 0`.
-/

@[expose] public section

open LO

namespace LO.FirstOrder

namespace Arithmetic

structure Prenex (Γ : Polarity) (s : ℕ) (ξ : Type*) (n : ℕ) where
  matrix : 𝚺₀.Semiformula ξ (n + s)

namespace Prenex

variable {Γ : Polarity} {s : ℕ} {ξ ξ₁ ξ₂ : Type*} {n n₁ n₂ : ℕ}

@[coe]
def val (π : Prenex Γ s ξ n) : ArithmeticSemiformula ξ n := π.matrix.val.toPrenex Γ s

instance : CoeTC (Prenex Γ s ξ n) (ArithmeticSemiformula ξ n) := ⟨val⟩

@[simp, grind .]
lemma val_hierarchy {π : Prenex Γ s ξ n} : Hierarchy Γ s π.val := by
  change Hierarchy Γ s (π.matrix.val.toPrenex Γ s)
  simpa only [Nat.zero_add] using Hierarchy.toPrenex (Γ := Γ) (j := 0) π.matrix.sigma_prop.of_zero

@[simp, grind .]
lemma val_deltaZero {π : Prenex Γ 0 ξ n} : Hierarchy 𝚺 0 π.val := π.matrix.sigma_prop


def neg (π : Prenex Γ s ξ n) : Prenex Γ.alt s ξ n :=
  ⟨.mkSigma (∼π.matrix.val) π.matrix.sigma_prop.neg.of_zero⟩

@[simp]
lemma val_neg (π : Prenex Γ s ξ n) : π.neg.val = ∼π.val := by simp [neg, val]


def rew (π : Prenex Γ s ξ₁ n₁) (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) : Prenex Γ s ξ₂ n₂ :=
  ⟨π.matrix.rew (ω.qpow s)⟩

@[simp]
lemma val_rew (π : Prenex Γ s ξ₁ n₁) (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) :
  (π.rew ω).val = ω ▹ π.val := by
  simp [val, rew]


def sigma (π : Prenex 𝚷 s ξ (n + 1)) : Prenex 𝚺 (s + 1) ξ n :=
  ⟨π.matrix.rew (Rew.castLE (Nat.succ_add n s).le)⟩

@[simp]
lemma val_sigma {π : Prenex 𝚷 s ξ (n + 1)} : π.sigma.val = ∃¹ π.val := by
  simp [val, sigma, Rewriting.quantItr_succ_smul_castLE]


def pi (π : Prenex 𝚺 s ξ (n + 1)) : Prenex 𝚷 (s + 1) ξ n :=
  ⟨π.matrix.rew (Rew.castLE (Nat.succ_add n s).le)⟩

@[simp, grind .]
lemma val_pi {π : Prenex 𝚺 s ξ (n + 1)} : π.pi.val = ∀¹ π.val := by
  simp [val, pi, Rewriting.quantItr_succ_smul_castLE]


def sigmaInv (π : Prenex 𝚺 (s + 1) ξ n) : Prenex 𝚷 s ξ (n + 1) :=
  ⟨π.matrix.rew (Rew.castLE (Nat.succ_add n s).ge)⟩

@[simp, grind .]
lemma val_sigmaInv {π : Prenex 𝚺 (s + 1) ξ n} : π.val = ∃¹ π.sigmaInv.val := by
  unfold val sigmaInv
  simp only [HierarchySymbol.Semiformula.val_rew]
  rw [← Polarity.quant_sigma, ← Polarity.alt_sigma, ← Rewriting.quantItr_succ_smul_castLE,
    ← TransitiveRewriting.comp_app]
  simp


def piInv (π : Prenex 𝚷 (s + 1) ξ n) : Prenex 𝚺 s ξ (n + 1) :=
  ⟨π.matrix.rew (Rew.castLE (Nat.succ_add n s).ge)⟩

@[simp, grind .]
lemma val_piInv {π : Prenex 𝚷 (s + 1) ξ n} : π.val = ∀¹ π.piInv.val := by
  unfold val piInv
  simp only [HierarchySymbol.Semiformula.val_rew]
  rw [← Polarity.quant_pi, ← Polarity.alt_pi, ← Rewriting.quantItr_succ_smul_castLE,
    ← TransitiveRewriting.comp_app]
  simp


def altUp (π : Prenex Γ s ξ n) : Prenex Γ.alt (s + 1) ξ n := by
  rcases Γ with _ | _
  . exact (π.rew Rew.bShift).pi
  . exact (π.rew Rew.bShift).sigma

lemma models_altUp (π : Prenex Γ s Empty n) (V : Type*) [ORingStructure V] (e : Fin n → V) :
  V ⊧/e π.altUp.val ↔ V ⊧/e π.val := by
  rcases Γ <;> simp [
    Polarity.eq_sigma, Polarity.alt_sigma, altUp,
    -val_piInv, -val_sigmaInv,
    Semiformula.eval_all, Nat.succ_eq_add_one
  ]


def ofΔ₀ (φ : 𝚺₀.Semiformula ξ n) : (Γ : Polarity) → (s : ℕ) → Prenex Γ s ξ n
  | Γ, 0 => ⟨φ⟩
  | Γ, s + 1 => by simpa using altUp (ofΔ₀ φ Γ.alt s)

lemma models_ofΔ₀ (φ : 𝚺₀.Semisentence n) (V : Type*) [ORingStructure V] (e : Fin n → V) :
    V ⊧/e (ofΔ₀ φ Γ s).val ↔ V ⊧/e φ.val := by
  induction s generalizing Γ with
  | zero => rfl
  | succ s ih =>
    rcases Γ with _ | _
    . change V ⊧/e (ofΔ₀ φ 𝚷 s).altUp.val ↔ V ⊧/e φ.val
      exact (models_altUp (ofΔ₀ φ 𝚷 s) V e).trans (ih (Γ := 𝚷))
    . change V ⊧/e (ofΔ₀ φ 𝚺 s).altUp.val ↔ V ⊧/e φ.val
      exact (models_altUp (ofΔ₀ φ 𝚺 s) V e).trans (ih (Γ := 𝚺))

variable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T]

@[simp, grind .]
lemma provable_iff_refl {π : Prenex Γ s Empty n} : T ⊢ ∀¹* (π.val 🡘 π.val) :=
  provable_iff_of_models_iff fun _ _ _ _ ↦ Iff.rfl

lemma provable_iff_neg {π : Prenex Γ s Empty n} (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) :
  T ⊢ ∀¹* ((∼φ) 🡘 π.neg.val) := by
  apply provable_iff_of_models_iff
  intro V _ _ e;
  simpa [neg, val, ← Semiformula.neg_toPrenex] using
    not_congr (models_iff_of_provable_iff hπ V e)

lemma provable_iff_rew {π : Prenex Γ s Empty n₁} (hπ : T ⊢ ∀¹* (φ 🡘 π.val))
  (ω : Rew ℒₒᵣ Empty n₁ Empty n₂) :
  T ⊢ ∀¹* ((ω ▹ φ) 🡘 (π.rew ω).val) := by
  apply provable_iff_of_models_iff
  intro V _ _ e
  rw [val_rew]
  simpa [Semiformula.eval_rew, Function.comp_def, Empty.eq_elim] using
    models_iff_of_provable_iff hπ V
      (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.bvar)

lemma provable_iff_sigma {π : Prenex 𝚷 s Empty (n + 1)} (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) :
  T ⊢ ∀¹* ((∃¹ φ) 🡘 π.sigma.val) := by
  apply provable_iff_of_models_iff
  intro V _ _ e
  rw [val_sigma]
  simpa [Semiformula.eval_ex, Empty.eq_elim] using
    exists_congr (fun x ↦ models_iff_of_provable_iff hπ V (x :> e))

lemma provable_iff_pi {π : Prenex 𝚺 s Empty (n + 1)} (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) :
  T ⊢ ∀¹* ((∀¹ φ) 🡘 π.pi.val) := by
  apply provable_iff_of_models_iff
  intro V _ _ e
  rw [val_pi]
  simpa [Semiformula.eval_all, Empty.eq_elim] using
    forall_congr' (fun x ↦ models_iff_of_provable_iff hπ V (x :> e))

lemma provable_iff_altUp {π : Prenex Γ s Empty n} (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) :
  T ⊢ ∀¹* (φ 🡘 π.altUp.val) := by
  apply provable_iff_of_models_iff
  intro V _ _ e
  exact (models_iff_of_provable_iff hπ V e).trans (models_altUp π V e).symm

lemma provable_iff_ofΔ₀ (φ₀ : 𝚺₀.Semisentence n) :
    T ⊢ ∀¹* (φ₀.val 🡘 (ofΔ₀ φ₀ Γ s).val) := by
  apply provable_iff_of_models_iff
  intro V _ _ e
  exact (models_ofΔ₀ φ₀ V e).symm


omit [𝗘𝗤 ℒₒᵣ ⪯ T] in
lemma provable_iff_sigmaInv {π : Prenex 𝚺 (s + 1) Empty n} (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) :
  T ⊢ ∀¹* (φ 🡘 ∃¹ π.sigmaInv.val) := π.val_sigmaInv ▸ hπ

omit [𝗘𝗤 ℒₒᵣ ⪯ T] in
lemma provable_iff_piInv {π : Prenex 𝚷 (s + 1) Empty n} (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) :
  T ⊢ ∀¹* (φ 🡘 ∀¹ π.piInv.val) := π.val_piInv ▸ hπ


lemma models_iff_sigmaInv
  {π : Prenex 𝚺 (s + 1) Empty n} (hπ : T ⊢ ∀¹* (φ 🡘 π.val))
  (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) :
  V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) π.sigmaInv.val :=
  (models_iff_of_provable_iff (provable_iff_sigmaInv hπ) V e).trans Semiformula.eval_ex

lemma models_iff_piInv
  {π : Prenex 𝚷 (s + 1) Empty n} (hπ : T ⊢ ∀¹* (φ 🡘 π.val))
  (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) :
  V ⊧/e φ ↔ ∀ x, V ⊧/(x :> e) π.piInv.val := by
  simpa [Semiformula.eval_all] using models_iff_of_provable_iff (provable_iff_piInv hπ) V e

structure ClosureData (s : ℕ) where
  ball {Γ : Polarity} {n : ℕ} : ArithmeticSemiterm Empty n → Prenex Γ s Empty (n + 1) → Prenex Γ s Empty n
  bexs {Γ : Polarity} {n : ℕ} : ArithmeticSemiterm Empty n → Prenex Γ s Empty (n + 1) → Prenex Γ s Empty n
  and  {Γ : Polarity} {n : ℕ} : Prenex Γ s Empty n → Prenex Γ s Empty n → Prenex Γ s Empty n
  or   {Γ : Polarity} {n : ℕ} : Prenex Γ s Empty n → Prenex Γ s Empty n → Prenex Γ s Empty n

structure ClosureData.Correct (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] (C : ClosureData s) where
  ball {Γ : Polarity} {n : ℕ} {φ} (u : ArithmeticSemiterm Empty n) (φ' : Prenex Γ s Empty (n + 1)) :
    T ⊢ ∀¹* (φ 🡘 φ'.val) →
    T ⊢ ∀¹* (φ.ballLT u 🡘 (C.ball u φ').val)
  bexs {Γ : Polarity} {n : ℕ} {φ} (u : ArithmeticSemiterm Empty n) (φ' : Prenex Γ s Empty (n + 1)) :
    T ⊢ ∀¹* (φ 🡘 φ'.val) →
    T ⊢ ∀¹* (φ.bexsLT u 🡘 (C.bexs u φ').val)
  and {Γ : Polarity} {n : ℕ} {φ ψ} (φ' ψ' : Prenex Γ s Empty n) :
    T ⊢ ∀¹* (φ 🡘 φ'.val) →
    T ⊢ ∀¹* (ψ 🡘 ψ'.val) →
    T ⊢ ∀¹* ((φ ⋏ ψ) 🡘 (C.and φ' ψ').val)
  or {Γ : Polarity} {n : ℕ} {φ ψ} (φ' ψ' : Prenex Γ s Empty n) :
    T ⊢ ∀¹* (φ 🡘 φ'.val) →
    T ⊢ ∀¹* (ψ 🡘 ψ'.val) →
    T ⊢ ∀¹* ((φ ⋎ ψ) 🡘 (C.or φ' ψ').val)


namespace ClosureData

def zero : ClosureData 0 where
  ball u π := ⟨.mkSigma _ (Hierarchy.ball (Rew.bShift_positive u) π.val_deltaZero)⟩
  bexs u π := ⟨.mkSigma _ (Hierarchy.bexs (Rew.bShift_positive u) π.val_deltaZero)⟩
  and  π ρ := ⟨.mkSigma _ (Hierarchy.and π.val_deltaZero ρ.val_deltaZero)⟩
  or   π ρ := ⟨.mkSigma _ (Hierarchy.or π.val_deltaZero ρ.val_deltaZero)⟩

lemma zero_correct (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] : zero.Correct T where
  ball u φ' hφ := by
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simpa [zero, Prenex.val, Semiformula.eval_ball] using
      forall_congr' (fun x ↦ imp_congr Iff.rfl (models_iff_of_provable_iff hφ V (x :> e)))
  bexs u φ' hφ := by
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simpa [zero, Prenex.val, Semiformula.eval_bexs] using
      exists_congr (fun x ↦ and_congr Iff.rfl (models_iff_of_provable_iff hφ V (x :> e)))
  and φ' ψ' hφ hψ := by
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp [zero, Prenex.val, models_iff_of_provable_iff hφ V e, models_iff_of_provable_iff hψ V e];
  or φ' ψ' hφ hψ := by
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp [zero, Prenex.val, models_iff_of_provable_iff hφ V e, models_iff_of_provable_iff hψ V e]

variable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {s n : ℕ}

def bexsSigma (C : ClosureData s) (u : ArithmeticSemiterm Empty n)
    (π : Prenex 𝚺 (s + 1) Empty (n + 1)) : Prenex 𝚺 (s + 1) Empty n :=
  (C.bexs (Rew.bShift u) (π.sigmaInv.rew (Rew.subst (#1 :> #0 :> (#·.succ.succ))))).sigma

lemma bexsSigma_correct {C : ClosureData s} (hC : C.Correct T)
    {φ : ArithmeticSemisentence (n + 1)} (u : ArithmeticSemiterm Empty n)
    (π : Prenex 𝚺 (s + 1) Empty (n + 1)) (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) :
    T ⊢ ∀¹* (φ.bexsLT u 🡘 (C.bexsSigma u π).val) := by
  set φ₁' := π.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 2) := ↑φ₁';
  set v : Fin (n + 2) → ArithmeticSemiterm Empty (n + 2) :=
    #1 :> #0 :> fun i => #(i.succ.succ) with hv;
  set φ₂ : ArithmeticSemisentence (n + 2) := Rew.subst v ▹ φ₁;
  let φ₂' := φ₁'.rew (Rew.subst v);
  have hχ := hC.bexs (φ := φ₂) (Rew.bShift u) φ₂'
    (by simpa [φ₂', φ₂, φ₁] using (provable_iff_rew (T := T) (by grind) (Rew.subst v)));
  have hχiff := models_iff_of_provable_iff hχ;
  have hχiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 1) → V),
      V ⊧/e (φ₂.bexsLT (Rew.bShift u)) ↔
        V ⊧/e ((C.bexs (Rew.bShift u) φ₂').val : ArithmeticSemisentence (n + 1)) :=
    hχiff;
  show T ⊢ ∀¹* (φ.bexsLT u 🡘 (C.bexs (Rew.bShift u) φ₂').sigma.val);
  apply provable_iff_of_models_iff
  intro V _ _ e;
  . rw [val_sigma]
    have hswap : ∀ (a b : V) (e : Fin n → V),
        V ⊧/(b :> a :> e) φ₂ ↔ V ⊧/(a :> b :> e) φ₁ := by
      intro a b e;
      show V ⊧/(b :> a :> e) (Rew.subst v ▹ φ₁) ↔ V ⊧/(a :> b :> e) φ₁;
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
    have hφiff : ∀ b : V, V ⊧/(b :> e) φ ↔ ∃ a, V ⊧/(a :> b :> e) φ₁ := fun b =>
      Prenex.models_iff_sigmaInv hπ V (b :> e);
    show V ⊧/e (φ.bexsLT u) ↔
      V ⊧/e (∃¹ (C.bexs (Rew.bShift u) φ₂').val);
    simp only [Semiformula.eval_bexsLT, Semiformula.eval_ex, ← hχiff', Semiterm.val_bShift,
      hswap, hφiff];
    grind;

def ballSigma (C : ClosureData s) (u : ArithmeticSemiterm Empty n)
    (π : Prenex 𝚺 (s + 1) Empty (n + 1)) : Prenex 𝚺 (s + 1) Empty n :=
  (C.ball (Rew.bShift u)
    (C.bexs ‘#1 + 1’ (π.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma

lemma ballSigma_correct [𝗜𝚺 (s + 1) ⪯ T] {C : ClosureData s} (hC : C.Correct T)
    {φ : ArithmeticSemisentence (n + 1)} (u : ArithmeticSemiterm Empty n)
    (π : Prenex 𝚺 (s + 1) Empty (n + 1)) (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) :
    T ⊢ ∀¹* (φ.ballLT u 🡘 (C.ballSigma u π).val) := by
  set φ₁' := π.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 2) := ↑φ₁';
  let φ₂' := φ₁'.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)));
  have hα := hC.bexs (φ := φ₁ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)))
    (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)) φ₂'
    (by simpa [φ₂', φ₁] using
      (provable_iff_rew (T := T) (by grind) (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))));
  have hαiff := models_iff_of_provable_iff hα;
  have hδ := hC.ball (Rew.bShift u) (C.bexs (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)) φ₂') hα;
  have hδiff := models_iff_of_provable_iff hδ;
  show T ⊢ ∀¹* (φ.ballLT u 🡘
    (C.ball (Rew.bShift u) (C.bexs (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)) φ₂')).sigma.val);
  apply provable_iff_of_models_iff
  intro V _ _ e;
  . rw [val_sigma]
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := models_of_subtheory (T := 𝗜𝚺 (s + 1)) (U := T) inferInstance;
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s + 1);
    have hαeval : ∀ x w : V,
        V ⊧/(x :> w :> e) ((C.bexs (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)) φ₂').val :
          ArithmeticSemisentence (n + 2)) ↔ ∃ y ≤ w, V ⊧/(y :> x :> e) φ₁ := by
      intro x w;
      rw [← hαiff V (x :> w :> e)];
      simp [Semiformula.eval_insert2, Arithmetic.lt_succ_iff_le, -Semiformula.eval_substs];
    have hδeval : ∀ w : V,
        V ⊧/(w :> e) ((C.ball (Rew.bShift u)
          (C.bexs (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)) φ₂')).val :
          ArithmeticSemisentence (n + 1)) ↔ ∀ x < u.valb e, ∃ y ≤ w, V ⊧/(y :> x :> e) φ₁ := by
      intro w;
      rw [← hδiff V (w :> e)];
      simp only [Semiformula.eval_ballLT, Semiterm.val_bShift, Nat.succ_eq_add_one,
        Semiformula.eval_bexsLT, Semiterm.val_operator, Matrix.comp₂, Nat.reduceAdd,
        Semiterm.val_bvar, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.comp₀,
        Structure.numeral_eq_numeral, ORingStructure.one_eq_one, Structure.Add.add,
        Semiformula.eval_substs]
      constructor
      . intro h x hx
        obtain ⟨y, hy, hxy⟩ := h x hx
        use y
        constructor
        . simpa [Arithmetic.lt_succ_iff_le] using hy
        . have hv :
              Semiterm.val (L := ℒₒᵣ) (M := V) (y :> x :> w :> e) Empty.elim ∘
                  (#0 :> #1 :> (#·.succ.succ.succ)) =
                (y :> x :> e) := by
            funext i
            cases i using Fin.cases with
            | zero => simp
            | succ i =>
              cases i using Fin.cases with
              | zero => simp
              | succ i => simp
          rw [hv] at hxy
          simpa [Semiformula.eval_insert2, -Semiformula.eval_substs] using hxy
      . intro h x hx
        obtain ⟨y, hy, hxy⟩ := h x hx
        use y
        constructor
        . simpa [Arithmetic.lt_succ_iff_le] using hy
        . have hv :
              Semiterm.val (L := ℒₒᵣ) (M := V) (y :> x :> w :> e) Empty.elim ∘
                  (#0 :> #1 :> (#·.succ.succ.succ)) =
                (y :> x :> e) := by
            funext i
            cases i using Fin.cases with
            | zero => simp
            | succ i =>
              cases i using Fin.cases with
              | zero => simp
              | succ i => simp
          rw [hv]
          simpa [Semiformula.eval_insert2, -Semiformula.eval_substs] using hxy;
    have hφeval : ∀ x : V, V ⊧/(x :> e) φ ↔ ∃ y, V ⊧/(y :> x :> e) φ₁ := fun x =>
      models_iff_sigmaInv hπ V (x :> e);
    show V ⊧/e (φ.ballLT u) ↔
      V ⊧/e (∃¹ (C.ball (Rew.bShift u)
        (C.bexs (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)) φ₂')).val);
    simp only [Semiformula.eval_ballLT, Semiformula.eval_ex, hδeval, hφeval];
    constructor;
    . intro h;
      have hθ : Hierarchy 𝚺 (s + 1) φ₁ := φ₁'.val_hierarchy.accum 𝚺;
      exact sigma_exists_bound_witness hθ e (u.valb e) h;
    . rintro ⟨w, hw⟩ x hx;
      obtain ⟨y, -, hy⟩ := hw x hx;
      exact ⟨y, hy⟩;

def orSigma (C : ClosureData s) (π ρ : Prenex 𝚺 (s + 1) Empty n) : Prenex 𝚺 (s + 1) Empty n :=
  (C.or π.sigmaInv ρ.sigmaInv).sigma

lemma orSigma_correct {C : ClosureData s} (hC : C.Correct T) {φ ψ : ArithmeticSemisentence n}
    (π ρ : Prenex 𝚺 (s + 1) Empty n)
    (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) (hρ : T ⊢ ∀¹* (ψ 🡘 ρ.val)) :
    T ⊢ ∀¹* ((φ ⋎ ψ) 🡘 (C.orSigma π ρ).val) := by
  set φ₁' := π.sigmaInv;
  set ψ₁' := ρ.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 1) := ↑φ₁';
  set ψ₁ : ArithmeticSemisentence (n + 1) := ↑ψ₁';
  have hχ := hC.or φ₁' ψ₁' provable_iff_refl provable_iff_refl;
  have hχiff := models_iff_of_provable_iff hχ;
  show T ⊢ ∀¹* ((φ ⋎ ψ) 🡘 (C.or φ₁' ψ₁').sigma.val);
  apply provable_iff_of_models_iff
  intro V _ _ e;
  . rw [val_sigma]
    have hφiff' : V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) φ₁ := models_iff_sigmaInv hπ V e;
    have hψiff' : V ⊧/e ψ ↔ ∃ x, V ⊧/(x :> e) ψ₁ := models_iff_sigmaInv hρ V e;
    simp only [LogicalConnective.HomClass.map_or, Semiformula.eval_ex, hφiff', hψiff'];
    constructor;
    . rintro (⟨x, hx⟩ | ⟨x, hx⟩);
      . use x;
        apply (hχiff V (x :> e)).mp;
        left;
        exact hx;
      . use x;
        apply (hχiff V (x :> e)).mp;
        right;
        exact hx;
    . rintro ⟨x, hx⟩;
      rcases (hχiff V (x :> e)).mpr hx with h | h;
      . left; exact ⟨x, h⟩;
      . right; exact ⟨x, h⟩;

def andSigma (C : ClosureData s) (π ρ : Prenex 𝚺 (s + 1) Empty n) : Prenex 𝚺 (s + 1) Empty n :=
  (C.and (C.bexs ‘#0 + 1’ (π.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))
         (C.bexs ‘#0 + 1’ (ρ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))).sigma

lemma andSigma_correct [𝗜𝚺 (s + 1) ⪯ T] {C : ClosureData s} (hC : C.Correct T)
    {φ ψ : ArithmeticSemisentence n} (π ρ : Prenex 𝚺 (s + 1) Empty n)
    (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) (hρ : T ⊢ ∀¹* (ψ 🡘 ρ.val)) :
    T ⊢ ∀¹* ((φ ⋏ ψ) 🡘 (C.andSigma π ρ).val) := by
  have : 𝗜𝚺₀ ⪯ T := Entailment.WeakerThan.trans
    (ISigma_weakerThan_of_le (by omega)) ‹𝗜𝚺(s + 1) ⪯ T›;
  set φ₁' := π.sigmaInv;
  set ψ₁' := ρ.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 1) := ↑φ₁';
  set ψ₁ : ArithmeticSemisentence (n + 1) := ↑ψ₁';
  let φ₂' := φ₁'.rew (Rew.subst (#0 :> (#·.succ.succ)));
  have hα := hC.bexs (φ := φ₁ ⇜ (#0 :> (#·.succ.succ)))
    (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)) φ₂'
    (by simpa [φ₂', φ₁] using
      (provable_iff_rew (T := T) (by grind) (Rew.subst (#0 :> (#·.succ.succ)))));
  let ψ₂' := ψ₁'.rew (Rew.subst (#0 :> (#·.succ.succ)));
  have hβ := hC.bexs (φ := ψ₁ ⇜ (#0 :> (#·.succ.succ)))
    (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)) ψ₂'
    (by simpa [ψ₂', ψ₁] using
      (provable_iff_rew (T := T) (by grind) (Rew.subst (#0 :> (#·.succ.succ)))));
  have hαiff := models_iff_of_provable_iff hα;
  have hβiff := models_iff_of_provable_iff hβ;
  have hχ := hC.and (C.bexs (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)) φ₂')
    (C.bexs (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)) ψ₂')
    provable_iff_refl provable_iff_refl;
  have hχiff := models_iff_of_provable_iff hχ;
  show T ⊢ ∀¹* ((φ ⋏ ψ) 🡘
    (C.and (C.bexs (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)) φ₂')
           (C.bexs (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)) ψ₂')).sigma.val);
  apply provable_iff_of_models_iff
  intro V _ _ e;
  . rw [val_sigma]
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance;
    have hα_eval : ∀ z : V,
        V ⊧/(z :> e) ((C.bexs (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)) φ₂').val :
          ArithmeticSemisentence (n + 1)) ↔ ∃ x ≤ z, V ⊧/(x :> e) φ₁ := fun z => by
      rw [← hαiff V (z :> e)];
      show V ⊧/(z :> e)
        ((φ₁ ⇜ (#0 :> (#·.succ.succ)) : ArithmeticSemisentence (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [Semiformula.eval_insert1, -Semiformula.eval_substs];
    have hβ_eval : ∀ z : V,
        V ⊧/(z :> e) ((C.bexs (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)) ψ₂').val :
          ArithmeticSemisentence (n + 1)) ↔ ∃ x ≤ z, V ⊧/(x :> e) ψ₁ := fun z => by
      rw [← hβiff V (z :> e)];
      show V ⊧/(z :> e)
        ((ψ₁ ⇜ (#0 :> (#·.succ.succ)) : ArithmeticSemisentence (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [Semiformula.eval_insert1, -Semiformula.eval_substs];
    have hφiff' : V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) φ₁ := models_iff_sigmaInv hπ V e;
    have hψiff' : V ⊧/e ψ ↔ ∃ x, V ⊧/(x :> e) ψ₁ := models_iff_sigmaInv hρ V e;
    have hχ_eval : ∀ z : V,
        V ⊧/(z :> e) ((C.and (C.bexs (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)) φ₂')
          (C.bexs (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)) ψ₂')).val :
          ArithmeticSemisentence (n + 1)) ↔
        V ⊧/(z :> e) ((C.bexs (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)) φ₂').val :
          ArithmeticSemisentence (n + 1)) ∧
        V ⊧/(z :> e) ((C.bexs (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)) ψ₂').val :
          ArithmeticSemisentence (n + 1)) := by
      intro z
      exact (hχiff V (z :> e)).symm
    simp only [LogicalConnective.HomClass.map_and, Semiformula.eval_ex, hφiff', hψiff',
      hχ_eval, hα_eval, hβ_eval];
    constructor;
    . rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
      exact ⟨max x y, ⟨x, le_max_left x y, hx⟩, ⟨y, le_max_right x y, hy⟩⟩;
    . rintro ⟨z, ⟨x, _, hx⟩, ⟨y, _, hy⟩⟩;
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;

end ClosureData


structure Closure (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] (s : ℕ) : Prop where
  ball : ∀ Γ {n} {φ : ArithmeticSemisentence (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → (∃ π : Prenex Γ s Empty (n + 1), T ⊢ ∀¹* (φ 🡘 π.val)) →
        ∃ π : Prenex Γ s Empty n, T ⊢ ∀¹* ((∀¹[“x. x < !!t”] φ) 🡘 π.val)
  bexs : ∀ Γ {n} {φ : ArithmeticSemisentence (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → (∃ π : Prenex Γ s Empty (n + 1), T ⊢ ∀¹* (φ 🡘 π.val)) →
        ∃ π : Prenex Γ s Empty n, T ⊢ ∀¹* ((∃¹[“x. x < !!t”] φ) 🡘 π.val)
  and : ∀ Γ {n} {φ ψ : ArithmeticSemisentence n},
    (∃ π : Prenex Γ s Empty n, T ⊢ ∀¹* (φ 🡘 π.val)) →
    (∃ π : Prenex Γ s Empty n, T ⊢ ∀¹* (ψ 🡘 π.val)) →
      ∃ π : Prenex Γ s Empty n, T ⊢ ∀¹* ((φ ⋏ ψ) 🡘 π.val)
  or : ∀ Γ {n} {φ ψ : ArithmeticSemisentence n},
    (∃ π : Prenex Γ s Empty n, T ⊢ ∀¹* (φ 🡘 π.val)) →
    (∃ π : Prenex Γ s Empty n, T ⊢ ∀¹* (ψ 🡘 π.val)) →
      ∃ π : Prenex Γ s Empty n, T ⊢ ∀¹* ((φ ⋎ ψ) 🡘 π.val)

lemma closure_zero : Closure T 0 where
  ball := by
    intro Γ n φ t ht h;
    obtain ⟨π, hπ⟩ := h
    exact ⟨⟨.mkSigma _ (Hierarchy.ball ht π.val_deltaZero)⟩,
      provable_iff_of_models_iff fun V _ _ e ↦ by
        simpa [Prenex.val, Semiformula.eval_ball] using
          forall_congr' (fun x ↦ imp_congr Iff.rfl (models_iff_of_provable_iff hπ V (x :> e)))⟩;
  bexs := by
    intro Γ n φ t ht h;
    obtain ⟨π, hπ⟩ := h
    exact ⟨⟨.mkSigma _ (Hierarchy.bexs ht π.val_deltaZero)⟩,
      provable_iff_of_models_iff fun V _ _ e ↦ by
        simpa [Prenex.val, Semiformula.eval_bexs] using
          exists_congr (fun x ↦ and_congr Iff.rfl (models_iff_of_provable_iff hπ V (x :> e)))⟩;
  and := by
    intro Γ n φ ψ hφ hψ;
    obtain ⟨π, hπ⟩ := hφ
    obtain ⟨ρ, hρ⟩ := hψ
    exact ⟨⟨.mkSigma _ (Hierarchy.and π.val_deltaZero ρ.val_deltaZero)⟩,
      provable_iff_of_models_iff fun V _ _ e ↦ by
        simp [Prenex.val, models_iff_of_provable_iff hπ V e,
          models_iff_of_provable_iff hρ V e]
    ⟩;
  or := by
    intro Γ n φ ψ hφ hψ;
    obtain ⟨π, hπ⟩ := hφ
    obtain ⟨ρ, hρ⟩ := hψ
    exact ⟨⟨.mkSigma _ (Hierarchy.or π.val_deltaZero ρ.val_deltaZero)⟩,
      provable_iff_of_models_iff fun V _ _ e ↦
        by simp [Prenex.val, models_iff_of_provable_iff hπ V e,
          models_iff_of_provable_iff hρ V e]⟩;

section QuantifierStep

variable {φ : ArithmeticSemisentence (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)}

lemma bexs_sigma_step (ih : Closure T s) (ht : t.Positive)
    (hφ : ∃ π : Prenex 𝚺 (s + 1) Empty (n + 1), T ⊢ ∀¹* (φ 🡘 π.val)) :
  ∃ π : Prenex 𝚺 (s + 1) Empty n,
    T ⊢ ∀¹* ((∃¹[“x. x < !!t”] φ) 🡘 π.val) := by
  obtain ⟨u, rfl⟩ := Rew.positive_iff.mp ht;
  obtain ⟨π, hπ⟩ := hφ
  set φ₁' := π.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 2) := ↑φ₁';
  set v : Fin (n + 2) → ArithmeticSemiterm Empty (n + 2) :=
    #1 :> #0 :> fun i => #(i.succ.succ) with hv;
  set φ₂ : ArithmeticSemisentence (n + 2) := Rew.subst v ▹ φ₁;
  let φ₂' := φ₁'.rew (Rew.subst v);
  obtain ⟨χ, hχ⟩ := ih.bexs 𝚷 (φ := φ₂) (t := Rew.bShift (Rew.bShift u)) (by simp)
    (by
      exact ⟨φ₂', by simpa [φ₂', φ₂, φ₁] using
        (provable_iff_rew (T := T) (by grind) (Rew.subst v))⟩)
  have hχiff := models_iff_of_provable_iff hχ;
  have hχiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 1) → V),
      V ⊧/e (φ₂.bexsLT (Rew.bShift u)) ↔
        V ⊧/e (↑χ : ArithmeticSemisentence (n + 1)) :=
    hχiff;
  use χ.sigma
  apply provable_iff_of_models_iff
  intro V _ _ e;
  . change V ⊧/e (φ.bexsLT u) ↔ V ⊧/e χ.sigma.val;
    rw [val_sigma]
    have hswap : ∀ (a b : V) (e : Fin n → V),
        V ⊧/(b :> a :> e) φ₂ ↔ V ⊧/(a :> b :> e) φ₁ := by
      intro a b e;
      show V ⊧/(b :> a :> e) (Rew.subst v ▹ φ₁) ↔ V ⊧/(a :> b :> e) φ₁;
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
    have hφiff : ∀ b : V, V ⊧/(b :> e) φ ↔ ∃ a, V ⊧/(a :> b :> e) φ₁ := fun b =>
      Prenex.models_iff_sigmaInv hπ V (b :> e);
    show V ⊧/e (φ.bexsLT u) ↔
      V ⊧/e (∃¹ (↑χ : ArithmeticSemisentence (n + 1)));
    simp only [Semiformula.eval_bexsLT, Semiformula.eval_ex, ← hχiff', Semiterm.val_bShift,
      hswap, hφiff];
    grind;

lemma ball_sigma_step [𝗜𝚺 (s + 1) ⪯ T] (ih : Closure T s) (ht : t.Positive)
    (hφ : ∃ π : Prenex 𝚺 (s + 1) Empty (n + 1), T ⊢ ∀¹* (φ 🡘 π.val)) :
  ∃ π : Prenex 𝚺 (s + 1) Empty n,
    T ⊢ ∀¹* ((∀¹[“x. x < !!t”] φ) 🡘 π.val) := by
  obtain ⟨u, rfl⟩ := Rew.positive_iff.mp ht;
  obtain ⟨π, hπ⟩ := hφ
  set φ₁' := π.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 2) := ↑φ₁';
  let φ₂' :=
    φ₁'.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)));
  obtain ⟨α, hα⟩ := ih.bexs 𝚷 (φ := φ₁ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)))
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) (by
      exact ⟨φ₂', by simpa [φ₂', φ₁] using
        (provable_iff_rew (T := T) (by grind)
        (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))⟩)
  have hαiff := models_iff_of_provable_iff hα;
  obtain ⟨δ, hδ⟩ := ih.ball 𝚷 (t := Rew.bShift (Rew.bShift u)) (by simp)
    ⟨α, hα⟩;
  have hδiff := models_iff_of_provable_iff hδ;
  use δ.sigma
  apply provable_iff_of_models_iff
  intro V _ _ e;
  . change V ⊧/e (φ.ballLT u) ↔ V ⊧/e δ.sigma.val;
    rw [val_sigma]
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := models_of_subtheory (T := 𝗜𝚺 (s + 1)) (U := T) inferInstance;
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s + 1);
    have hαeval : ∀ x w : V, V ⊧/(x :> w :> e) (↑α : ArithmeticSemisentence (n + 2)) ↔
        ∃ y ≤ w, V ⊧/(y :> x :> e) φ₁ := by
      intro x w;
      rw [← hαiff V (x :> w :> e)];
      simp [Semiformula.eval_insert2, Arithmetic.lt_succ_iff_le, -Semiformula.eval_substs];
    have hδeval : ∀ w : V, V ⊧/(w :> e) (↑δ : ArithmeticSemisentence (n + 1)) ↔
        ∀ x < u.valb e, ∃ y ≤ w, V ⊧/(y :> x :> e) φ₁ := by
      intro w;
      rw [← hδiff V (w :> e)];
      simp only [Rew.finitary2, Rew.bShift_bvar, Fin.succ_one_eq_two, Rew.finitary0,
        Semiformula.eval_ball, Nat.succ_eq_add_one, Semiformula.eval_operator, Matrix.comp₂,
        Nat.reduceAdd, Semiterm.val_bvar, Matrix.cons_val_zero, Semiterm.val_bShift,
        Structure.lt_iff_lt, Fin.isValue, Matrix.cons_val_one, Fin.Fin1.eq_one,
        Matrix.cons_val_fin_one, Semiformula.eval_bexs, Semiterm.val_operator, Matrix.cons_app_two,
        Matrix.comp₀, Structure.numeral_eq_numeral, ORingStructure.one_eq_one,
        Structure.Add.add, Semiformula.eval_substs, LogicalConnective.Prop.and_eq]
      constructor
      . intro h x hx
        obtain ⟨y, hy, hxy⟩ := h x hx
        use y
        constructor
        . simpa [Arithmetic.lt_succ_iff_le] using hy
        . have hv :
              Semiterm.val (L := ℒₒᵣ) (M := V) (y :> x :> w :> e) Empty.elim ∘
                  (#0 :> #1 :> (#·.succ.succ.succ)) =
                (y :> x :> e) := by
            funext i
            cases i using Fin.cases with
            | zero => simp
            | succ i =>
              cases i using Fin.cases with
              | zero => simp
              | succ i => simp
          rw [hv] at hxy
          simpa [Semiformula.eval_insert2, -Semiformula.eval_substs] using hxy
      . intro h x hx
        obtain ⟨y, hy, hxy⟩ := h x hx
        use y
        constructor
        . simpa [Arithmetic.lt_succ_iff_le] using hy
        . have hv :
              Semiterm.val (L := ℒₒᵣ) (M := V) (y :> x :> w :> e) Empty.elim ∘
                  (#0 :> #1 :> (#·.succ.succ.succ)) =
                (y :> x :> e) := by
            funext i
            cases i using Fin.cases with
            | zero => simp
            | succ i =>
              cases i using Fin.cases with
              | zero => simp
              | succ i => simp
          rw [hv]
          simpa [Semiformula.eval_insert2, -Semiformula.eval_substs] using hxy;
    have hφeval : ∀ x : V, V ⊧/(x :> e) φ ↔ ∃ y, V ⊧/(y :> x :> e) φ₁ := fun x =>
      models_iff_sigmaInv hπ V (x :> e);
    show V ⊧/e (φ.ballLT u) ↔ V ⊧/e (∃¹ (↑δ : ArithmeticSemisentence (n + 1)));
    simp only [Semiformula.eval_ballLT, Semiformula.eval_ex, hδeval, hφeval];
    constructor;
    . intro h;
      have hθ : Hierarchy 𝚺 (s + 1) φ₁ := φ₁'.val_hierarchy.accum 𝚺;
      exact sigma_exists_bound_witness hθ e (u.valb e) h;
    . rintro ⟨w, hw⟩ x hx;
      obtain ⟨y, -, hy⟩ := hw x hx;
      exact ⟨y, hy⟩;

end QuantifierStep

section ConnectiveStep

variable {φ ψ : ArithmeticSemisentence n}

lemma or_sigma_step (ih : Closure T s)
    (hφ : ∃ π : Prenex 𝚺 (s + 1) Empty n, T ⊢ ∀¹* (φ 🡘 π.val))
    (hψ : ∃ π : Prenex 𝚺 (s + 1) Empty n, T ⊢ ∀¹* (ψ 🡘 π.val)) :
    ∃ π : Prenex 𝚺 (s + 1) Empty n, T ⊢ ∀¹* ((φ ⋎ ψ) 🡘 π.val) := by
  obtain ⟨π, hπ⟩ := hφ
  obtain ⟨ρ, hρ⟩ := hψ
  set φ₁' := π.sigmaInv;
  set ψ₁' := ρ.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 1) := ↑φ₁';
  set ψ₁ : ArithmeticSemisentence (n + 1) := ↑ψ₁';
  obtain ⟨χ, hχ⟩ := ih.or 𝚷
    ⟨φ₁', provable_iff_refl (π := φ₁')⟩ ⟨ψ₁', provable_iff_refl (π := ψ₁')⟩;
  have hχiff := models_iff_of_provable_iff hχ;
  use χ.sigma
  apply provable_iff_of_models_iff
  intro V _ _ e;
  . rw [val_sigma]
    have hφiff' : V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) φ₁ := models_iff_sigmaInv hπ V e;
    have hψiff' : V ⊧/e ψ ↔ ∃ x, V ⊧/(x :> e) ψ₁ := models_iff_sigmaInv hρ V e;
    simp only [LogicalConnective.HomClass.map_or, Semiformula.eval_ex, hφiff', hψiff'];
    constructor;
    . rintro (⟨x, hx⟩ | ⟨x, hx⟩);
      . use x;
        apply (hχiff V (x :> e)).mp;
        left;
        exact hx;
      . use x;
        apply (hχiff V (x :> e)).mp;
        right;
        exact hx;
    . rintro ⟨x, hx⟩;
      rcases (hχiff V (x :> e)).mpr hx with h | h;
      . left; exact ⟨x, h⟩;
      . right; exact ⟨x, h⟩;

lemma and_sigma_step [𝗜𝚺 (s + 1) ⪯ T] (ih : Closure T s)
  (hφ : ∃ π : Prenex 𝚺 (s + 1) Empty n, T ⊢ ∀¹* (φ 🡘 π.val))
  (hψ : ∃ π : Prenex 𝚺 (s + 1) Empty n, T ⊢ ∀¹* (ψ 🡘 π.val)) :
  ∃ π : Prenex 𝚺 (s + 1) Empty n, T ⊢ ∀¹* ((φ ⋏ ψ) 🡘 π.val) := by
  have : 𝗜𝚺₀ ⪯ T := Entailment.WeakerThan.trans
    (ISigma_weakerThan_of_le (by omega)) ‹𝗜𝚺(s + 1) ⪯ T›;
  obtain ⟨π, hπ⟩ := hφ
  obtain ⟨ρ, hρ⟩ := hψ
  set φ₁' := π.sigmaInv;
  set ψ₁' := ρ.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 1) := ↑φ₁';
  set ψ₁ : ArithmeticSemisentence (n + 1) := ↑ψ₁';
  let φ₂' :=
    φ₁'.rew (Rew.subst (#0 :> (#·.succ.succ)));
  obtain ⟨α, hα⟩ := ih.bexs 𝚷 (φ := φ₁ ⇜ (#0 :> (#·.succ.succ)))
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) (by
      exact ⟨φ₂', by simpa [φ₂', φ₁] using
        (provable_iff_rew (T := T) (by grind) (Rew.subst (#0 :> (#·.succ.succ))))⟩)
  let ψ₂' :=
    ψ₁'.rew (Rew.subst (#0 :> (#·.succ.succ)));
  obtain ⟨β, hβ⟩ := ih.bexs 𝚷 (φ := ψ₁ ⇜ (#0 :> (#·.succ.succ)))
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) (by
      exact ⟨ψ₂', by simpa [ψ₂', ψ₁] using
        (provable_iff_rew (T := T) (by grind) (Rew.subst (#0 :> (#·.succ.succ))))⟩)
  have hαiff := models_iff_of_provable_iff hα;
  have hβiff := models_iff_of_provable_iff hβ;
  obtain ⟨χ, hχ⟩ := ih.and 𝚷 ⟨α, provable_iff_refl (π := α)⟩ ⟨β, provable_iff_refl (π := β)⟩;
  have hχiff := models_iff_of_provable_iff hχ;
  use χ.sigma
  apply provable_iff_of_models_iff
  intro V _ _ e;
  . rw [val_sigma]
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance;
    have hα_eval : ∀ z : V, V ⊧/(z :> e) (↑α : ArithmeticSemisentence (n + 1)) ↔
        ∃ x ≤ z, V ⊧/(x :> e) φ₁ := fun z => by
      rw [← hαiff V (z :> e)];
      show V ⊧/(z :> e)
        ((φ₁ ⇜ (#0 :> (#·.succ.succ)) : ArithmeticSemisentence (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [Semiformula.eval_insert1, -Semiformula.eval_substs];
    have hβ_eval : ∀ z : V, V ⊧/(z :> e) (↑β : ArithmeticSemisentence (n + 1)) ↔
        ∃ x ≤ z, V ⊧/(x :> e) ψ₁ := fun z => by
      rw [← hβiff V (z :> e)];
      show V ⊧/(z :> e)
        ((ψ₁ ⇜ (#0 :> (#·.succ.succ)) : ArithmeticSemisentence (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [Semiformula.eval_insert1, -Semiformula.eval_substs];
    have hφiff' : V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) φ₁ := models_iff_sigmaInv hπ V e;
    have hψiff' : V ⊧/e ψ ↔ ∃ x, V ⊧/(x :> e) ψ₁ := models_iff_sigmaInv hρ V e;
    have hχ_eval : ∀ z : V, V ⊧/(z :> e) (↑χ : ArithmeticSemisentence (n + 1)) ↔
        V ⊧/(z :> e) (↑α : ArithmeticSemisentence (n + 1)) ∧
          V ⊧/(z :> e) (↑β : ArithmeticSemisentence (n + 1)) := by
      intro z
      exact (hχiff V (z :> e)).symm
    simp only [LogicalConnective.HomClass.map_and, Semiformula.eval_ex, hφiff', hψiff',
      hχ_eval, hα_eval, hβ_eval];
    constructor;
    . rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
      exact ⟨max x y, ⟨x, le_max_left x y, hx⟩, ⟨y, le_max_right x y, hy⟩⟩;
    . rintro ⟨z, ⟨x, _, hx⟩, ⟨y, _, hy⟩⟩;
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;

end ConnectiveStep

lemma closure_succ [𝗜𝚺 (s + 1) ⪯ T] (ih : Closure T s) : Closure T (s + 1) where
  ball := by
    intro Γ n φ t ht hφ;
    rcases Γ with _ | _;
    . exact ball_sigma_step ih ht hφ;
    . obtain ⟨π, hπ⟩ := hφ
      obtain ⟨χ, hχ⟩ := bexs_sigma_step ih ht
        ⟨π.neg, provable_iff_neg hπ⟩
      exact ⟨χ.neg, by simpa using provable_iff_neg hχ⟩
  bexs := by
    intro Γ n φ t ht hφ;
    rcases Γ with _ | _;
    . exact bexs_sigma_step ih ht hφ;
    . obtain ⟨π, hπ⟩ := hφ
      obtain ⟨χ, hχ⟩ := ball_sigma_step ih ht
        ⟨π.neg, provable_iff_neg hπ⟩
      exact ⟨χ.neg, by simpa using provable_iff_neg hχ⟩
  and := by
    intro Γ n φ ψ hφ hψ;
    rcases Γ with _ | _;
    . exact and_sigma_step ih hφ hψ;
    . obtain ⟨π, hπ⟩ := hφ
      obtain ⟨ρ, hρ⟩ := hψ
      obtain ⟨χ, hχ⟩ := or_sigma_step ih
        ⟨π.neg, provable_iff_neg hπ⟩ ⟨ρ.neg, provable_iff_neg hρ⟩
      exact ⟨χ.neg, by simpa [Semiformula.imp_eq] using provable_iff_neg hχ⟩
  or := by
    intro Γ n φ ψ hφ hψ;
    rcases Γ with _ | _;
    . exact or_sigma_step ih hφ hψ;
    . obtain ⟨π, hπ⟩ := hφ
      obtain ⟨ρ, hρ⟩ := hψ
      obtain ⟨χ, hχ⟩ := and_sigma_step ih
        ⟨π.neg, provable_iff_neg hπ⟩ ⟨ρ.neg, provable_iff_neg hρ⟩
      exact ⟨χ.neg, by simpa [Semiformula.imp_eq] using provable_iff_neg hχ⟩

lemma closure [𝗜𝚺 s ⪯ T] : Closure T s := by
  rename_i h;
  induction s generalizing h with
  | zero => exact closure_zero;
  | succ s ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) h;
    exact closure_succ ih;

section UnboundedQuantifier

variable {φ : ArithmeticSemisentence (n + 1)}

lemma exs [𝗜𝚺 s ⪯ T] (c : Closure T s)
    (hφ : ∃ π : Prenex 𝚺 (s + 1) Empty (n + 1), T ⊢ ∀¹* (φ 🡘 π.val)) :
  ∃ π : Prenex 𝚺 (s + 1) Empty n, T ⊢ ∀¹* ((∃¹ φ) 🡘 π.val) := by
  have : 𝗜𝚺₀ ⪯ T :=
    Entailment.WeakerThan.trans (ISigma_weakerThan_of_le (Nat.zero_le s)) inferInstance;
  obtain ⟨π, hπ⟩ := hφ
  set φ₁' := π.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 2) := ↑φ₁';
  let φ₂' :=
    φ₁'.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)));
  obtain ⟨α, hα⟩ := c.bexs 𝚷 (φ := φ₁ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)))
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) (by
      exact ⟨φ₂', by simpa [φ₂', φ₁] using
        (provable_iff_rew (T := T) (by grind)
        (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))⟩)
  obtain ⟨β, hβ⟩ := c.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) ⟨α, provable_iff_refl (π := α)⟩;
  have hαiff := models_iff_of_provable_iff hα;
  have hβiff := models_iff_of_provable_iff hβ;
  have hαiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 2) → V),
      V ⊧/e ((φ₁ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)) : ArithmeticSemisentence (n + 3)).bexsLTSucc
        (‘#1’ : ArithmeticSemiterm Empty (n + 2))) ↔
      V ⊧/e (↑α : ArithmeticSemisentence (n + 2)) :=
    hαiff;
  have hβiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 1) → V),
      V ⊧/e ((↑α : ArithmeticSemisentence (n + 2)).bexsLTSucc
        (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔
      V ⊧/e (↑β : ArithmeticSemisentence (n + 1)) :=
    hβiff;
  use β.sigma
  apply provable_iff_of_models_iff
  intro V _ _ e;
  . change V ⊧/e (∃¹ φ) ↔ V ⊧/e β.sigma.val;
    rw [val_sigma]
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance;
    have hαeval : ∀ y z : V, V ⊧/(y :> z :> e) (↑α : ArithmeticSemisentence (n + 2)) ↔
        ∃ x ≤ z, V ⊧/(x :> y :> e) φ₁ := by
      intro y z;
      rw [← hαiff' V (y :> z :> e)];
      simp [Semiformula.eval_insert2, -Semiformula.eval_substs];
    have hβeval : ∀ z : V, V ⊧/(z :> e) (↑β : ArithmeticSemisentence (n + 1)) ↔
        ∃ y ≤ z, V ⊧/(y :> z :> e) (↑α : ArithmeticSemisentence (n + 2)) := by
      intro z;
      rw [← hβiff' V (z :> e)];
      simp;
    have hφeval : ∀ y : V, V ⊧/(y :> e) φ ↔ ∃ x, V ⊧/(x :> y :> e) φ₁ := fun y =>
      models_iff_sigmaInv hπ V (y :> e);
    simp only [Semiformula.eval_ex, hφeval, hβeval, hαeval];
    constructor;
    . rintro ⟨y, x, hx⟩;
      exact ⟨max x y, y, le_max_right x y, x, le_max_left x y, hx⟩;
    . rintro ⟨z, y, -, x, -, hx⟩;
      exact ⟨y, x, hx⟩;

lemma all [𝗜𝚺 s ⪯ T] (c : Closure T s)
    (hφ : ∃ π : Prenex 𝚷 (s + 1) Empty (n + 1), T ⊢ ∀¹* (φ 🡘 π.val)) :
  ∃ π : Prenex 𝚷 (s + 1) Empty n, T ⊢ ∀¹* ((∀¹ φ) 🡘 π.val) := by
  obtain ⟨π, hπ⟩ := hφ
  obtain ⟨χ, hχ⟩ := exs c ⟨π.neg, provable_iff_neg hπ⟩
  exact ⟨χ.neg, by simpa using provable_iff_neg hχ⟩

end UnboundedQuantifier

end Prenex

open Prenex (ofΔ₀ closure exs all)

variable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {Γ : Polarity} {s n : ℕ}
  {φ : ArithmeticSemisentence n}

theorem hasPrenex (h : Hierarchy Γ s φ) [𝗜𝚺 s ⪯ T] :
    ∃ π : Prenex Γ s Empty n, T ⊢ ∀¹* (φ 🡘 π.val) := by
  rename_i hT;
  induction h generalizing hT with
  | verum Γ s n =>
    let φ₀ : 𝚺₀.Semisentence n := .mkSigma _ (Hierarchy.verum 𝚺 0 n)
    exact ⟨Prenex.ofΔ₀ φ₀ Γ s, Prenex.provable_iff_ofΔ₀ φ₀⟩
  | falsum Γ s n =>
    let φ₀ : 𝚺₀.Semisentence n := .mkSigma _ (Hierarchy.falsum 𝚺 0 n)
    exact ⟨Prenex.ofΔ₀ φ₀ Γ s, Prenex.provable_iff_ofΔ₀ φ₀⟩
  | rel Γ s r v =>
    let φ₀ : 𝚺₀.Semisentence _ := .mkSigma (.rel r v) (Hierarchy.rel 𝚺 0 r v)
    exact ⟨Prenex.ofΔ₀ φ₀ Γ s, Prenex.provable_iff_ofΔ₀ φ₀⟩
  | nrel Γ s r v =>
    let φ₀ : 𝚺₀.Semisentence _ := .mkSigma (.nrel r v) (Hierarchy.nrel 𝚺 0 r v)
    exact ⟨Prenex.ofΔ₀ φ₀ Γ s, Prenex.provable_iff_ofΔ₀ φ₀⟩
  | and _ _ ihp ihq =>
    exact closure.and _ ihp ihq;
  | or _ _ ihp ihq =>
    exact closure.or _ ihp ihq;
  | ball pos _ ih => exact closure.ball _ pos ih;
  | bexs pos _ ih => exact closure.bexs _ pos ih;
  | @exs s n φ _ ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact exs closure ih;
  | @all s n φ _ ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact all closure ih;
  | @sigma s n φ hp ih =>
    rcases s with _ | s;
    . let φ₀ : 𝚺₀.Semisentence (n + 1) := .mkSigma _ (Hierarchy.zero_iff.mp hp)
      let π := Prenex.ofΔ₀ φ₀ 𝚷 0
      exact ⟨π.sigma, Prenex.provable_iff_sigma (Prenex.provable_iff_ofΔ₀ φ₀)⟩
    . have : 𝗜𝚺 (s + 1) ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT
      obtain ⟨π, hπ⟩ := ih
      exact ⟨π.sigma, Prenex.provable_iff_sigma hπ⟩
  | @pi s n φ hp ih =>
    rcases s with _ | s;
    . let φ₀ : 𝚺₀.Semisentence (n + 1) := .mkSigma _ (Hierarchy.zero_iff.mp hp)
      let π := Prenex.ofΔ₀ φ₀ 𝚺 0
      exact ⟨π.pi, Prenex.provable_iff_pi (Prenex.provable_iff_ofΔ₀ φ₀)⟩
    . have : 𝗜𝚺 (s + 1) ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT
      obtain ⟨π, hπ⟩ := ih
      exact ⟨π.pi, Prenex.provable_iff_pi hπ⟩
  | @dummy_sigma s n φ hp ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    have : 𝗜𝚺 (s + 1) ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    obtain ⟨ψ, hψ⟩ := all closure ih
    exact ⟨ψ.altUp, Prenex.provable_iff_altUp hψ⟩
  | @dummy_pi s n φ hp ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    have : 𝗜𝚺 (s + 1) ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    obtain ⟨ψ, hψ⟩ := exs closure ih
    exact ⟨ψ.altUp, Prenex.provable_iff_altUp hψ⟩

variable (T : ArithmeticTheory) {Γ : Polarity} {s n : ℕ} {φ : ArithmeticSemisentence n} [𝗜𝚺 s ⪯ T]

theorem exists_matrix_provable (h : Hierarchy Γ s φ) :
  ∃ φ₀ : 𝚺₀.Semisentence (n + s), T ⊢ ∀¹* (φ 🡘 φ₀.val.toPrenex Γ s) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := Entailment.WeakerThan.trans
    (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀) (ISigma_weakerThan_of_le_trans (by omega) ‹𝗜𝚺 s ⪯ T›);
  obtain ⟨π, hπ⟩ := hasPrenex (T := T) h;
  exact ⟨π.matrix, by simpa [Prenex.val] using hπ⟩;

end Arithmetic

end LO.FirstOrder
