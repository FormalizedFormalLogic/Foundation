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

def neg (π : Prenex Γ s ξ n) : Prenex Γ.alt s ξ n := ⟨.mkSigma (∼π.matrix.val) π.matrix.sigma_prop.neg.of_zero⟩

def rew (π : Prenex Γ s ξ₁ n₁) (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) : Prenex Γ s ξ₂ n₂ := ⟨π.matrix.rew (ω.qpow s)⟩

def sigma (π : Prenex 𝚷 s ξ (n + 1)) : Prenex 𝚺 (s + 1) ξ n := ⟨π.matrix.rew (Rew.castLE (Nat.succ_add n s).le)⟩

def pi (π : Prenex 𝚺 s ξ (n + 1)) : Prenex 𝚷 (s + 1) ξ n := ⟨π.matrix.rew (Rew.castLE (Nat.succ_add n s).le)⟩

def sigmaInv (π : Prenex 𝚺 (s + 1) ξ n) : Prenex 𝚷 s ξ (n + 1) := ⟨π.matrix.rew (Rew.castLE (Nat.succ_add n s).ge)⟩

def piInv (π : Prenex 𝚷 (s + 1) ξ n) : Prenex 𝚺 s ξ (n + 1) := ⟨π.matrix.rew (Rew.castLE (Nat.succ_add n s).ge)⟩

def altUp (π : Prenex Γ s ξ n) : Prenex Γ.alt (s + 1) ξ n := by
  rcases Γ with _ | _
  . exact (π.rew Rew.bShift).pi
  . exact (π.rew Rew.bShift).sigma

def ofΔ₀ (φ : 𝚺₀.Semiformula ξ n) : (Γ : Polarity) → (s : ℕ) → Prenex Γ s ξ n
  | Γ, 0     => ⟨φ⟩
  | Γ, s + 1 => by simpa using altUp (ofΔ₀ φ Γ.alt s)

def verum : Prenex Γ s ξ n := ofΔ₀ (.mkSigma ⊤ (Hierarchy.verum 𝚺 0 n)) Γ s

def falsum : Prenex Γ s ξ n := ofΔ₀ (.mkSigma ⊥ (Hierarchy.falsum 𝚺 0 n)) Γ s

def rel (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm ξ n) : Prenex Γ s ξ n :=
  ofΔ₀ (.mkSigma (.rel r v) (Hierarchy.rel 𝚺 0 r v)) Γ s

def nrel (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm ξ n) : Prenex Γ s ξ n :=
  ofΔ₀ (.mkSigma (.nrel r v) (Hierarchy.nrel 𝚺 0 r v)) Γ s


@[simp, grind .]
lemma val_hierarchy {π : Prenex Γ s ξ n} : Hierarchy Γ s π.val := by
  change Hierarchy Γ s (π.matrix.val.toPrenex Γ s)
  simpa only [Nat.zero_add] using Hierarchy.toPrenex (Γ := Γ) (j := 0) π.matrix.sigma_prop.of_zero

@[simp, grind .]
lemma val_deltaZero {π : Prenex Γ 0 ξ n} : Hierarchy 𝚺 0 π.val := π.matrix.sigma_prop

@[simp, grind .]
lemma val_neg (π : Prenex Γ s ξ n) : π.neg.val = ∼π.val := by simp [neg, val]

@[simp, grind .]
lemma val_rew (π : Prenex Γ s ξ₁ n₁) (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) :
  (π.rew ω).val = ω ▹ π.val := by
  simp [val, rew]

@[simp, grind .]
lemma val_sigma {π : Prenex 𝚷 s ξ (n + 1)} : π.sigma.val = ∃¹ π.val := by
  simp [val, sigma, Rewriting.quantItr_succ_smul_castLE]

@[simp, grind .]
lemma val_pi {π : Prenex 𝚺 s ξ (n + 1)} : π.pi.val = ∀¹ π.val := by
  simp [val, pi, Rewriting.quantItr_succ_smul_castLE]

@[simp, grind .]
lemma val_sigmaInv {π : Prenex 𝚺 (s + 1) ξ n} : π.val = ∃¹ π.sigmaInv.val := by
  unfold val sigmaInv
  simp only [HierarchySymbol.Semiformula.val_rew]
  rw [← Polarity.quant_sigma, ← Polarity.alt_sigma, ← Rewriting.quantItr_succ_smul_castLE,
    ← TransitiveRewriting.comp_app]
  simp



@[simp, grind .]
lemma val_piInv {π : Prenex 𝚷 (s + 1) ξ n} : π.val = ∀¹ π.piInv.val := by
  unfold val piInv
  simp only [HierarchySymbol.Semiformula.val_rew]
  rw [← Polarity.quant_pi, ← Polarity.alt_pi, ← Rewriting.quantItr_succ_smul_castLE,
    ← TransitiveRewriting.comp_app]
  simp



lemma models_altUp (π : Prenex Γ s Empty n) (V : Type*) [ORingStructure V] (e : Fin n → V) :
  V ⊧/e π.altUp.val ↔ V ⊧/e π.val := by
  rcases Γ <;> simp [
    Polarity.eq_sigma, Polarity.alt_sigma, altUp,
    -val_piInv, -val_sigmaInv,
    Semiformula.eval_all, Nat.succ_eq_add_one
  ]

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

variable {T : ArithmeticTheory}

lemma provable_iff_sigmaInv {π : Prenex 𝚺 (s + 1) Empty n} (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) :
  T ⊢ ∀¹* (φ 🡘 ∃¹ π.sigmaInv.val) := π.val_sigmaInv ▸ hπ

lemma provable_iff_piInv {π : Prenex 𝚷 (s + 1) Empty n} (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) :
  T ⊢ ∀¹* (φ 🡘 ∀¹ π.piInv.val) := π.val_piInv ▸ hπ

variable [𝗘𝗤 ℒₒᵣ ⪯ T]

@[simp, grind .]
lemma provable_iff_refl {π : Prenex Γ s Empty n} : T ⊢ ∀¹* (π.val 🡘 π.val) :=
  provable_iff_of_models_iff fun _ _ _ _ ↦ Iff.rfl

lemma provable_iff_neg {π : Prenex Γ s Empty n} (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) :
  T ⊢ ∀¹* ((∼φ) 🡘 π.neg.val) := by
  apply provable_iff_of_models_iff
  intro V _ _ e;
  simpa [val_neg] using not_congr (models_iff_of_provable_iff hπ V e)

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

lemma provable_iff_verum : T ⊢ ∀¹* (⊤ 🡘 (verum : Prenex Γ s Empty n).val) :=
  provable_iff_ofΔ₀ (.mkSigma ⊤ (by simp))

lemma provable_iff_falsum : T ⊢ ∀¹* (⊥ 🡘 (falsum : Prenex Γ s Empty n).val) :=
  provable_iff_ofΔ₀ (.mkSigma ⊥ (by simp))

lemma provable_iff_rel (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm Empty n) :
  T ⊢ ∀¹* (Semiformula.rel r v 🡘 (rel r v : Prenex Γ s Empty n).val) :=
  provable_iff_ofΔ₀ (.mkSigma (.rel r v) (by simp))

lemma provable_iff_nrel (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm Empty n) :
  T ⊢ ∀¹* (Semiformula.nrel r v 🡘 (nrel r v : Prenex Γ s Empty n).val) :=
  provable_iff_ofΔ₀ (.mkSigma (.nrel r v) (by simp))

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
  ball {Γ : Polarity} {n : ℕ} {φ} (u) (φ' : Prenex Γ s Empty (n + 1)) :
    T ⊢ ∀¹* (φ 🡘 φ'.val) →
    T ⊢ ∀¹* (φ.ballLT u 🡘 (C.ball u φ').val)
  bexs {Γ : Polarity} {n : ℕ} {φ} (u) (φ' : Prenex Γ s Empty (n + 1)) :
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

def bexsSigma (C : ClosureData s) (u : ArithmeticSemiterm Empty n)
    (π : Prenex 𝚺 (s + 1) Empty (n + 1)) : Prenex 𝚺 (s + 1) Empty n :=
  (C.bexs (Rew.bShift u) (π.sigmaInv.rew (Rew.subst (#1 :> #0 :> (#·.succ.succ))))).sigma

def ballSigma (C : ClosureData s) (u : ArithmeticSemiterm Empty n)
    (π : Prenex 𝚺 (s + 1) Empty (n + 1)) : Prenex 𝚺 (s + 1) Empty n :=
  (C.ball (Rew.bShift u)
    (C.bexs ‘#1 + 1’ (π.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma

def orSigma (C : ClosureData s) (π ρ : Prenex 𝚺 (s + 1) Empty n) : Prenex 𝚺 (s + 1) Empty n :=
  (C.or π.sigmaInv ρ.sigmaInv).sigma

def andSigma (C : ClosureData s) (π ρ : Prenex 𝚺 (s + 1) Empty n) : Prenex 𝚺 (s + 1) Empty n :=
  (C.and (C.bexs ‘#0 + 1’ (π.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))
         (C.bexs ‘#0 + 1’ (ρ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))).sigma

def succ (C : ClosureData s) : ClosureData (s + 1) where
  ball {Γ} _ u π :=
    match Γ with
    | 𝚺 => C.ballSigma u π
    | 𝚷 => (C.bexsSigma u π.neg).neg
  bexs {Γ} _ u π :=
    match Γ with
    | 𝚺 => C.bexsSigma u π
    | 𝚷 => (C.ballSigma u π.neg).neg
  and {Γ} _ π ρ :=
    match Γ with
    | 𝚺 => C.andSigma π ρ
    | 𝚷 => (C.orSigma π.neg ρ.neg).neg
  or {Γ} _ π ρ :=
    match Γ with
    | 𝚺 => C.orSigma π ρ
    | 𝚷 => (C.andSigma π.neg ρ.neg).neg

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

lemma bexsSigma_correct {C : ClosureData s} (hC : C.Correct T) (u : ArithmeticSemiterm Empty n)
  (π : Prenex 𝚺 (s + 1) Empty (n + 1)) (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) :
  T ⊢ ∀¹* (φ.bexsLT u 🡘 (C.bexsSigma u π).val) := by
  set φ₁' := π.sigmaInv;
  set φ₁ := φ₁'.val;
  set v := #1 :> #0 :> fun i => #(i.succ.succ) with hv;
  set φ₂ := Rew.subst v ▹ φ₁;
  let φ₂' := φ₁'.rew (Rew.subst v);
  have hχ := hC.bexs (φ := φ₂) (Rew.bShift u) φ₂'
    (by simpa [φ₂', φ₂, φ₁] using (provable_iff_rew (T := T) (by grind) (Rew.subst v)));
  have hχiff := models_iff_of_provable_iff hχ;
  have hχiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 1) → V),
      V ⊧/e (φ₂.bexsLT (Rew.bShift u)) ↔ V ⊧/e (C.bexs (Rew.bShift u) φ₂').val :=
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

lemma ballSigma_correct [𝗜𝚺 (s + 1) ⪯ T] {C : ClosureData s} (hC : C.Correct T)
    {φ : ArithmeticSemisentence (n + 1)} (u : ArithmeticSemiterm Empty n)
    (π : Prenex 𝚺 (s + 1) Empty (n + 1)) (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) :
    T ⊢ ∀¹* (φ.ballLT u 🡘 (C.ballSigma u π).val) := by
  set φ₁' := π.sigmaInv;
  set φ₁ := φ₁'.val;
  let φ₂' := φ₁'.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)));
  let α' := C.bexs (‘#1 + 1’) φ₂';
  have hα := hC.bexs (φ := φ₁ ⇜ (#0 :> #1 :> (#·.succ.succ.succ))) (‘#1 + 1’) φ₂'
    (by simpa [φ₂', φ₁] using
      (provable_iff_rew (T := T) (by grind) (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))));
  have hαiff := models_iff_of_provable_iff hα;
  have hδ := hC.ball (Rew.bShift u) α' hα;
  have hδiff := models_iff_of_provable_iff hδ;
  show T ⊢ ∀¹* (φ.ballLT u 🡘 (C.ball (Rew.bShift u) α').sigma.val);
  apply provable_iff_of_models_iff
  intro V _ _ e;
  . rw [val_sigma]
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := models_of_subtheory (T := 𝗜𝚺 (s + 1)) (U := T) inferInstance;
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s + 1);
    have hαeval : ∀ x w : V,
        V ⊧/(x :> w :> e) α'.val ↔ ∃ y ≤ w, V ⊧/(y :> x :> e) φ₁ := by
      intro x w;
      rw [← hαiff V (x :> w :> e)];
      simp [Semiformula.eval_insert2, Arithmetic.lt_succ_iff_le, -Semiformula.eval_substs];
    have hδeval : ∀ w : V,
        V ⊧/(w :> e) (C.ball (Rew.bShift u) α').val ↔
          ∀ x < u.valb e, ∃ y ≤ w, V ⊧/(y :> x :> e) φ₁ := by
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
    show V ⊧/e (φ.ballLT u) ↔ V ⊧/e (∃¹ (C.ball (Rew.bShift u) α').val);
    simp only [Semiformula.eval_ballLT, Semiformula.eval_ex, hδeval, hφeval];
    constructor;
    . intro h;
      have hθ : Hierarchy 𝚺 (s + 1) φ₁ := φ₁'.val_hierarchy.accum 𝚺;
      exact sigma_exists_bound_witness hθ e (u.valb e) h;
    . rintro ⟨w, hw⟩ x hx;
      obtain ⟨y, -, hy⟩ := hw x hx;
      exact ⟨y, hy⟩;

lemma orSigma_correct {C : ClosureData s} (hC : C.Correct T)
  (π ρ : Prenex 𝚺 (s + 1) Empty n)
  (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) (hρ : T ⊢ ∀¹* (ψ 🡘 ρ.val)) :
  T ⊢ ∀¹* ((φ ⋎ ψ) 🡘 (C.orSigma π ρ).val) := by
  set φ₁' := π.sigmaInv;
  set ψ₁' := ρ.sigmaInv;
  set φ₁ := φ₁'.val;
  set ψ₁ := ψ₁'.val;
  have hχ := hC.or φ₁' ψ₁' provable_iff_refl provable_iff_refl;
  have hχiff := models_iff_of_provable_iff hχ;
  show T ⊢ ∀¹* ((φ ⋎ ψ) 🡘 (C.or φ₁' ψ₁').sigma.val);
  apply provable_iff_of_models_iff;
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

lemma andSigma_correct [𝗜𝚺 (s + 1) ⪯ T] {C : ClosureData s} (hC : C.Correct T)
  (π ρ : Prenex 𝚺 (s + 1) Empty n)  (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) (hρ : T ⊢ ∀¹* (ψ 🡘 ρ.val)) :
  T ⊢ ∀¹* ((φ ⋏ ψ) 🡘 (C.andSigma π ρ).val) := by
  have : 𝗜𝚺₀ ⪯ T := Entailment.WeakerThan.trans (ISigma_weakerThan_of_le (by omega)) ‹𝗜𝚺(s + 1) ⪯ T›;
  set φ₁' := π.sigmaInv;
  set ψ₁' := ρ.sigmaInv;
  set φ₁ := φ₁'.val;
  set ψ₁ := ψ₁'.val;
  let φ₂' := φ₁'.rew (Rew.subst (#0 :> (#·.succ.succ)));
  let α' := C.bexs (‘#0 + 1’) φ₂';
  have hα := hC.bexs (φ := φ₁ ⇜ (#0 :> (#·.succ.succ))) (‘#0 + 1’) φ₂'
    (by simpa [φ₂', φ₁] using
      (provable_iff_rew (T := T) (by grind) (Rew.subst (#0 :> (#·.succ.succ)))));
  let ψ₂' := ψ₁'.rew (Rew.subst (#0 :> (#·.succ.succ)));
  let β' := C.bexs (‘#0 + 1’) ψ₂';
  have hβ := hC.bexs (φ := ψ₁ ⇜ (#0 :> (#·.succ.succ))) (‘#0 + 1’) ψ₂'
    (by simpa [ψ₂', ψ₁] using
      (provable_iff_rew (T := T) (by grind) (Rew.subst (#0 :> (#·.succ.succ)))));
  have hαiff := models_iff_of_provable_iff hα;
  have hβiff := models_iff_of_provable_iff hβ;
  have hχ := hC.and α' β' provable_iff_refl provable_iff_refl;
  have hχiff := models_iff_of_provable_iff hχ;
  show T ⊢ ∀¹* ((φ ⋏ ψ) 🡘 (C.and α' β').sigma.val);
  apply provable_iff_of_models_iff
  intro V _ _ e;
  . rw [val_sigma]
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance;
    have hα_eval : ∀ z : V, V ⊧/(z :> e) α'.val ↔ ∃ x ≤ z, V ⊧/(x :> e) φ₁ := fun z => by
      rw [← hαiff V (z :> e)];
      show V ⊧/(z :> e)
        ((φ₁ ⇜ (#0 :> (#·.succ.succ)) : ArithmeticSemisentence (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [Semiformula.eval_insert1, -Semiformula.eval_substs];
    have hβ_eval : ∀ z : V, V ⊧/(z :> e) β'.val ↔ ∃ x ≤ z, V ⊧/(x :> e) ψ₁ := fun z => by
      rw [← hβiff V (z :> e)];
      show V ⊧/(z :> e)
        ((ψ₁ ⇜ (#0 :> (#·.succ.succ)) : ArithmeticSemisentence (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [Semiformula.eval_insert1, -Semiformula.eval_substs];
    have hφiff' : V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) φ₁ := models_iff_sigmaInv hπ V e;
    have hψiff' : V ⊧/e ψ ↔ ∃ x, V ⊧/(x :> e) ψ₁ := models_iff_sigmaInv hρ V e;
    have hχ_eval : ∀ z : V,
        V ⊧/(z :> e) (C.and α' β').val ↔ V ⊧/(z :> e) α'.val ∧ V ⊧/(z :> e) β'.val := by
      intro z
      exact (hχiff V (z :> e)).symm
    simp only [LogicalConnective.HomClass.map_and, Semiformula.eval_ex, hφiff', hψiff',
      hχ_eval, hα_eval, hβ_eval];
    constructor;
    . rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
      exact ⟨max x y, ⟨x, le_max_left x y, hx⟩, ⟨y, le_max_right x y, hy⟩⟩;
    . rintro ⟨z, ⟨x, _, hx⟩, ⟨y, _, hy⟩⟩;
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;

lemma succ_correct [𝗜𝚺 (s + 1) ⪯ T] {C : ClosureData s} (hC : C.Correct T) : C.succ.Correct T where
  ball {Γ} {n} {φ} u π hπ := by
    rcases Γ with _ | _;
    . exact ballSigma_correct hC u π hπ;
    . have := bexsSigma_correct hC u π.neg (provable_iff_neg hπ);
      show T ⊢ ∀¹* (φ.ballLT u 🡘 (C.bexsSigma u π.neg).neg.val);
      apply provable_iff_of_models_iff;
      intro V _ _ e;
      have hthis := models_iff_of_provable_iff this V e;
      simp only [Semiformula.eval_ballLT, Semiformula.eval_bexsLT, val_neg,
        LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq] at hthis ⊢;
      grind;
  bexs {Γ} {n} {φ} u π hπ := by
    rcases Γ with _ | _;
    . exact bexsSigma_correct hC u π hπ;
    . have := ballSigma_correct hC u π.neg (provable_iff_neg hπ);
      show T ⊢ ∀¹* (φ.bexsLT u 🡘 (C.ballSigma u π.neg).neg.val);
      apply provable_iff_of_models_iff;
      intro V _ _ e;
      have hthis := models_iff_of_provable_iff this V e;
      simp only [Semiformula.eval_ballLT, Semiformula.eval_bexsLT, val_neg,
        LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq] at hthis ⊢;
      grind;
  and {Γ} {n} {φ} {ψ} π ρ hπ hρ := by
    rcases Γ with _ | _;
    . exact andSigma_correct hC π ρ hπ hρ;
    . have := orSigma_correct hC π.neg ρ.neg (provable_iff_neg hπ) (provable_iff_neg hρ);
      show T ⊢ ∀¹* ((φ ⋏ ψ) 🡘 (C.orSigma π.neg ρ.neg).neg.val);
      apply provable_iff_of_models_iff;
      intro V _ _ e;
      have hthis := models_iff_of_provable_iff this V e;
      simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_and,
        LogicalConnective.HomClass.map_or, LogicalConnective.Prop.neg_eq,
        LogicalConnective.Prop.or_eq, LogicalConnective.Prop.and_eq] at hthis ⊢;
      tauto;
  or {Γ} {n} {φ} {ψ} π ρ hπ hρ := by
    rcases Γ with _ | _;
    . exact orSigma_correct hC π ρ hπ hρ;
    . have := andSigma_correct hC π.neg ρ.neg (provable_iff_neg hπ) (provable_iff_neg hρ);
      show T ⊢ ∀¹* ((φ ⋎ ψ) 🡘 (C.andSigma π.neg ρ.neg).neg.val);
      apply provable_iff_of_models_iff;
      intro V _ _ e;
      have hthis := models_iff_of_provable_iff this V e;
      simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_and,
        LogicalConnective.HomClass.map_or, LogicalConnective.Prop.neg_eq,
        LogicalConnective.Prop.or_eq, LogicalConnective.Prop.and_eq] at hthis ⊢;
      tauto;

end ClosureData

def closureData : (s : ℕ) → ClosureData s
  | 0 => .zero
  | s + 1 => (closureData s).succ

def exs (π : Prenex 𝚺 (s + 1) Empty (n + 1)) : Prenex 𝚺 (s + 1) Empty n :=
  letI φ₁' := π.sigmaInv;
  letI φ₂' := φ₁'.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)));
  letI α   := (closureData s).bexs (‘#1 + 1’) φ₂';
  letI β   := (closureData s).bexs (‘#0 + 1’) α;
  β.sigma

def all (π : Prenex 𝚷 (s + 1) Empty (n + 1)) : Prenex 𝚷 (s + 1) Empty n := (exs π.neg).neg

lemma closureData_correct [𝗜𝚺 s ⪯ T] : (closureData s).Correct T := by
  rename_i h;
  induction s generalizing h with
  | zero => exact ClosureData.zero_correct T;
  | succ s ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) h;
    exact ClosureData.succ_correct ih;

lemma exs_correct [𝗜𝚺 s ⪯ T] {φ : ArithmeticSemisentence (n + 1)} {π : Prenex 𝚺 (s + 1) Empty (n + 1)}
    (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) : T ⊢ ∀¹* ((∃¹ φ) 🡘 (exs π).val) := by
  have : 𝗜𝚺₀ ⪯ T := Entailment.WeakerThan.trans (ISigma_weakerThan_of_le (Nat.zero_le s)) inferInstance;
  set φ₁' := π.sigmaInv;
  set φ₁ := φ₁'.val;
  let φ₂' := φ₁'.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)));
  let α := (closureData s).bexs (‘#1 + 1’) φ₂';
  have hα : T ⊢ ∀¹* ((φ₁ ⇜ (#0 :> #1 :> (#·.succ.succ.succ))).bexsLT (‘#1 + 1’) 🡘 α.val) :=
    closureData_correct.bexs (φ := φ₁ ⇜ (#0 :> #1 :> (#·.succ.succ.succ))) (‘#1 + 1’) φ₂'
      (by simpa [φ₂', φ₁] using
        (provable_iff_rew (T := T) (by grind)
        (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))));
  let β := (closureData s).bexs (‘#0 + 1’) α;
  have hβ : T ⊢ ∀¹* ((α.val).bexsLT (‘#0 + 1’) 🡘 β.val) := closureData_correct.bexs (‘#0 + 1’) α provable_iff_refl;
  have hαiff := models_iff_of_provable_iff hα;
  have hβiff := models_iff_of_provable_iff hβ;
  unfold exs;
  apply provable_iff_of_models_iff
  intro V _ _ e;
  . change V ⊧/e (∃¹ φ) ↔ V ⊧/e β.sigma.val;
    rw [val_sigma]
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance;
    have hαeval : ∀ y z : V, V ⊧/(y :> z :> e) α.val ↔
        ∃ x ≤ z, V ⊧/(x :> y :> e) φ₁ := by
      intro y z;
      rw [← hαiff V (y :> z :> e)];
      simp [Semiformula.eval_bexsLT, Semiformula.eval_insert2, Arithmetic.lt_succ_iff_le,
        -Semiformula.eval_substs];
    have hβeval : ∀ z : V, V ⊧/(z :> e) β.val ↔
        ∃ y ≤ z, V ⊧/(y :> z :> e) α.val := by
      intro z;
      rw [← hβiff V (z :> e)];
      simp [Semiformula.eval_bexsLT, Arithmetic.lt_succ_iff_le];
    have hφeval : ∀ y : V, V ⊧/(y :> e) φ ↔ ∃ x, V ⊧/(x :> y :> e) φ₁ := fun y =>
      models_iff_sigmaInv hπ V (y :> e);
    simp only [Semiformula.eval_ex, hφeval, hβeval, hαeval];
    constructor;
    . rintro ⟨y, x, hx⟩;
      exact ⟨max x y, y, le_max_right x y, x, le_max_left x y, hx⟩;
    . rintro ⟨z, y, -, x, -, hx⟩;
      exact ⟨y, x, hx⟩;

lemma all_correct [𝗜𝚺 s ⪯ T] {φ : ArithmeticSemisentence (n + 1)} {π : Prenex 𝚷 (s + 1) Empty (n + 1)}
    (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) : T ⊢ ∀¹* ((∀¹ φ) 🡘 (all π).val) := by
  unfold all;
  simpa using provable_iff_neg $ exs_correct (provable_iff_neg hπ);

end Prenex

open Prenex (ofΔ₀ closureData_correct)

variable (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] {Γ : Polarity} {s n : ℕ} {φ : ArithmeticSemisentence n}

theorem exists_prenex_of_hierarchy (h : Hierarchy Γ s φ) [𝗜𝚺 s ⪯ T] : ∃ π : Prenex Γ s Empty n, T ⊢ ∀¹* (φ 🡘 π.val) := by
  rename_i hT;
  induction h generalizing hT with
  | verum Γ s n => exact ⟨.verum, Prenex.provable_iff_verum⟩;
  | falsum Γ s n => exact ⟨.falsum, Prenex.provable_iff_falsum⟩;
  | rel Γ s r v => exact ⟨.rel r v, Prenex.provable_iff_rel r v⟩;
  | nrel Γ s r v => exact ⟨.nrel r v, Prenex.provable_iff_nrel r v⟩;
  | and _ _ ihφ ihψ =>
    obtain ⟨φ', hφ⟩ := ihφ;
    obtain ⟨ψ', hψ⟩ := ihψ;
    exact ⟨_, closureData_correct.and φ' ψ' hφ hψ⟩;
  | or _ _ ihφ ihψ =>
    obtain ⟨φ', hφ⟩ := ihφ;
    obtain ⟨ψ', hψ⟩ := ihψ;
    exact ⟨_, closureData_correct.or φ' ψ' hφ hψ⟩;
  | ball pos _ ih =>
    obtain ⟨u, rfl⟩ := Rew.positive_iff.mp pos;
    obtain ⟨π, hπ⟩ := ih;
    exact ⟨_, closureData_correct.ball u π hπ⟩;
  | bexs pos _ ih =>
    obtain ⟨u, rfl⟩ := Rew.positive_iff.mp pos;
    obtain ⟨π, hπ⟩ := ih;
    exact ⟨_, closureData_correct.bexs u π hπ⟩;
  | @exs s n φ _ ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    obtain ⟨π, hπ⟩ := ih;
    use π.exs;
    exact Prenex.exs_correct hπ;
  | @all s n φ _ ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    obtain ⟨π, hπ⟩ := ih;
    use π.all;
    exact Prenex.all_correct hπ;
  | @sigma s n φ hp ih =>
    rcases s with _ | s;
    . let φ₀ : 𝚺₀.Semisentence (n + 1) := .mkSigma _ (Hierarchy.zero_iff.mp hp)
      exact ⟨_, Prenex.provable_iff_sigma (Prenex.provable_iff_ofΔ₀ φ₀)⟩
    . have : 𝗜𝚺 (s + 1) ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT
      obtain ⟨π, hπ⟩ := ih
      exact ⟨_, Prenex.provable_iff_sigma hπ⟩
  | @pi s n φ hp ih =>
    rcases s with _ | s;
    . let φ₀ : 𝚺₀.Semisentence (n + 1) := .mkSigma _ (Hierarchy.zero_iff.mp hp)
      exact ⟨_, Prenex.provable_iff_pi (Prenex.provable_iff_ofΔ₀ φ₀)⟩
    . have : 𝗜𝚺 (s + 1) ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT
      obtain ⟨π, hπ⟩ := ih
      exact ⟨_, Prenex.provable_iff_pi hπ⟩
  | @dummy_sigma s n φ hp ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    have : 𝗜𝚺 (s + 1) ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    obtain ⟨_, hπ⟩ := ih
    exact ⟨_, Prenex.provable_iff_altUp (Prenex.all_correct hπ)⟩
  | @dummy_pi s n φ hp ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    have : 𝗜𝚺 (s + 1) ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    obtain ⟨_, hπ⟩ := ih
    exact ⟨_, Prenex.provable_iff_altUp (Prenex.exs_correct hπ)⟩

variable (T : ArithmeticTheory) {Γ : Polarity} {s n : ℕ} {φ : ArithmeticSemisentence n} [𝗜𝚺 s ⪯ T]

theorem exists_matrix_provable (h : Hierarchy Γ s φ) :
  ∃ φ₀ : 𝚺₀.Semisentence (n + s), T ⊢ ∀¹* (φ 🡘 φ₀.val.toPrenex Γ s) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀) (ISigma_weakerThan_of_le_trans (by omega) ‹𝗜𝚺 s ⪯ T›);
  obtain ⟨_, hπ⟩ := exists_prenex_of_hierarchy T h;
  exact ⟨_, by simpa [Prenex.val] using hπ⟩;

end Arithmetic

end LO.FirstOrder
