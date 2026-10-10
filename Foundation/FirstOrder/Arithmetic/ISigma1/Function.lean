module

public import Foundation.FirstOrder.Arithmetic.Function.Basic
public import Foundation.FirstOrder.Arithmetic.HFS.PRF
public import Foundation.Vorspiel.List.Vector
public import Mathlib.Computability.Primrec.List

/-!
# Primitive recursive functions are `𝗜𝚺₁`-provably total

The graph of a primitive recursive function is assembled by composition and primitive recursion
along a derivation of its primitive recursiveness, and `𝗜𝚺₁` proves it functional.

## References

- [HP98, Theorem I.1.54, Lemma I.1.55]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

namespace Arithmetic

open ArithmeticTheory Bounding.HierarchySymbol

inductive PrimrecScheme : ∀ {n}, (List.Vector ℕ n → ℕ) → Type
  | zero : PrimrecScheme (n := 0) fun _ => 0
  | succ : PrimrecScheme (n := 1) fun v => v.head + 1
  | get {n} (i : Fin n) : PrimrecScheme fun v => v.get i
  | comp {m n f} (g : Fin n → List.Vector ℕ m → ℕ) :
      PrimrecScheme f → (∀ i, PrimrecScheme (g i)) →
      PrimrecScheme fun a => f (List.Vector.ofFn fun i => g i a)
  | prec {n f g} :
      PrimrecScheme (n := n) f → PrimrecScheme (n := n + 2) g →
      PrimrecScheme fun v : List.Vector ℕ (n + 1) =>
        v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)

lemma PrimrecScheme.nonempty {n} {f : List.Vector ℕ n → ℕ} (hf : Nat.Primrec' f) :
    Nonempty (PrimrecScheme f) := by
  induction hf with
  | zero => exact ⟨.zero⟩
  | succ => exact ⟨.succ⟩
  | get i => exact ⟨.get i⟩
  | comp g _ _ ihf ihg =>
    obtain ⟨pf⟩ := ihf
    exact ⟨.comp g pf fun i ↦ (ihg i).some⟩
  | prec _ _ ihf ihg =>
    obtain ⟨pf⟩ := ihf
    obtain ⟨pg⟩ := ihg
    exact ⟨.prec pf pg⟩

def precBlueprint {n : ℕ} (ψ : 𝚺ᴬ₁.Semisentence (n + 1)) (χ : 𝚺ᴬ₁.Semisentence (n + 3)) :
    PR.Blueprint n where
  zero := ψ
  succ := χ.rew (Rew.subst (#0 :> #2 :> #1 :> (#·.succ.succ.succ)))

def precConstruction {n : ℕ} {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {ψ : 𝚺ᴬ₁.Semisentence (n + 1)} {χ : 𝚺ᴬ₁.Semisentence (n + 3)}
    {f : (Fin n → V) → V} {g : (Fin (n + 2) → V) → V}
    (hf : 𝚺ᴬ₁.DefinedFunction f ψ) (hg : 𝚺ᴬ₁.DefinedFunction g χ) :
    PR.Construction V (precBlueprint ψ χ) where
  zero := f
  succ := fun v i z ↦ g (i :> z :> v)
  zero_defined := hf
  succ_defined := .mk fun v ↦ by
    simp [precBlueprint, Semiformula.eval_rew, Empty.eq_elim, hg.iff, Matrix.comp_vecCons']

def PrimrecScheme.graph {n : ℕ} {f : List.Vector ℕ n → ℕ} :
    PrimrecScheme f → 𝚺ᴬ₁.Semisentence (n + 1)
  | .zero => .mkSigma “y. y = 0”
  | .succ => .mkSigma “y x. y = x + 1”
  | .get i => (.mkSigma “y x. y = x” : 𝚺ᴬ₁.Semisentence 2).rew (Rew.subst ![#0, #i.succ])
  | .comp _ pf pg => compGraph pf.graph fun i ↦ (pg i).graph
  | .prec pf pg => (precBlueprint pf.graph pg.graph).resultDef

open ProvablyFunctionalVia in
theorem PrimrecScheme.provablyFunctionalVia_graph {n : ℕ} {f : List.Vector ℕ n → ℕ}
    (p : PrimrecScheme f) : 𝗜𝚺₁.ProvablyFunctionalVia (fun v ↦ f (.ofFn v)) p.graph := by
  induction p with
  | zero =>
    have h (V : Type) [ORingStructure V] :
        𝚺ᴬ₁.DefinedFunction (fun _ : Fin 0 → V ↦ 0) (.mkSigma “y. y = 0”) :=
      .mk fun _ ↦ by simp
    exact of_models (h ℕ) fun V _ _ ↦ ⟨_, h V⟩
  | succ =>
    have h (V : Type) [ORingStructure V] :
        𝚺ᴬ₁.DefinedFunction (fun v : Fin 1 → V ↦ v 0 + 1) (.mkSigma “y x. y = x + 1”) :=
      .mk fun _ ↦ by simp
    exact of_models ((h ℕ).of_eq (by simp)) fun V _ _ ↦ ⟨_, h V⟩
  | @get n i =>
    have h (V : Type) [ORingStructure V] :
        𝚺ᴬ₁.DefinedFunction (fun v : Fin n → V ↦ v i)
          ((.mkSigma “y x. y = x” : 𝚺ᴬ₁.Semisentence 2).rew (Rew.subst ![#0, #i.succ])) :=
      .mk fun _ ↦ by simp
    exact of_models ((h ℕ).of_eq (by simp)) fun V _ _ ↦ ⟨_, h V⟩
  | comp g _ _ ihf ihg =>
    exact of_models ((definedFunction_compGraph ihf.defined fun i ↦ (ihg i).defined).of_eq
      (by simp)) fun V _ _ ↦ by
        obtain ⟨G, hG⟩ := ihf.models V
        choose H hH using fun i ↦ (ihg i).models V
        exact ⟨_, definedFunction_compGraph hG hH⟩
  | @prec n f g pf pg ihf ihg =>
    have h (v : Fin n → ℕ) (u : ℕ) :
        (precConstruction ihf.defined ihg.defined).result v u =
          u.rec (f (.ofFn v)) fun y ih ↦ g (.ofFn (y :> ih :> v)) := by
      induction u with
      | zero => simp [precConstruction]
      | succ u ih => rw [PR.Construction.result_succ, ih]; rfl
    exact of_models (DefinedFunction.of_eq (fun v ↦ h _ _ |>.trans (by simp))
      (precConstruction ihf.defined ihg.defined).result_defined) fun V _ _ ↦ by
        have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ 𝗜𝚺₁ inferInstance
        obtain ⟨F, hF⟩ := ihf.models V
        obtain ⟨G, hG⟩ := ihg.models V
        exact ⟨_, (precConstruction hF hG).result_defined⟩

theorem provablyFunctional_of_primrec' {k : ℕ} {f : List.Vector ℕ k → ℕ} (hf : Nat.Primrec' f) :
    𝗜𝚺₁.ProvablyFunctional (fun v ↦ f (.ofFn v)) :=
  have ⟨p⟩ := PrimrecScheme.nonempty hf
  ⟨_, p.provablyFunctionalVia_graph⟩

theorem provablyFunctional_of_primrec {k : ℕ} {f : List.Vector ℕ k → ℕ} (hf : Primrec f) :
    𝗜𝚺₁.ProvablyFunctional (fun v ↦ f (.ofFn v)) :=
  provablyFunctional_of_primrec' (Nat.Primrec'.prim_iff.mpr hf)

lemma provablyTotal_of_primrec' {k : ℕ} {f : List.Vector ℕ k → ℕ} (hf : Nat.Primrec' f) :
    𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v)) :=
  (provablyFunctional_of_primrec' hf).toProvablyTotal

lemma provablyTotal_of_primrec {k : ℕ} {f : List.Vector ℕ k → ℕ} (hf : Primrec f) :
    𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v)) :=
  (provablyFunctional_of_primrec hf).toProvablyTotal

end Arithmetic

end FFL.FirstOrder
