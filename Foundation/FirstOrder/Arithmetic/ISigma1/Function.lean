module

public import Foundation.FirstOrder.Arithmetic.Function.Basic
public import Foundation.FirstOrder.Arithmetic.HFS.PRF
public import Foundation.Vorspiel.List.Vector
public import Mathlib.Computability.Primrec.List

/-!
# Primitive recursive functions are `𝗜𝚺₁`-provably total

Every primitive recursive function is `𝗜𝚺₁`-provably functional, by induction on its derivation of
primitive recursiveness.

## References

- [HP98, Theorem I.1.54, Lemma I.1.55]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

namespace Arithmetic

open ArithmeticTheory Bounding.HierarchySymbol

open ProvablyFunctionalVia in
/-- Every primitive recursive function in the `List.Vector` form `Nat.Primrec'` is
`𝗜𝚺₁`-provably functional.
- [HP98, Theorem I.1.54]
- [HP98, Lemma I.1.55] -/
theorem provablyFunctional_of_primrec' {k : ℕ} {f : List.Vector ℕ k → ℕ} (hf : Nat.Primrec' f) :
    𝗜𝚺₁.ProvablyFunctional (fun v ↦ f (.ofFn v)) := by
  induction hf with
  | zero =>
    have h (V : Type) [ORingStructure V] :
        𝚺ᴬ₁.DefinedFunction (fun _ : Fin 0 → V ↦ 0) (.mkSigma “y. y = 0”) :=
      .mk fun _ ↦ by simp
    exact ⟨_, of_models (h ℕ) fun V _ _ ↦ ⟨_, h V⟩⟩
  | succ =>
    have h (V : Type) [ORingStructure V] :
        𝚺ᴬ₁.DefinedFunction (fun v : Fin 1 → V ↦ v 0 + 1) (.mkSigma “y x. y = x + 1”) :=
      .mk fun _ ↦ by simp
    exact ⟨_, of_models ((h ℕ).of_eq (by simp)) fun V _ _ ↦ ⟨_, h V⟩⟩
  | @get n i =>
    have h (V : Type) [ORingStructure V] :
        𝚺ᴬ₁.DefinedFunction (fun v : Fin n → V ↦ v i)
          ((.mkSigma “y x. y = x” : 𝚺ᴬ₁.Semisentence 2).rew (Rew.subst ![#0, #i.succ])) :=
      .mk fun _ ↦ by simp
    exact ⟨_, of_models ((h ℕ).of_eq (by simp)) fun V _ _ ↦ ⟨_, h V⟩⟩
  | comp g _ _ ihf ihg =>
    obtain ⟨ψ, hψ⟩ := ihf
    choose χ hχ using ihg
    exact ⟨_, of_models ((definedFunction_compGraph hψ.defined fun i ↦ (hχ i).defined).of_eq
      (by simp)) fun V _ _ ↦ by
        obtain ⟨G, hG⟩ := hψ.models V
        choose H hH using fun i ↦ (hχ i).models V
        exact ⟨_, definedFunction_compGraph hG hH⟩⟩
  | @prec n f g _ _ ihf ihg =>
    obtain ⟨ψ, hψ⟩ := ihf
    obtain ⟨χ, hχ⟩ := ihg
    let bp : PR.Blueprint n := ⟨ψ, χ.rew (Rew.subst (#0 :> #2 :> #1 :> (#·.succ.succ.succ)))⟩
    let con (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {F : (Fin n → V) → V}
        {G : (Fin (n + 2) → V) → V} (hF : 𝚺ᴬ₁.DefinedFunction F ψ)
        (hG : 𝚺ᴬ₁.DefinedFunction G χ) : PR.Construction V bp :=
      { zero := F
        succ := fun v i z ↦ G (i :> z :> v)
        zero_defined := hF
        succ_defined := .mk fun v ↦ by
          simp [bp, Semiformula.eval_rew, Empty.eq_elim, hG.iff, Matrix.comp_vecCons'] }
    have h (v : Fin n → ℕ) (u : ℕ) :
        (con ℕ hψ.defined hχ.defined).result v u =
          u.rec (f (.ofFn v)) fun y ih ↦ g (.ofFn (y :> ih :> v)) := by
      induction u with
      | zero => simp [con]
      | succ u ih => rw [PR.Construction.result_succ, ih]
    exact ⟨_, of_models (DefinedFunction.of_eq (fun v ↦ h _ _ |>.trans (by simp))
      (con ℕ hψ.defined hχ.defined).result_defined) fun V _ _ ↦ by
        have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ 𝗜𝚺₁ inferInstance
        obtain ⟨F, hF⟩ := hψ.models V
        obtain ⟨G, hG⟩ := hχ.models V
        exact ⟨_, (con V hF hG).result_defined⟩⟩

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
