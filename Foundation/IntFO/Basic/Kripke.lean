import Foundation.IntFO.Basic.Deduction

namespace LO.FirstOrder

open Frame

structure PreorderFrame where
  World : Type u
  Rel : World → World → Prop
  [world_nonempty : Nonempty World]
  [preorder : IsPreorder World Rel]

namespace PreorderFrame

instance : CoeSort PreorderFrame (Type u) := ⟨fun F ↦ PreorderFrame.World F⟩

scoped infix:45 " ≺ " => Rel _

instance (F : PreorderFrame) : IsPreorder F (· ≺ ·) := F.preorder

variable {F : PreorderFrame}

@[refl, simp] lemma rel_refl (w : F) : w ≺ w := IsRefl.refl w

@[trans] lemma rel_trans {w v z : F} : w ≺ v → v ≺ z → w ≺ z := IsTrans.trans w v z

end PreorderFrame

open PreorderFrame

structure KripkeModel (L : Language) where
  Frame : PreorderFrame
  Dom : Frame → Struc L
  wire (w v : Frame) : w ≺ v → Dom w ↪ Dom v
  wire_refl (w : Frame) : wire w w (IsRefl.refl _) = Function.Embedding.refl _
  wire_trans (w v z : Frame) (hxy : w ≺ v) (hyz : v ≺ z) :
    wire v z hyz ∘ wire w v hxy = wire w z (IsTrans.trans w v z hxy hyz)
  monotone {w v : Frame} {k} (R : L.Rel k) (a : Fin k → Dom w) :
    (hxy : w ≺ v) → (Dom w).struc.rel R a → (Dom v).struc.rel R fun i ↦ wire w v hxy (a i)
  wire_func {w v : Frame} {k} (f : L.Func k) (a : Fin k → Dom w) (hwv : w ≺ v) :
    wire w v hwv ((Dom w).struc.func f a) = (Dom v).struc.func f fun i ↦ wire w v hwv (a i)

instance : CoeSort (KripkeModel L) (Type _) := ⟨fun 𝓚 ↦ 𝓚.Frame⟩

attribute [simp] KripkeModel.wire_refl

namespace KripkeModel

variable {L : Language} {𝓚 : KripkeModel L}

abbrev Domain (w : 𝓚) : Struc L := 𝓚.Dom w

def Val {n} (w : 𝓚) (bv : Fin n → Domain w) (fv : ξ → Domain w) : Semiformulaᵢ L ξ n → Prop
  | .rel R t => (Domain w).struc.rel R fun i ↦ Semiterm.val (Domain w).struc bv fv (t i)
  | ⊤        => True
  | ⊥        => False
  | φ ⋏ ψ    => Val w bv fv φ ∧ Val w bv fv ψ
  | φ ⋎ ψ    => Val w bv fv φ ∨ Val w bv fv ψ
  | φ ➝ ψ    => ∀ v, (hwv : w ≺ v) →
    Val v (fun x ↦ 𝓚.wire w v hwv (bv x)) (fun x ↦ 𝓚.wire w v hwv (fv x)) φ →
    Val v (fun x ↦ 𝓚.wire w v hwv (bv x)) (fun x ↦ 𝓚.wire w v hwv (fv x)) ψ
  | ∀' φ     => ∀ v, (hwv : w ≺ v) →
    ∀ x : Domain v, Val v (x :> fun x ↦ 𝓚.wire w v hwv (bv x)) (fun x ↦ 𝓚.wire w v hwv (fv x)) φ
  | ∃' φ     => ∃ x : Domain w, Val w (x :> bv) fv φ

scoped notation:45 w " ⊩[" bv "|" fv "] " φ:46 => Val w bv fv φ

variable (w : 𝓚) (bv : Fin n → Domain w) (fv : ξ → Domain w)

@[simp] lemma val_verum : w ⊩[bv|fv] ⊤ := by trivial

@[simp] lemma val_falsum : ¬w ⊩[bv|fv] ⊥ := by rintro ⟨⟩

variable {w bv fv}

@[simp] lemma val_rel {k} {R : L.Rel k} {t} :
    w ⊩[bv|fv] .rel R t ↔ (Domain w).struc.rel R fun i ↦ Semiterm.val (Domain w).struc bv fv (t i) := by rfl

@[simp] lemma val_and {φ ψ : Semiformulaᵢ L ξ n} : w ⊩[bv|fv] φ ⋏ ψ ↔ w ⊩[bv|fv] φ ∧ w ⊩[bv|fv] ψ := by rfl

@[simp] lemma val_or {φ ψ : Semiformulaᵢ L ξ n} : w ⊩[bv|fv] φ ⋎ ψ ↔ w ⊩[bv|fv] φ ∨ w ⊩[bv|fv] ψ := by rfl

@[simp] lemma val_imply {φ ψ : Semiformulaᵢ L ξ n} :
    w ⊩[bv|fv] φ ➝ ψ ↔
    ∀ v, (hwv : w ≺ v) →
      v ⊩[fun x ↦ 𝓚.wire w v hwv (bv x)|fun x ↦ 𝓚.wire w v hwv (fv x)] φ →
      v ⊩[fun x ↦ 𝓚.wire w v hwv (bv x)|fun x ↦ 𝓚.wire w v hwv (fv x)] ψ := by rfl

@[simp] lemma val_all {φ : Semiformulaᵢ L ξ (n + 1)} :
    w ⊩[bv|fv] ∀' φ ↔
    ∀ v, (hwv : w ≺ v) →
      ∀ x : Domain v, v ⊩[x :> fun x ↦ 𝓚.wire w v hwv (bv x)|fun x ↦ 𝓚.wire w v hwv (fv x)] φ := by rfl

@[simp] lemma val_ex {φ : Semiformulaᵢ L ξ (n + 1)} :
    w ⊩[bv|fv] ∃' φ ↔ ∃ x : Domain w, w ⊩[x :> bv|fv] φ := by rfl

@[simp] lemma val_neg {φ : Semiformulaᵢ L ξ n} :
    w ⊩[bv|fv] ∼φ ↔
    ∀ v, (hwv : w ≺ v) → ¬v ⊩[fun x ↦ 𝓚.wire w v hwv (bv x)|fun x ↦ 𝓚.wire w v hwv (fv x)] φ := by rfl

lemma wire_val (t : Semiterm L ξ n) {v : 𝓚} (hwv : w ≺ v) :
    𝓚.wire w v hwv (t.val (Domain w).struc bv fv) =
    t.val (Domain v).struc (fun x ↦ 𝓚.wire w v hwv (bv x)) (fun x ↦ 𝓚.wire w v hwv (fv x)) := by
  induction t <;> simp [Semiterm.val_func, wire_func, *]

@[simp] lemma val_rew {bv : Fin n₂ → Domain w} {fv : ξ₂ → Domain w} {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformulaᵢ L ξ₁ n₁} :
    w ⊩[bv|fv] (ω ▹ φ) ↔
    w ⊩[fun x ↦ (ω #x).val (Domain w).struc bv fv|fun x ↦ (ω &x).val (Domain w).struc bv fv] φ := by
  induction φ using Semiformulaᵢ.rec' generalizing n₂ w
  case hRel k R t =>
    simp only [Semiformulaᵢ.rew_rel, val_rel]
    apply iff_of_eq; congr; funext x
    simp [Semiterm.val_rew ω (t x), Function.comp_def]
  case hImp φ ψ ihφ ihψ =>
    simp only [val_imply, Function.comp_apply, wire_val]
    constructor
    · intro h v hwv hφ
      simpa [Function.comp_def] using ihψ.mp <| h v hwv (ihφ.mpr <| by simpa [Function.comp_def, wire_val] using hφ)
    · intro h v hwv hφ
      exact ihψ.mpr <| h v hwv <| by simpa [Function.comp_def] using ihφ.mp hφ
  case hAnd φ ψ ihφ ihψ => simp [ihφ, ihψ]
  case hOr φ ψ ihφ ihψ => simp [ihφ, ihψ]
  case hVerum => simp
  case hFalsum => simp
  case hAll φ ih =>
    constructor
    · simp only [val_all, Nat.succ_eq_add_one, wire_val]
      intro h v hwv x
      exact cast (by congr; { funext x; cases x using Fin.cases <;> simp }; { simp }) <| ih.mp <| h v hwv x
    · simp only [val_all, Nat.succ_eq_add_one, wire_val]
      intro h v hwv x
      apply ih.mpr
      exact cast (by congr; { funext x; cases x using Fin.cases <;> simp }; { simp }) <| h v hwv x
  case hEx φ ih =>
    constructor
    · simp only [Rewriting.app_ex, val_ex, Nat.succ_eq_add_one, forall_exists_index]
      intro x h
      exact ⟨x, cast (by congr; { funext x; cases x using Fin.cases <;> simp }; { simp }) (ih.mp h)⟩
    · simp only [val_ex, Nat.succ_eq_add_one, forall_exists_index]
      intro x h
      exact ⟨x, ih.mpr <| cast (by congr; { funext x; cases x using Fin.cases <;> simp }; { simp }) h⟩

variable (𝓚)

def Force (φ : Semiformulaᵢ L ξ n) : Prop := ∀ (w : 𝓚) bv fv, w ⊩[bv|fv] φ

scoped infix:45 " ⊩ " => Force

instance : Semantics (SyntacticFormulaᵢ L) (KripkeModel L) := ⟨fun 𝓚 φ ↦ 𝓚.Force φ⟩

variable {𝓚}

variable {Λ : Hilbertᵢ L}

open HilbertProofᵢ Semantics

/-
theorem sound (H : 𝓚 ⊧* Λ) : Λ ⊢! φ → 𝓚 ⊧ φ
  | eaxm h => RealizeSet.realize 𝓚 h
  | @mdp _ _ φ ψ bφψ bφ => fun w bv fv ↦ by simpa using sound H bφψ w bv fv w (by simp) (sound H bφ w _ _)
  | @gen _ _ φ b        => fun w bv fv v hwv x ↦ by { have := sound H b v ![] }
-/

end KripkeModel

end LO.FirstOrder
