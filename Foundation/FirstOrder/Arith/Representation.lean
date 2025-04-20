import Foundation.FirstOrder.Arith.CobhamR0
import Foundation.Vorspiel.Arith
import Mathlib.Computability.Primrec

namespace Part

lemma unit_dom_iff (x : Part Unit) : x.Dom ↔ () ∈ x := by simp [dom_iff_mem, show ∀ x : Unit, x = () by intro x; rfl]

end Part

namespace Mathlib.List.Vector

variable {α : Type*}

lemma cons_get (a : α) (v : List.Vector α k) : (a ::ᵥ v).get = a :> v.get := by
  ext i; cases i using Fin.cases <;> simp

end Mathlib.List.Vector

open Encodable Denumerable

namespace Nat.Partrec

open Part _root_.Primrec

lemma projection {f : ℕ →. ℕ} (hf : Nat.Partrec f) (unif : ∀ {m n₁ n₂ a₁ a₂ : ℕ}, a₁ ∈ f (m.pair n₁) → a₂ ∈ f (m.pair n₂) → a₁ = a₂) :
    ∃ g : ℕ →. ℕ, Nat.Partrec g ∧ (∀ a m, a ∈ g m ↔ ∃ z, a ∈ f (m.pair z)) := by
  obtain ⟨cf, rfl⟩ := Code.exists_code.1 hf
  let F : ℕ → ℕ → Option ℕ := fun m n ↦ Nat.rec .none (fun x ih ↦ ih.casesOn (cf.evaln n (m.pair x)) .some) n
  have : Primrec₂ F := .to₂ <| Primrec.nat_rec' Primrec.snd (.const Option.none)
      (Primrec.option_casesOn (Primrec.snd.comp .snd)
        (Code.evaln_prim.comp <| _root_.Primrec.pair (_root_.Primrec.pair (snd.comp .fst) (.const cf)) (Primrec₂.natPair.comp (fst.comp fst) (fst.comp snd)))
        (Primrec.option_some.comp snd).to₂).to₂
  have hF : ∀ {m n a}, a ∈ F m n ↔ ∃ x < n, a ∈ cf.evaln n (m.pair x) := by
    suffices ∀ m n s a : ℕ,
      Nat.rec Option.none (fun x ih ↦ ih.casesOn (cf.evaln s (m.pair x)) Option.some) n = Option.some a ↔
      ∃ x < n, cf.evaln s (m.pair x) = .some a from fun m n a ↦ this m n n a
    intro m n s a
    induction n generalizing a
    case zero => simp
    case succ n ih =>
        cases hC : @Nat.rec (fun _ ↦ Option ℕ) Option.none (fun x ih ↦ ih.rec (cf.evaln s (m.pair x)) Option.some) n <;> simp [hC]
        · constructor
          · intro h; exact ⟨n, by simp, h⟩
          · rintro ⟨x, hx, Hx⟩
            rcases eq_or_lt_of_le (le_of_lt_succ hx) with (rfl | hx)
            · exact Hx
            · exfalso; simpa using ((ih _).mpr ⟨x, hx, Hx⟩).symm.trans hC
        · constructor
          · rintro rfl;
            rcases (ih _).mp hC with ⟨x, hx, Hx⟩
            exact ⟨x, lt_trans hx (by simp), Hx⟩
          · rintro ⟨x, _, Hx⟩
            rcases (ih _).mp hC with ⟨y, _, Hy⟩
            exact unif (Nat.Partrec.Code.evaln_sound Hy) (Nat.Partrec.Code.evaln_sound Hx)
  have mono : ∀ {a m n₁ n₂ : ℕ}, n₁ ≤ n₂ → a ∈ F m n₁ → a ∈ F m n₂ := by
    intro a m n₁ n₂ hn h₁
    rcases hF.mp h₁ with ⟨x, hx, H⟩
    apply hF.mpr ⟨x, lt_of_lt_of_le hx hn, Code.evaln_mono hn H⟩
  have : Partrec (fun m ↦ rfindOpt (F m)) := Partrec.nat_iff.1 <| Partrec.rfindOpt <| this.to_comp
  exact ⟨_, this, by
    intro a m
    rw [Nat.rfindOpt_mono mono]
    constructor
    · rintro ⟨n, H⟩
      obtain ⟨x, _, H⟩ := hF.mp H
      exact ⟨x, Code.evaln_sound H⟩
    · rintro ⟨x, H⟩
      obtain ⟨s, Hs⟩ := Code.evaln_complete.mp H
      exact ⟨max s x + 1, (@hF m (max s x + 1) a).mpr
        ⟨x, by simp [Nat.lt_succ],
          Code.evaln_mono (le_trans (Nat.le_max_left s x) (le_add_right (max s x) 1)) Hs⟩⟩⟩

end Nat.Partrec

namespace Partrec

variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

lemma projection {f : α → β →. γ} (hf : Partrec₂ f) (unif : ∀ {a b₁ b₂ c₁ c₂}, c₁ ∈ f a b₁ → c₂ ∈ f a b₂ → c₁ = c₂) :
    ∃ g : α →. γ, Partrec g ∧ (∀ c a, c ∈ g a ↔ ∃ b, c ∈ f a b) := by
  have := Nat.Partrec.projection (Partrec.bind_decode₂_iff.mp hf)
    (by intro m n₁ n₂ c₁ c₂; simp only [Part.mem_bind_iff, Part.mem_of_Option,
          Option.mem_def, decode₂_eq_some, Part.mem_map_iff, Prod.exists, encode_prod_val,
          Nat.pair_eq_pair, forall_exists_index, and_imp]
        rintro a b₁ rfl rfl c₁ h₁ rfl a b₂ e rfl c₂ h₂ rfl
        rcases Encodable.encode_inj.mp e
        rw [unif h₁ h₂])
  rcases this with ⟨g, hg, H⟩
  let g' : α →. γ := fun a ↦ (g (encode a)).bind fun n ↦ decode (α := γ) n
  refine ⟨g', ((nat_iff.2 hg).comp Computable.encode).bind (Computable.decode.of_Option.comp Computable.snd).to₂, ?_⟩
  have H : ∀ {c a : ℕ}, c ∈ g a ↔ ∃ a' b, encode a' = a ∧ ∃ c' ∈ f a' b, encode c' = c := by
    simp [Encodable.decode₂_eq_some] at H
    intro c a; constructor
    · intro h; rcases (H c a).mp h with ⟨b, a, b, ⟨rfl, rfl⟩, ⟨c, H, rfl⟩⟩
      exact ⟨a, b, rfl, c, H, rfl⟩
    · rintro ⟨a, b, rfl, c, hc, rfl⟩
      exact (H _ _).mpr ⟨encode b, a, b, ⟨rfl, rfl⟩, c, hc, rfl⟩
  intro c a
  constructor
  · simp [g']
    intro c' h hc
    rcases H.mp h with ⟨a, b, ae, c, habc, rfl⟩;
    rcases by simpa using hc
    rcases Encodable.encode_inj.mp ae
    exact ⟨b, habc⟩
  · simp [g']
    rintro b habc
    exact ⟨encode c, H.mpr ⟨a, b, rfl, c, habc, rfl⟩, by simp⟩

end Partrec

namespace REPred

variable {α β : Type*} [Primcodable α] [Primcodable β] {p q : α → Prop}

@[simp] protected lemma const (p : Prop) : REPred fun _ : α ↦ p := by
  by_cases h : p <;> simp [h]
  · simpa using Partrec.some.dom_re
  · simpa using (Partrec.none (α := α) (σ := α)).dom_re

lemma iff : REPred p ↔ ∃ f : α →. Unit, Partrec f ∧ p = fun x ↦ (f x).Dom :=
  ⟨fun h ↦ ⟨_, h, by ext x; simp [Part.assert]⟩, by rintro ⟨f, hf, rfl⟩; exact hf.dom_re⟩

lemma iff' : REPred p ↔ ∃ f : α →. Unit, Partrec f ∧ ∀ x, p x ↔ (f x).Dom :=
  ⟨fun h ↦ ⟨_, h, by intro x; simp [Part.assert]⟩, by rintro ⟨f, hf, H⟩; exact hf.dom_re.of_eq (by simp [H])⟩

lemma and (hp : REPred p) (hq : REPred q) : REPred fun x ↦ p x ∧ q x := by
  rcases REPred.iff.mp hp with ⟨f, hf, rfl⟩
  rcases REPred.iff.mp hq with ⟨g, hg, rfl⟩
  let h : α →. Unit := fun x ↦ (f x).bind fun _ ↦ (g x).map fun _ ↦ ()
  have : Partrec h := Partrec.bind hf <| Partrec.to₂ <| Partrec.map (hg.comp Computable.fst) (Computable.const ()).to₂
  exact REPred.iff.mpr ⟨_, this, by funext x; simp [h]⟩

lemma or (hp : REPred p) (hq : REPred q) : REPred fun x ↦ p x ∨ q x := by
  rcases REPred.iff.mp hp with ⟨f, hf, rfl⟩
  rcases REPred.iff.mp hq with ⟨g, hg, rfl⟩
  rcases hf.merge hg (by intro a x; simp) with ⟨k, hk, h⟩
  exact REPred.iff.mpr ⟨k, hk, by funext x; simp [Part.unit_dom_iff, h]⟩

lemma projection {p : α × β → Prop} (hp : REPred p) : REPred fun x ↦ ∃ y, p (x, y) := by
  rcases REPred.iff.mp hp with ⟨f, hf, rfl⟩
  have : Partrec₂ fun a b ↦ f (a, b) := hf.comp <| Computable.pair .fst .snd
  obtain ⟨g, hg, Hg⟩ := Partrec.projection this (by simp)
  exact REPred.iff.mpr ⟨g, hg, by funext x; simp [Part.unit_dom_iff, Hg]⟩

protected lemma comp {f : α → β} (hf : Computable f) {p : β → Prop} (hp : REPred p) : REPred fun x ↦ p (f x) := by
  rcases REPred.iff.mp hp with ⟨p, pp, rfl⟩
  exact REPred.iff'.mpr ⟨_, pp.comp hf, by intro x; simp⟩

end REPred

namespace LO.FirstOrder.Arith

open Mathlib Encodable Semiterm.Operator.GoedelNumber

section

lemma term_primrec {k f} : (t : Semiterm ℒₒᵣ ξ k) → Primrec (fun v : List.Vector ℕ k ↦ t.valm ℕ v.get f)
  | #x                                 => by simpa using Primrec.vector_get.comp .id (.const _)
  | &x                                 => by simpa using Primrec.const _
  | Semiterm.func Language.Zero.zero _ => by simpa using Primrec.const 0
  | Semiterm.func Language.One.one _   => by simpa using Primrec.const 1
  | Semiterm.func Language.Add.add v   => by
    simpa [Semiterm.val_func] using Primrec.nat_add.comp (term_primrec (v 0)) (term_primrec (v 1))
  | Semiterm.func Language.Mul.mul v   => by
    simpa [Semiterm.val_func] using Primrec.nat_mul.comp (term_primrec (v 0)) (term_primrec (v 1))

lemma sigma1_re (ε : ξ → ℕ) {k} {φ : Semiformula ℒₒᵣ ξ k} (hp : Hierarchy 𝚺 1 φ) :
    REPred fun v : List.Vector ℕ k ↦ Semiformula.Evalm ℕ v.get ε φ := by
  apply sigma₁_induction' hp
  case hVerum => simp
  case hFalsum => simp
  case hEQ =>
    intro n t₁ t₂
    refine ComputablePred.to_re <| ComputablePred.computable_iff.mpr
      <| ⟨fun v : List.Vector ℕ n ↦ decide (t₁.valm ℕ v.get ε = t₂.valm ℕ v.get ε), ?_, ?_⟩
    · apply Primrec.to_comp <| Primrec.eq.comp (term_primrec t₁) (term_primrec t₂)
    · simp
  case hNEQ =>
    intro n t₁ t₂
    refine ComputablePred.to_re <| ComputablePred.computable_iff.mpr
      <| ⟨fun v : List.Vector ℕ n ↦ !decide (t₁.valm ℕ v.get ε = t₂.valm ℕ v.get ε), ?_, ?_⟩
    · apply Primrec.to_comp <| Primrec.not.comp <| Primrec.eq.comp (term_primrec t₁) (term_primrec t₂)
    · simp
  case hLT =>
    intro n t₁ t₂
    refine ComputablePred.to_re <| ComputablePred.computable_iff.mpr
      <| ⟨fun v : List.Vector ℕ n ↦ decide (t₁.valm ℕ v.get ε < t₂.valm ℕ v.get ε), ?_, ?_⟩
    · apply Primrec.to_comp <| Primrec.nat_lt.comp (term_primrec t₁) (term_primrec t₂)
    · simp
  case hNLT =>
    intro n t₁ t₂
    refine ComputablePred.to_re <| ComputablePred.computable_iff.mpr
      <| ⟨fun v : List.Vector ℕ n ↦ !decide (t₁.valm ℕ v.get ε < t₂.valm ℕ v.get ε), ?_, ?_⟩
    · apply Primrec.to_comp <| Primrec.not.comp <| Primrec.nat_lt.comp (term_primrec t₁) (term_primrec t₂)
    · simp
  case hAnd =>
    intro n φ ψ _ _ ihp ihq
    exact REPred.of_eq (ihp.and ihq) fun v ↦ by simp
  case hOr =>
    intro n φ ψ _ _ ihp ihq
    exact REPred.of_eq (ihp.or ihq) fun v ↦ by simp
  case hBall =>
    intro n t φ _ ih
    rcases REPred.iff'.mp ih with ⟨f, hf, H⟩
    let g : List.Vector ℕ n →. Unit := fun v ↦
      Nat.rec (.some ()) (fun x ih ↦ ih.bind fun _ ↦ f (x ::ᵥ v)) (t.valm ℕ v.get ε)
    have : Partrec g :=
      Partrec.nat_rec (term_primrec t).to_comp (Computable.const ())
        (Partrec.to₂ <| hf.comp (Primrec.to_comp <| Primrec.vector_cons.comp (Primrec.fst.comp .snd) .fst))
    refine REPred.iff.mpr ⟨_, this, ?_⟩
    funext v; simp [g]
    suffices ∀ k : ℕ, (∀ x < k, Semiformula.Evalm ℕ (x :> v.get) ε φ) ↔
      Part.Dom (Nat.rec (.some ()) (fun x ih ↦ ih.bind fun _ ↦ f (x ::ᵥ v)) k) from this _
    intro k; induction k
    case zero => simp
    case succ k ih =>
      simp [←ih]
      constructor
      · intro h
        exact ⟨fun x hx ↦ h x (lt_trans hx (by simp)),
          (H (k ::ᵥ v)).mp (by simpa [List.Vector.cons_get] using h k (by simp))⟩
      · rintro ⟨hs, hd⟩ x hx
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hx) with (hx | rfl)
        · exact hs x hx
        · simpa [List.Vector.cons_get] using (H (x ::ᵥ v)).mpr hd
  case hEx =>
    intro n φ _ ih
    rcases REPred.iff'.mp ih with ⟨f, _, _⟩
    have : REPred fun vx : List.Vector ℕ n × ℕ ↦ Semiformula.Evalm ℕ (vx.2 :> vx.1.get) ε φ := by
      simpa [List.Vector.cons_get] using ih.comp (Primrec.to_comp <| Primrec.vector_cons.comp .snd .fst)
    simpa using this.projection

end

open Nat.ArithPart₁

def codeAux : {k : ℕ} → Nat.ArithPart₁.Code k → Formula ℒₒᵣ (Fin (k + 1))
  | _, Code.zero _    => “&0 = 0”
  | _, Code.one _     => “&0 = 1”
  | _, Code.add i j   => “&0 = &i.succ + &j.succ”
  | _, Code.mul i j   => “&0 = &i.succ * &j.succ”
  | _, Code.equal i j => “(&i.succ = &j.succ ∧ &0 = 1) ∨ (&i.succ ≠ &j.succ ∧ &0 = 0)”
  | _, Code.lt i j    => “(&i.succ < &j.succ ∧ &0 = 1) ∨ (&i.succ ≮ &j.succ ∧ &0 = 0)”
  | _, Code.proj i    => “&0 = !!&i.succ”
  | k, @Code.comp _ n c d  =>
    exClosure ((Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (n + 1)) ![] (&0 :> (#·)) ▹ (codeAux c)) ⋏
      Matrix.conj fun i ↦ Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (k + 1)) ![] (#i :> (&·.succ)) ▹ codeAux (d i))
  | k, Code.rfind c   =>
    (Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (k + 1 + 1)) ![] (‘0’ :> &0 :> (&·.succ)) ▹ codeAux c) ⋏
    (∀[“z. z < &0”] ∃' “z. z ≠ 0” ⋏ ((Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (k + 1 + 1)) ![] (#0 :> #1 :> (&·.succ)) ▹ codeAux c)))

def code (c : Code k) : Semisentence ℒₒᵣ (k + 1) := (Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (k + 1)) ![] (#0 :> (#·.succ))) ▹ (codeAux c)

/-
section model

open LO.Arith

variable {M : Type*} [ORingStruc M] [M ⊧ₘ* 𝐑₀]

private lemma codeAux_uniq {k} {c : Code k} {v : Fin k → M} {z z' : M} :
    Semiformula.Evalfm M (z :> v) (codeAux c) → Semiformula.Evalfm M (z' :> v) (codeAux c) → z = z' := by
  induction c generalizing z z' <;> simp [code, codeAux]
  case zero => rintro rfl rfl; rfl
  case one  => rintro rfl rfl; rfl
  case add  => rintro rfl rfl; rfl
  case mul  => rintro rfl rfl; rfl
  case proj => rintro rfl rfl; rfl
  case equal i j =>
    by_cases hv : v i = v j <;> simp [hv]
    · rintro rfl rfl; rfl
    · rintro rfl rfl; rfl
  case lt i j =>
    by_cases hv : v i < v j <;> simp [hv, -not_lt, ←not_lt]
    · rintro rfl rfl; rfl
    · rintro rfl rfl; rfl
  case comp m n c d ihc ihd =>
    simp [Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons']
    intro w₁ hc₁ hd₁ w₂ hc₂ hd₂;
    have : w₁ = w₂ := funext fun i => ihd i (hd₁ i) (hd₂ i)
    rcases this with rfl
    exact ihc hc₁ hc₂
  case rfind c ih =>
    simp [Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons']
    intro h₁ hm₁ h₂ hm₂
    by_contra hz
    wlog h : z < z' with Hz
    case inr =>
      have : z' < z := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hz)
      exact Hz (k := k) c ih h₂ hm₂ h₁ hm₁ (Ne.symm hz) this
    have : ∃ x, x ≠ 0 ∧ (Semiformula.Evalfm M (x :> z :> fun i => v i)) (codeAux c) := hm₂ z h
    rcases this with ⟨x, xz, hx⟩
    exact xz (ih hx h₁)

lemma code_uniq {k} {c : Code k} {v : Fin k → M} {z z' : M} :
    Semiformula.Evalbm M (z :> v) (code c) → Semiformula.Evalbm M (z' :> v) (code c) → z = z' := by
  simp [code, Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def, Matrix.comp_vecCons']
  exact codeAux_uniq

end model
-/

private lemma codeAux_sigma_one {k} (c : Nat.ArithPart₁.Code k) : Hierarchy 𝚺 1 (codeAux c) := by
  induction c <;> simp [codeAux, Matrix.fun_eq_vec₂]
  case comp c d ihc ihg =>
    exact Hierarchy.exClosure (by simp [ihc, ihg])
  case rfind k c ih => simp [ih]

@[simp] lemma code_sigma_one {k} (c : Nat.ArithPart₁.Code k) : Hierarchy 𝚺 1 (code c) :=
  Hierarchy.rew _ (codeAux_sigma_one c)

@[simp] lemma natCast_nat (n : ℕ) : Nat.cast n = n := by rfl

private lemma models_codeAux {c : Code k} {f : List.Vector ℕ k →. ℕ} (hc : c.eval f) (y : ℕ) (v : Fin k → ℕ) :
    Semiformula.Evalfm ℕ (y :> v) (codeAux c) ↔ f (List.Vector.ofFn v) = Part.some y := by
  induction hc generalizing y <;> simp [code, codeAux, models_iff]
  case zero =>
    have : (0 : Part ℕ) = Part.some 0 := rfl
    simp [this, eq_comm]
  case one =>
    have : (1 : Part ℕ) = Part.some 1 := rfl
    simp [this, eq_comm]
  case equal i j =>
    by_cases hv : v i = v j <;> simp [hv, Nat.isEqNat, eq_comm]
  case lt i j =>
    by_cases hv : v i < v j <;> simp [hv, Nat.isLtNat, eq_comm]
    · simp [Nat.not_lt.mp hv]
  case add => simp [eq_comm]
  case mul => simp [eq_comm]
  case proj => simp [eq_comm]
  case comp c d f g _ _ ihf ihg =>
    simp [Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons']
    constructor
    · rintro ⟨e, hf, hg⟩
      have hf : f (List.Vector.ofFn e) = Part.some y := (ihf _ _).mp hf
      have hg : ∀ i, g i (List.Vector.ofFn v) = Part.some (e i) := fun i => (ihg i _ _).mp (hg i)
      simp [hg, hf]
    · intro h
      have : ∃ w, (∀ i, List.Vector.get w i ∈ g i (List.Vector.ofFn v)) ∧ y ∈ f w := by
        simpa using Part.eq_some_iff.mp h
      rcases this with ⟨w, hw, hy⟩
      exact ⟨w.get, (ihf y w.get).mpr (by simpa[Part.eq_some_iff] using hy),
        fun i => (ihg i (w.get i) v).mpr (by simpa[Part.eq_some_iff] using hw i)⟩
  case rfind c f _ ihf =>
    simp [Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons', ihf, List.Vector.ofFn_vecCons]
    constructor
    · rintro ⟨hy, h⟩; simp [Part.eq_some_iff]
      exact ⟨by simpa using hy, by intro z hz; exact Nat.ne_zero_of_lt (h z hz)⟩
    · intro h; simpa [pos_iff_ne_zero] using Nat.mem_rfind.mp (Part.eq_some_iff.mp h)

lemma models_code {c : Code k} {f : List.Vector ℕ k →. ℕ} (hc : c.eval f) (y : ℕ) (v : Fin k → ℕ) :
    Semiformula.Evalbm ℕ (y :> v) (code c) ↔ y ∈ f (List.Vector.ofFn v) := by
  simpa[code, models_iff, Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def,
    Matrix.comp_vecCons', ←Part.eq_some_iff] using models_codeAux hc y v

noncomputable def codeOfPartrec' {k} (f : List.Vector ℕ k →. ℕ) : Semisentence ℒₒᵣ (k + 1) :=
  code <| Classical.epsilon (fun c ↦ ∀ y v, Semiformula.Evalbm ℕ (y :> v) (code c) ↔ y ∈ f (List.Vector.ofFn v))

lemma codeOfPartrec'_spec {k} {f : List.Vector ℕ k →. ℕ} (hf : Nat.Partrec' f) {y : ℕ} {v : Fin k → ℕ} :
    ℕ ⊧/(y :> v) (codeOfPartrec' f) ↔ y ∈ f (List.Vector.ofFn v) := by
  have : ∃ c, ∀ y v, Semiformula.Evalbm ℕ (y :> v) (code c) ↔ y ∈ f (List.Vector.ofFn v) := by
    rcases Nat.ArithPart₁.exists_code (of_partrec hf) with ⟨c, hc⟩
    exact ⟨c, models_code hc⟩
  exact Classical.epsilon_spec this y v

open Classical

noncomputable def codeOfREPred (p : ℕ → Prop) : Semisentence ℒₒᵣ 1 :=
  let f : ℕ →. Unit := fun a ↦ Part.assert (p a) fun _ ↦ Part.some ()
  (codeOfPartrec' (fun v ↦ (f (v.get 0)).map fun _ ↦ 0))/[‘0’, #0]

lemma codeOfREPred_spec {p : ℕ → Prop} (hp : REPred p) {x : ℕ} :
    ℕ ⊧/![x] (codeOfREPred p) ↔ p x := by
  let f : ℕ →. Unit := fun a ↦ Part.assert (p a) fun _ ↦ Part.some ()
  suffices ℕ ⊧/![x] ((codeOfPartrec' fun v ↦ Part.map (fun _ ↦ 0) (f (v.get 0)))/[‘0’, #0]) ↔ p x from this
  have : Partrec fun v : List.Vector ℕ 1 ↦ (f (v.get 0)).map fun _ ↦ 0 := by
    refine Partrec.map (Partrec.comp hp (Primrec.to_comp <| Primrec.vector_get.comp .id (.const 0))) (Computable.const 0).to₂
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
  apply (codeOfPartrec'_spec (Nat.Partrec'.of_part this) (v := ![x]) (y := 0)).trans (by simp [f])

variable {T : Theory ℒₒᵣ} [𝐑₀ ⪯ T] [Sigma1Sound T]

lemma re_complete {p : ℕ → Prop} (hp : REPred p) {x : ℕ} :
    p x ↔ T ⊢! ↑((codeOfREPred p)/[‘↑x’] : Sentence ℒₒᵣ) := Iff.trans
  (by simpa [models₀_iff, Semiformula.eval_substs, Matrix.constant_eq_singleton] using (codeOfREPred_spec hp (x := x)).symm)
  (sigma_one_completeness_iff (by simp [codeOfREPred, codeOfPartrec']))

end Arith

end FirstOrder

end LO
