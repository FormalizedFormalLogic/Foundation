module

public import Mathlib.Computability.Halting

@[expose]
public section


namespace Part

@[simp] lemma mem_vector_mOfFn : ∀ {n : ℕ} {w : List.Vector α n} {v : Fin n →. α},
    w ∈ List.Vector.mOfFn v ↔ ∀ i, w.get i ∈ v i
  |     0, _, _ => by simp [List.Vector.mOfFn, List.Vector.eq_nil]
  | n + 1, w, v => by
    suffices (∃ a ∈ v 0, ∃ u, (∀ (i : Fin n), u.get i ∈ v i.succ) ∧ w = a ::ᵥ u) ↔ ∀ (i : Fin (n + 1)), w.get i ∈ v i by
      simpa [List.Vector.mOfFn, @mem_vector_mOfFn _ n]
    constructor
    · rintro ⟨a, ha, v, hv, rfl⟩ i; cases i using Fin.cases <;> simp [ha, hv]
    · intro h; exact ⟨w.head, by simpa using h 0, w.tail, fun i => by simpa using h i.succ, by simp⟩

lemma unit_dom_iff (x : Part Unit) : x.Dom ↔ () ∈ x := by simp [dom_iff_mem, show ∀ x : Unit, x = () by intro x; rfl]

end Part



namespace Nat.Partrec

open Part _root_.Primrec

lemma projection {f : ℕ →. ℕ} (hf : Nat.Partrec f) (unif : ∀ {m n₁ n₂ a₁ a₂ : ℕ}, a₁ ∈ f (m.pair n₁) → a₂ ∈ f (m.pair n₂) → a₁ = a₂) :
    ∃ g : ℕ →. ℕ, Nat.Partrec g ∧ (∀ a m, a ∈ g m ↔ ∃ z, a ∈ f (m.pair z)) := by
  obtain ⟨cf, rfl⟩ := Code.exists_code.1 hf
  let F : ℕ → ℕ → Option ℕ := fun m n ↦ Nat.rec .none (fun x ih ↦ ih.casesOn (cf.evaln n (m.pair x)) .some) n
  have : Primrec₂ F := .to₂ <| Primrec.nat_rec' Primrec.snd (.const Option.none)
      (Primrec.option_casesOn (Primrec.snd.comp .snd)
        (Code.primrec_evaln.comp <| _root_.Primrec.pair (_root_.Primrec.pair (snd.comp .fst) (.const cf)) (Primrec₂.natPair.comp (fst.comp fst) (fst.comp snd)))
        (Primrec.option_some.comp snd).to₂).to₂
  have hF : ∀ {m n a}, a ∈ F m n ↔ ∃ x < n, a ∈ cf.evaln n (m.pair x) := by
    suffices ∀ m n s a : ℕ,
      Nat.rec Option.none (fun x ih ↦ ih.casesOn (cf.evaln s (m.pair x)) Option.some) n = Option.some a ↔
      ∃ x < n, cf.evaln s (m.pair x) = .some a from fun m n a ↦ this m n n a
    intro m n s a
    induction n generalizing a
    case zero => simp
    case succ n ih =>
      cases hC : @Nat.rec (fun _ ↦ Option ℕ) Option.none (fun x ih ↦ ih.rec (cf.evaln s (m.pair x)) Option.some) n
      · suffices
          Code.evaln s cf (Nat.pair m n) = Option.some a
          ↔ ∃ x < n + 1, Code.evaln s cf (Nat.pair m x) = Option.some a by simpa [hC]
        constructor
        · intro h; exact ⟨n, by simp, h⟩
        · rintro ⟨x, hx, Hx⟩
          rcases eq_or_lt_of_le (le_of_lt_succ hx) with (rfl | hx)
          · exact Hx
          · exfalso; simpa using ((ih _).mpr ⟨x, hx, Hx⟩).symm.trans hC
      case some i =>
        suffices i = a ↔ ∃ x < n + 1, Code.evaln s cf (Nat.pair m x) = Option.some a by simpa [hC]
        constructor
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
  have : Partrec (fun m ↦ rfindOpt (F m)) := Partrec.rfindOpt <| this.to_comp
  exact ⟨_, this, by
    intro a m
    suffices (∃ n, F m n = .some a) ↔ ∃ z, a ∈ cf.eval (m.pair z) by
      simpa [Nat.rfindOpt_mono mono]
    constructor
    · rintro ⟨n, H⟩
      obtain ⟨x, _, H⟩ := hF.mp H
      exact ⟨x, Code.evaln_sound H⟩
    · rintro ⟨x, H⟩
      obtain ⟨s, Hs⟩ := Code.evaln_complete.mp H
      exact ⟨max s x + 1, (@hF m (max s x + 1) a).mpr
        ⟨x, by simp [Nat.lt_succ_iff],
          Code.evaln_mono (le_trans (Nat.le_max_left s x) (le_add_right (max s x) 1)) Hs⟩⟩⟩

end Nat.Partrec


namespace Partrec

variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

lemma projection {f : α → β →. γ} (hf : Partrec₂ f) (unif : ∀ {a b₁ b₂ c₁ c₂}, c₁ ∈ f a b₁ → c₂ ∈ f a b₂ → c₁ = c₂) :
    ∃ g : α →. γ, Partrec g ∧ (∀ c a, c ∈ g a ↔ ∃ b, c ∈ f a b) := by
  have := Nat.Partrec.projection (Partrec.bind_decode₂_iff.mp hf)
    (by intro m n₁ n₂ c₁ c₂; simp only [Part.mem_bind_iff, Part.mem_ofOption,
          Option.mem_def, Encodable.decode₂_eq_some, Part.mem_map_iff, Prod.exists, Encodable.encode_prod_val,
          Nat.pair_eq_pair, forall_exists_index, and_imp]
        rintro a b₁ rfl rfl c₁ h₁ rfl a b₂ e rfl c₂ h₂ rfl
        rcases Encodable.encode_inj.mp e
        rw [unif h₁ h₂])
  rcases this with ⟨g, hg, H⟩
  let g' : α →. γ := fun a ↦ (g (Encodable.encode a)).bind fun n ↦ Encodable.decode (α := γ) n
  refine ⟨g', ((nat_iff.2 hg).comp Computable.encode).bind (Computable.decode.ofOption.comp Computable.snd).to₂, ?_⟩
  have H : ∀ {c a : ℕ}, c ∈ g a ↔ ∃ a' b, Encodable.encode a' = a ∧ ∃ c' ∈ f a' b, Encodable.encode c' = c := by
    have H : ∀ (a m : ℕ),
      a ∈ g m ↔ ∃ z a' b, (Encodable.encode a' = m ∧ Encodable.encode b = z) ∧ ∃ a'' ∈ f a' b, Encodable.encode a'' = a := by
      simpa [Encodable.decode₂_eq_some] using H
    intro c a; constructor
    · intro h; rcases (H c a).mp h with ⟨b, a, b, ⟨rfl, rfl⟩, ⟨c, H, rfl⟩⟩
      exact ⟨a, b, rfl, c, H, rfl⟩
    · rintro ⟨a, b, rfl, c, hc, rfl⟩
      exact (H _ _).mpr ⟨Encodable.encode b, a, b, ⟨rfl, rfl⟩, c, hc, rfl⟩
  intro c a
  suffices (∃ c' ∈ g (Encodable.encode a), Encodable.decode c' = some c) ↔ ∃ b, c ∈ f a b by simpa [g']
  constructor
  · rintro ⟨c', h, hc⟩
    rcases H.mp h with ⟨a, b, ae, c, habc, rfl⟩;
    rcases by simpa using hc
    rcases Encodable.encode_inj.mp ae
    exact ⟨b, habc⟩
  · rintro ⟨b, habc⟩
    exact ⟨Encodable.encode c, H.mpr ⟨a, b, rfl, c, habc, rfl⟩, by simp⟩

end Partrec


namespace REPred

variable {α β : Type*} [Primcodable α] [Primcodable β] {p q : α → Prop}

@[simp]
protected lemma const (p : Prop) : REPred fun _ : α ↦ p := by
  by_cases h : p
  · simpa [h] using Partrec.some.dom_re
  · simpa [h] using (Partrec.none (α := α) (σ := α)).dom_re

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


namespace ComputablePred

variable {α β : Type*} [Primcodable α] [Primcodable β] {p q : α → Prop}

@[simp] protected lemma const (p : Prop) : ComputablePred fun _ : α ↦ p :=
  computable_iff_re_compl_re'.mpr ⟨REPred.const _, REPred.const _⟩

lemma and : ComputablePred p → ComputablePred q → ComputablePred fun x ↦ p x ∧ q x := by
  simp_rw [computable_iff_re_compl_re']
  rintro ⟨hp, hnp⟩
  rintro ⟨hq, hnq⟩
  refine ⟨hp.and hq, (hnp.or hnq).of_eq <| by grind⟩

lemma or : ComputablePred p → ComputablePred q → ComputablePred fun x ↦ p x ∨ q x := by
  simp_rw [computable_iff_re_compl_re']
  rintro ⟨hp, hnp⟩
  rintro ⟨hq, hnq⟩
  refine ⟨hp.or hq, (hnp.and hnq).of_eq <| by grind⟩

end ComputablePred

end
