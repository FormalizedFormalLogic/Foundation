import Logic.Vorspiel.Computability
import Mathlib.Data.List.Sigma

attribute [-instance] WType.instEncodable Encodable.finPi Encodable.fintypeArrowOfEncodable

open Encodable
variable {α β γ σ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

namespace List

variable {α : Type u} [DecidableEq α]

lemma lookup_map_fun_of_mem (f : α → β) {a : α} {as : List α} (h : a ∈ as) :
    lookup a (as.map $ fun x => (x, f x)) = some (f a) := by
  induction' as with a' as ih
  · simp at h
  · simp at h
    have : a = a' ∨ (a ≠ a' ∧ a ∈ as) := by { by_cases ha : a = a'; { simp[ha] }; { simp[ha] at h; exact Or.inr ⟨ha, h⟩ } }
    rcases this with (rfl | ⟨hne, hmem⟩) <;> simp[lookup]
    · simp[beq_false_of_ne hne, ih hmem]

def mapGraph (M : List (α × β)) (as : List α) : List β := as.bind (Option.toList <| M.lookup ·)

lemma mapGraph_graph (f : α → β) {as as' : List α} (has : as' ⊆ as) :
    mapGraph (as.map $ fun x => (x, f x)) as' = as'.map f := by
  induction' as' with a as' ih <;> simp[mapGraph]
  · have : a ∈ as ∧ as' ⊆ as := by simpa using has
    rcases this with ⟨ha, has'⟩
    simp[lookup_map_fun_of_mem f ha]; exact ih has'

lemma subset_bind_of_mem {a : α} {as : List α} (h : a ∈ as) (f : α → List α) : f a ⊆ as.bind f := by
  intro a' ha'; simpa using ⟨a, h, ha'⟩

end List

namespace Primrec

lemma nat_rec'' {f : α → ℕ} {g : α → β} {h : α → ℕ → β → β}
  (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ (fun a (p : ℕ × β) => h a p.1 p.2)) :
  Primrec (fun a => @Nat.rec _ (g a) (h a) (f a)) := nat_rec' hf hg hh

lemma option_toList : Primrec (Option.toList : Option α → List α) := by
  have : Primrec (fun a => [a] : α → List α) := list_cons.comp Primrec.id (const [])
  exact (option_casesOn Primrec.id (const []) (this.comp₂ Primrec₂.right)).of_eq
    (fun o => by rcases o <;> simp)

lemma iterate {f : α → α} (hf : Primrec f) : Primrec₂ (f^[·] ·) := by
  have : Primrec₂ (fun s a => s.rec a (fun _ => f) : ℕ → α → α) :=
    to₂ (nat_rec' fst snd (hf.comp₂ (snd.comp₂ Primrec₂.right)))
  exact this.of_eq (fun s a => by
    induction' s with s ih <;> simp[*]; { exact Eq.symm (Function.iterate_succ_apply' f s a) })

lemma list_take : Primrec₂ (List.take : ℕ → List α → List α) := by
  have : Primrec₂ (fun s a => s.rec [] (fun n as => as ++ (a.get? n).toList) : ℕ → List α → List α) :=
    to₂ (nat_rec' fst (const [])
      (list_append.comp₂ (snd.comp₂ Primrec₂.right)
        (option_toList.comp₂ $ list_get?.comp₂ (snd.comp₂ Primrec₂.left) (fst.comp₂ Primrec₂.right))))
  exact this.of_eq (fun n as => by induction' n with n ih <;> simp[List.take_succ, *])

lemma nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

lemma list_lookup [DecidableEq α] : Primrec₂ (List.lookup : α → List (α × β) → Option β) := by
  have : Primrec₂ (fun p q => bif p.1 == q.1.1 then q.1.2 else q.2.2 : α × List (α × β) → (α × β) × List (α × β) × Option β → Option β) :=
    cond (Primrec.beq.comp (fst.comp fst) (fst.comp $ fst.comp snd))
      (option_some.comp $ snd.comp $ fst.comp snd) (snd.comp $ snd.comp snd)
  have : Primrec₂ (fun a l => List.recOn l none (fun p _ ih => bif a == p.1 then p.2 else ih) : α → List (α × β) → Option β) :=
    to₂ <| list_rec snd (const none) this
  exact this.of_eq <| fun a ps => by
    induction' ps with p ps <;> simp[List.lookup, *]
    cases ha : a == p.1 <;> simp[ha]

lemma list_mapGraph [DecidableEq α] : Primrec₂ (List.mapGraph : List (α × β) → List α → List β) :=
  to₂ <| list_bind snd (option_toList.comp₂ $ list_lookup.comp₂ Primrec₂.right (fst.comp₂ Primrec₂.left))

lemma nat_omega_rec_prod [DecidableEq α] {t : α → ℕ → α} (f : α → ℕ → σ) {g : α × ℕ → List σ → Option σ}
  (ht : Primrec₂ t) (hg : Primrec₂ g)
  (H : ∀ a k, g (a, k) ((List.range k).map (f (t a k))) = some (f a k)) : Primrec₂ f := by
  have hm : Primrec (fun p => p.2 : α × ℕ → ℕ) := snd
  have hl : Primrec (fun p => (List.range p.2).map fun x => (t p.1 p.2, x) : α × ℕ → List (α × ℕ)) :=
    list_map (list_range.comp snd) (Primrec₂.pair.comp₂ (ht.comp₂ (fst.comp₂ Primrec₂.left) (snd.comp₂ Primrec₂.left)) Primrec₂.right)
  have := nat_omega_rec' (fun (p : α × ℕ) => f p.1 p.2) hm hl hg (by simp) (by rintro ⟨a, k⟩; simp[Function.comp, H])
  exact to₂ this

end Primrec
