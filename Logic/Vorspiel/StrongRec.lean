import Logic.Vorspiel.Computability

attribute [-instance] WType.instEncodableWType Encodable.finPi Encodable.fintypeArrowOfEncodable

open Encodable
variable {α β γ σ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

namespace List

variable {α : Type u} [DecidableEq α]

def dlookup' (a : α) : List (α × β) → Option β
  | []           => none
  | (a', b) :: l => if a' = a then some b else dlookup' a l

lemma dlookup'_map_fun_of_mem (f : α → β) {a : α} {as : List α} (h : a ∈ as) :
    dlookup' a (as.map $ fun x => (x, f x)) = some (f a) := by
  induction' as with a' as ih
  · simp at h
  · have : a = a' ∨ (a ≠ a' ∧ a ∈ as) := by { by_cases ha : a = a'; { simp[ha] }; { simp[ha] at h; exact Or.inr ⟨ha, h⟩ } }
    rcases this with (rfl | ⟨hne, hmem⟩) <;> simp[dlookup']
    · simp[hne.symm, ih hmem]

def mapGraph (M : List (α × β)) (as : List α) : List β := as.bind (Option.toList <| M.dlookup' ·)

lemma mapGraph_graph (f : α → β) {as as' : List α} (has : as' ⊆ as) :
    mapGraph (as.map $ fun x => (x, f x)) as' = as'.map f := by
  induction' as' with a as' ih <;> simp[mapGraph]
  · have : a ∈ as ∧ as' ⊆ as := by simpa using has
    rcases this with ⟨ha, has'⟩
    simp[dlookup'_map_fun_of_mem f ha]; exact ih has'

lemma subset_bind_of_mem {a : α} {as : List α} (h : a ∈ as) (f : α → List α) : f a ⊆ as.bind f := by
  unfold List.bind; simp[List.subset_def]; intro a' ha'; exact ⟨a, h, ha'⟩

end List

namespace Primrec

lemma nat_rec'' {f : α → ℕ} {g : α → β} {h : α → ℕ → β → β}
  (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ (fun a (p : ℕ × β) => h a p.1 p.2)) :
  Primrec (fun a => @Nat.rec _ (g a) (h a) (f a)) := nat_rec' hf hg hh

lemma list_bind {f : α → List β} {g : α → β → List σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).bind (g a)) := list_join.comp (list_map hf hg)

lemma option_toList : Primrec (Option.toList : Option α → List α) := by
  have : Primrec (fun a => [a] : α → List α) := list_cons.comp Primrec.id (const [])
  exact (option_casesOn Primrec.id (const []) (this.comp₂ Primrec₂.right)).of_eq
    (fun o => by rcases o <;> simp)

lemma iterate {f : α → α} (hf : Primrec f) : Primrec₂ (f^[·] ·) := by
  have : Primrec₂ (fun s a => s.rec a (fun _ => f) : ℕ → α → α) :=
    to₂' (nat_rec' fst snd (hf.comp₂ (snd.comp₂ Primrec₂.right)))
  exact this.of_eq (fun s a => by
    induction' s with s ih <;> simp[*]; { exact Eq.symm (Function.iterate_succ_apply' f s a) })

lemma list_take : Primrec₂ (List.take : ℕ → List α → List α) := by
  have : Primrec₂ (fun s a => s.rec [] (fun n as => as ++ (a.get? n).toList) : ℕ → List α → List α) :=
    to₂' (nat_rec' fst (const [])
      (list_append.comp₂ (snd.comp₂ Primrec₂.right)
        (option_toList.comp₂ $ list_get?.comp₂ (snd.comp₂ Primrec₂.left) (fst.comp₂ Primrec₂.right))))
  exact this.of_eq (fun n as => by induction' n with n ih <;> simp[List.take_succ, *])

lemma nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

lemma list_dlookup' [DecidableEq α] : Primrec₂ (List.dlookup' : α → List (α × β) → Option β) := by
  have : Primrec₂ (fun p q => if q.1.1 = p.1 then q.1.2 else q.2.2 : α × List (α × β) → (α × β) × List (α × β) × Option β → Option β) :=
    ite (Primrec.eq.comp (fst.comp $ fst.comp snd) (fst.comp fst))
      (option_some.comp $ snd.comp $ fst.comp snd) (snd.comp $ snd.comp snd)
  have : Primrec₂ (fun a l => List.recOn l none (fun p _ ih => if p.1 = a then p.2 else ih) : α → List (α × β) → Option β) :=
    to₂ <| list_rec snd (const none) this
  exact this.of_eq <| fun a ps => by
    induction' ps with p ps <;> simp[List.dlookup', *]

lemma list_mapGraph [DecidableEq α] : Primrec₂ (List.mapGraph : List (α × β) → List α → List β) :=
  to₂ <| list_bind snd (option_toList.comp₂ $ list_dlookup'.comp₂ Primrec₂.right (fst.comp₂ Primrec₂.left))

section strong_rec

variable [DecidableEq α]

private def hist (l : α → List α) (a : α) : ℕ → List α := fun n => n.rec [a] (fun _ as => as.bind l)

private def graph (m : α → ℕ) (l : α → List α) (g : α → List σ → Option σ) (a : α) : ℕ → List (α × σ) :=
  fun i => i.rec [] (fun i ih => (hist l a (m a - i)).bind $ fun a' => Option.toList <| (g a' $ ih.mapGraph (l a')).map (a', ·))

private lemma hist_primrec {l : α → List α} (hl : Primrec l) : Primrec₂ (hist l) :=
  nat_rec'' snd (list_cons.comp fst (const [])) (list_bind (snd.comp snd) (hl.comp₂ Primrec₂.right))

private lemma graph_primrec {m : α → ℕ} {l : α → List α} {g : α → List σ → Option σ}
  (hm : Primrec m) (hl : Primrec l) (hg : Primrec₂ g) : Primrec₂ (graph m l g) :=
  to₂' <| nat_rec'' snd (const [])
    <| to₂' <| list_bind ((hist_primrec hl).comp (fst.comp fst) (nat_sub.comp (hm.comp $ fst.comp fst) (fst.comp snd)))
    <| option_toList.comp₂ <| to₂' <| option_map (hg.comp snd (list_mapGraph.comp (snd.comp $ snd.comp fst) (hl.comp snd)))
    <| (Primrec₂.pair.comp₂ (snd.comp₂ Primrec₂.left) Primrec₂.right)

private lemma hist_m_lt (m : α → ℕ) (l : α → List α) (a : α) (Ord : ∀ a, ∀ a' ∈ l a, m a' < m a) (k) :
    ∀ a' ∈ hist l a k, m a' < m a + 1 - k := by
  induction' k with k ih <;> simp[hist]
  { intro a₂ a₁ ha₁ ha₂
    have : m a₁ ≤ m a - k
    { have : 0 < m a + 1 - k := by exact Nat.zero_lt_of_lt (ih a₁ ha₁)
      have : k ≤ m a := Nat.lt_succ.mp (by simpa using Nat.add_lt_of_lt_sub this)
      apply Nat.lt_succ.mp (by simp[←Nat.succ_sub this]; exact ih a₁ ha₁) }
    exact lt_of_lt_of_le (Ord a₁ a₂ ha₂) this }

private lemma hist_eq_nil (m : α → ℕ) (l : α → List α) (a : α) (Ord : ∀ a, ∀ a' ∈ l a, m a' < m a) :
    hist l a (m a + 1) = [] :=
  List.eq_nil_iff_forall_not_mem.mpr (by intro a' ha'; by_contra; simpa using hist_m_lt m l a Ord (m a + 1) a' ha')

private lemma graph_eq (m : α → ℕ) (f : α → σ) (l : α → List α) (g : α → List σ → Option σ) (a : α)
  (Ord : ∀ a, ∀ a' ∈ l a, m a' < m a) (H : ∀ a, g a ((l a).map f) = some (f a)) :
    ∀ i ≤ m a + 1, graph m l g a i = (hist l a (m a + 1 - i)).map (fun x => (x, f x)) := by
  have graph_succ : ∀ i, graph m l g a (i + 1) =
    (hist l a (m a - i)).bind fun a' => Option.toList <| (g a' $ (graph m l g a i).mapGraph (l a')).map (a', ·) := by intro i; rfl
  have hist_succ : ∀ i, hist l a (i + 1) = (hist l a i).bind l := by intro i; rfl
  intro i hi
  induction' i with i ih <;> simp
  · simp[graph, hist_eq_nil m l a Ord]
  · simp[graph_succ, hist_succ, ih (Nat.le_of_lt hi), Nat.succ_sub (Nat.lt_succ.mp hi)]
    rw[List.bind_toList_some]
    { intro a' ha'; simp; rw[List.mapGraph_graph]
      · exact H a'
      · exact List.subset_bind_of_mem ha' l }

lemma strong_rec {m : α → ℕ} (f : α → σ) {l : α → List α} {g : α → List σ → Option σ}
  (hm : Primrec m) (hl : Primrec l) (hg : Primrec₂ g)
  (Ord : ∀ a, ∀ a' ∈ l a, m a' < m a)
  (H : ∀ a, g a ((l a).map f) = some (f a)) : Primrec f := by
  have : Primrec (fun a => ((graph m l g a (m a + 1)).get? 0).map Prod.snd) :=
    option_map (list_get?.comp ((graph_primrec hm hl hg).comp Primrec.id (succ.comp hm)) (const 0)) (snd.comp₂ Primrec₂.right)
  exact option_some_iff.mp <| this.of_eq <| fun a => by simp[graph_eq m f l g a Ord H (m a + 1) (by rfl)]

end strong_rec

lemma strong_rec_prod [DecidableEq α] {t : α → ℕ → α} (f : α → ℕ → σ) {g : α × ℕ → List σ → Option σ}
  (ht : Primrec₂ t) (hg : Primrec₂ g)
  (H : ∀ a k, g (a, k) ((List.range k).map (f (t a k))) = some (f a k)) : Primrec₂ f := by
  have hm : Primrec (fun p => p.2 : α × ℕ → ℕ) := snd
  have hl : Primrec (fun p => (List.range p.2).map fun x => (t p.1 p.2, x) : α × ℕ → List (α × ℕ)) :=
    list_map (list_range.comp snd) (Primrec₂.pair.comp₂ (ht.comp₂ (fst.comp₂ Primrec₂.left) (snd.comp₂ Primrec₂.left)) Primrec₂.right)
  have := strong_rec (fun (p : α × ℕ) => f p.1 p.2) hm hl hg (by simp) (by rintro ⟨a, k⟩; simp[Function.comp, H])
  exact to₂ this

end Primrec
