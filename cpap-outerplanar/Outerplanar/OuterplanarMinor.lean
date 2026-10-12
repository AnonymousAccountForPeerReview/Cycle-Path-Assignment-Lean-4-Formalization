module

public import Outerplanar.OuterplanarMinorLists
public import Mathlib.Logic.Relation
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic

/-!
# Outerplanar drawings are closed under minors

The direction "an outerplanar drawing has no `K₄` and no `K_{2,3}` minor" of Lemma 19,
up to the two base facts `¬ OuterplanarDrawing k4`, `¬ OuterplanarDrawing k23`: a minor
`h` (on the vertices `0, …, size - 1`) of a graph `g` with an outerplanar drawing has an
outerplanar drawing (`OuterplanarDrawing.of_hasMinor`), given Euler's inequality for hypermaps
(`HypermapEuler`); hence, with the two base facts, an outerplanar drawing has neither minor
(`OuterplanarDrawing.outerplanar`).

The minor is realized by edge-list operations on an outerplanar embedding
(`OuterplanarMinorLists`). Minor data is carried on an arbitrary edge list `es`, with the
symmetric adjacency `LAdj` and connectivity of the branch sets as reflexive-transitive closure
(`ListMinor`). By induction on the total size of the branch sets (`weight`):

* if a branch set has two different vertices, it contains an edge `(s, t)` of `es`; contracting
  it (renaming `t` to `s`) keeps an outerplanar embedding and minor data with `t` removed from
  its branch set (`listMinor_contract`);
* otherwise every branch set `i` is a single vertex `t i`: keep the edges between these
  vertices, rename `t i` to `i`, write every edge smaller end first, and delete what is not an
  edge of the simple graph of `h` (`outerplanar_of_listMinor_const`).
-/

@[expose] public section

namespace STACS2027.OuterplanarMinor
open Complexity

/-! ## Facts on `simpleEdges`

The only three facts on the definition of `simpleEdges` used below: it is duplicate-free, its
entries are the normalized proper entries of the graph, and it contains every adjacency. -/

theorem nodup_eraseDups' {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → l.eraseDups.Nodup
  | _, [], _ => by simp
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨fun ha => ?_, nodup_eraseDups' n _
      (Nat.le_trans (List.length_filter_le _ _) (by simp at h; omega))⟩
    have := List.mem_filter.mp (List.mem_eraseDups.mp ha)
    simp at this

theorem simpleEdges_nodup (g : Graph) : (simpleEdges g).Nodup :=
  nodup_eraseDups' _ _ le_rfl

theorem exists_of_mem_simpleEdges {g : Graph} {e : Edge} (he : e ∈ simpleEdges g) :
    ∃ f ∈ g, f.1 ≠ f.2 ∧ e = edge f.1 f.2 := by
  simp only [simpleEdges, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq] at he
  refine ⟨e, he.1, Nat.ne_of_lt he.2, ?_⟩
  unfold edge; ext <;> simp <;> omega

theorem edge_mem_simpleEdges {g : Graph} {u v : ℕ} (h : Adj g u v) :
    edge u v ∈ simpleEdges g := by
  simp only [simpleEdges, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq]
  refine ⟨h.2, ?_⟩
  have := h.1
  simp only [edge]
  omega

/-! ## Minor data on an edge list -/

/-- Adjacency in an edge list, in either orientation. -/
def LAdj (es : List (ℕ × ℕ)) (u v : ℕ) : Prop := u ≠ v ∧ ((u, v) ∈ es ∨ (v, u) ∈ es)

/-- A step between two adjacent vertices of the branch set `B`. -/
def BStep (es : List (ℕ × ℕ)) (B : List ℕ) (a b : ℕ) : Prop := a ∈ B ∧ b ∈ B ∧ LAdj es a b

/-- `h` (its edges with two different ends) is a minor of the edge list `es` with the branch
sets `branch 0, …, branch (size - 1)`: nonempty, pairwise disjoint, connected, and with an
edge of `es` between the branch sets of the ends of every edge of `h`. -/
def ListMinor (es : List (ℕ × ℕ)) (size : ℕ) (h : Graph) (branch : ℕ → List ℕ) : Prop :=
  (∀ i, i < size → branch i ≠ []) ∧
  (∀ i j, i < size → j < size → i ≠ j → ∀ v, v ∈ branch i → v ∉ branch j) ∧
  (∀ i, i < size → ∀ u ∈ branch i, ∀ v ∈ branch i,
    Relation.ReflTransGen (BStep es (branch i)) u v) ∧
  (∀ e ∈ h, e.1 ≠ e.2 → ∃ u ∈ branch e.1, ∃ v ∈ branch e.2, LAdj es u v)

/-- The total size of the branch sets. -/
def weight (size : ℕ) (branch : ℕ → List ℕ) : ℕ := ∑ i ∈ Finset.range size, (branch i).length

theorem renameTo_self {u v : ℕ} : renameTo u v u = u := by
  unfold renameTo; split <;> simp_all

theorem renameTo_target {u v : ℕ} : renameTo u v v = u := by simp [renameTo]

theorem renameTo_of_ne {u v w : ℕ} (h : w ≠ v) : renameTo u v w = w := by simp [renameTo, h]

/-- **Contracting an edge inside a branch set** keeps minor data, with the contracted vertex
removed from its branch set. -/
theorem listMinor_contract {es : List (ℕ × ℕ)} {size : ℕ} {h : Graph} {branch : ℕ → List ℕ}
    (hm : ListMinor es size h branch) (hh : ∀ e ∈ h, e.1 < size ∧ e.2 < size)
    {i : ℕ} (hi : i < size) {s t : ℕ} (hs : s ∈ branch i) (ht : t ∈ branch i) (hst : s ≠ t) :
    ListMinor ((es.erase (s, t)).map fun e => (renameTo s t e.1, renameTo s t e.2)) size h
      (fun j => (branch j).filter fun w => decide (w ≠ t)) := by
  obtain ⟨hne, hdisj, hconn, hedges⟩ := hm
  set es' := (es.erase (s, t)).map fun e => (renameTo s t e.1, renameTo s t e.2) with hes'
  have hmem' : ∀ j w, w ∈ (branch j).filter (fun w => decide (w ≠ t)) ↔
      w ∈ branch j ∧ w ≠ t := by
    intro j w
    simp only [List.mem_filter, decide_eq_true_eq]
  -- adjacency survives the contraction, or the two ends are identified
  have hadj : ∀ a b, LAdj es a b →
      renameTo s t a = renameTo s t b ∨ LAdj es' (renameTo s t a) (renameTo s t b) := by
    intro a b hab
    by_cases hρ : renameTo s t a = renameTo s t b
    · exact Or.inl hρ
    · refine Or.inr ⟨hρ, ?_⟩
      have hne1 : (a, b) ≠ (s, t) := by
        intro he
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact hρ (by rw [renameTo_self, renameTo_target])
      have hne2 : (b, a) ≠ (s, t) := by
        intro he
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact hρ (by rw [renameTo_self, renameTo_target])
      rcases hab.2 with h1 | h1
      · exact Or.inl (List.mem_map.mpr ⟨(a, b), (List.mem_erase_of_ne hne1).mpr h1, rfl⟩)
      · exact Or.inr (List.mem_map.mpr ⟨(b, a), (List.mem_erase_of_ne hne2).mpr h1, rfl⟩)
  -- the renaming maps every branch set into its new version
  have hρmem : ∀ j, j < size → ∀ w ∈ branch j,
      renameTo s t w ∈ (branch j).filter (fun w => decide (w ≠ t)) := by
    intro j hj w hw
    rw [hmem']
    by_cases hwt : w = t
    · subst w
      have hji : j = i := by
        by_contra hji
        exact hdisj j i hj hi hji _ hw ht
      subst j
      rw [renameTo_target]
      exact ⟨hs, hst⟩
    · rw [renameTo_of_ne hwt]
      exact ⟨hw, hwt⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hji : j = i
    · subst j
      exact List.ne_nil_of_mem ((hmem' _ _).mpr ⟨hs, hst⟩)
    · obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ (hne j hj)
      have hwt : w ≠ t := by
        rintro rfl
        exact hdisj j i hj hi hji _ hw ht
      exact List.ne_nil_of_mem ((hmem' _ _).mpr ⟨hw, hwt⟩)
  · intro j k hj hk hjk v hv hv'
    exact hdisj j k hj hk hjk v ((hmem' _ _).mp hv).1 ((hmem' _ _).mp hv').1
  · intro j hj u hu v hv
    obtain ⟨hu, hut⟩ := (hmem' _ _).mp hu
    obtain ⟨hv, hvt⟩ := (hmem' _ _).mp hv
    have hstep : ∀ a b, BStep es (branch j) a b →
        Relation.ReflTransGen (BStep es' ((branch j).filter fun w => decide (w ≠ t)))
          (renameTo s t a) (renameTo s t b) := by
      intro a b hab
      obtain ⟨ha, hb, hab⟩ := hab
      rcases hadj a b hab with he | he
      · rw [he]
      · exact Relation.ReflTransGen.single ⟨hρmem j hj a ha, hρmem j hj b hb, he⟩
    have hr := Relation.ReflTransGen.lift' (renameTo s t) hstep u v (hconn j hj u hu v hv)
    change Relation.ReflTransGen _ (renameTo s t u) (renameTo s t v) at hr
    rwa [renameTo_of_ne hut, renameTo_of_ne hvt] at hr
  · intro e he hne'
    obtain ⟨u, hu, v, hv, huv⟩ := hedges e he hne'
    have h1 := hρmem e.1 (hh e he).1 u hu
    have h2 := hρmem e.2 (hh e he).2 v hv
    refine ⟨_, h1, _, h2, ?_⟩
    rcases hadj u v huv with h3 | h3
    · exfalso
      rw [h3] at h1
      exact hdisj e.1 e.2 (hh e he).1 (hh e he).2 hne' _ ((hmem' _ _).mp h1).1
        ((hmem' _ _).mp h2).1
    · exact h3

theorem weight_contract_lt {size : ℕ} {branch : ℕ → List ℕ} {i : ℕ} (hi : i < size) {t : ℕ}
    (ht : t ∈ branch i) :
    weight size (fun j => (branch j).filter fun w => decide (w ≠ t)) < weight size branch := by
  unfold weight
  apply Finset.sum_lt_sum
  · intro j _
    exact List.length_filter_le _ _
  · refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
    apply List.length_filter_lt_length_iff_exists.mpr
    exact ⟨t, ht, by simp⟩

/-- **The base case**: every branch set is a single vertex `t i`. Keep the edges between
these vertices, rename `t i` to `i`, write the edges smaller end first and delete the edges
outside the simple graph of `h`. -/
theorem outerplanar_of_listMinor_const (hE : HypermapEuler) {es : List (ℕ × ℕ)} {size : ℕ}
    {h : Graph} {branch : ℕ → List ℕ} (hh : ∀ e ∈ h, e.1 < size ∧ e.2 < size)
    (ho : OuterplanarEmbedding es) (hm : ListMinor es size h branch)
    (hc : ∀ i, i < size → ∀ p ∈ branch i, ∀ q ∈ branch i, p = q) :
    OuterplanarEmbedding (simpleEdges h) := by
  obtain ⟨hne, hdisj, -, hedges⟩ := hm
  let t : ℕ → ℕ := fun i => (branch i).headD 0
  have ht : ∀ i, i < size → t i ∈ branch i := by
    intro i hi
    have := hne i hi
    simp only [t]
    cases hb : branch i with
    | nil => exact absurd hb this
    | cons a l => simp
  have htw : ∀ i, i < size → ∀ w ∈ branch i, w = t i :=
    fun i hi w hw => hc i hi w hw (t i) (ht i hi)
  have htinj : ∀ i j, i < size → j < size → t i = t j → i = j := by
    intro i j hi hj hij
    by_contra hne
    exact hdisj i j hi hj hne _ (ht i hi) (hij ▸ ht j hj)
  have hedge : ∀ e ∈ h, e.1 ≠ e.2 → LAdj es (t e.1) (t e.2) := by
    intro e he hne'
    obtain ⟨u, hu, v, hv, huv⟩ := hedges e he hne'
    rwa [← htw e.1 (hh e he).1 u hu, ← htw e.2 (hh e he).2 v hv]
  let T : List ℕ := (List.range size).map t
  have hT : ∀ w, w ∈ T ↔ ∃ i, i < size ∧ t i = w := by
    intro w
    simp only [T, List.mem_map, List.mem_range]
  have hTnd : T.Nodup := by
    apply List.Nodup.map_on _ List.nodup_range
    intro i hi j hj hij
    exact htinj i j (List.mem_range.mp hi) (List.mem_range.mp hj) hij
  have hσ : ∀ i, i < size → T.idxOf (t i) = i := by
    intro i hi
    have hiT : i < T.length := by simp [T, hi]
    have h1 : T[i] = t i := by simp [T]
    have h2 := List.get_idxOf hTnd ⟨i, hiT⟩
    simp only [List.get_eq_getElem, h1] at h2
    exact h2
  let es1 := es.filter fun f => decide (f.1 ∈ T ∧ f.2 ∈ T)
  have ho1 : OuterplanarEmbedding es1 := ho.sublist hE List.filter_sublist
  have hends : ∀ a, (∃ e ∈ es1, a = e.1 ∨ a = e.2) → a ∈ T := by
    rintro a ⟨e, he, hae⟩
    have he' := (List.mem_filter.mp he).2
    simp only [decide_eq_true_eq] at he'
    rcases hae with rfl | rfl
    · exact he'.1
    · exact he'.2
  have ho2 := ho1.map_injOn (fun w => T.idxOf w) (by
    intro a b ha hb hab
    obtain ⟨i, hi, rfl⟩ := (hT a).mp (hends a ha)
    obtain ⟨j, hj, rfl⟩ := (hT b).mp (hends b hb)
    simp only [hσ i hi, hσ j hj] at hab
    rw [hab])
  have ho3 := ho2.canonical
  apply ho3.subperm hE
  apply (simpleEdges_nodup h).subperm
  intro e he
  obtain ⟨f, hf, hfne, rfl⟩ := exists_of_mem_simpleEdges he
  have h1 := (hh f hf).1
  have h2 := (hh f hf).2
  have hT1 : t f.1 ∈ T := (hT _).mpr ⟨_, h1, rfl⟩
  have hT2 : t f.2 ∈ T := (hT _).mpr ⟨_, h2, rfl⟩
  simp only [List.map_map, List.mem_map, Function.comp_apply]
  rcases (hedge f hf hfne).2 with hm | hm
  · refine ⟨(t f.1, t f.2), List.mem_filter.mpr ⟨hm, by simp [hT1, hT2]⟩, ?_⟩
    simp only [hσ _ h1, hσ _ h2]
  · refine ⟨(t f.2, t f.1), List.mem_filter.mpr ⟨hm, by simp [hT1, hT2]⟩, ?_⟩
    simp only [hσ _ h1, hσ _ h2, edge]
    rw [Nat.min_comm, Nat.max_comm]

/-- **Minors of outerplanar embeddings**, on edge lists, by induction on the total size of
the branch sets. -/
theorem outerplanar_of_listMinor (hE : HypermapEuler) {size : ℕ} {h : Graph}
    (hh : ∀ e ∈ h, e.1 < size ∧ e.2 < size) :
    ∀ (N : ℕ) (es : List (ℕ × ℕ)) (branch : ℕ → List ℕ), weight size branch = N →
      OuterplanarEmbedding es → ListMinor es size h branch →
        OuterplanarEmbedding (simpleEdges h) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro es branch hw ho hm
    by_cases hc : ∃ i, i < size ∧ ∃ p ∈ branch i, ∃ q ∈ branch i, p ≠ q
    · obtain ⟨i, hi, p, hp, q, hq, hpq⟩ := hc
      obtain ⟨s, t, hs, ht, hst, hmem⟩ : ∃ s t, s ∈ branch i ∧ t ∈ branch i ∧ s ≠ t ∧
          (s, t) ∈ es := by
        rcases Relation.ReflTransGen.cases_head (hm.2.2.1 i hi p hp q hq) with he | ⟨c, hc, -⟩
        · exact absurd he hpq
        · obtain ⟨hp', hc', hne, hpc | hcp⟩ := hc
          · exact ⟨p, c, hp', hc', hne, hpc⟩
          · exact ⟨c, p, hc', hp', Ne.symm hne, hcp⟩
      exact ih _ (hw ▸ weight_contract_lt hi ht) _ _ rfl (ho.contract hst hmem)
        (listMinor_contract hm hh hi hs ht hst)
    · refine outerplanar_of_listMinor_const hE hh ho hm ?_
      intro i hi p hp q hq
      by_contra hpq
      exact hc ⟨i, hi, p, hp, q, hq, hpq⟩

/-- A walk within `S` gives a chain of adjacent vertices of `S`. -/
theorem reflTransGen_of_walk {g : Graph} {S : ℕ → Prop} :
    ∀ (w : List ℕ) (u v : ℕ), WalkWithin g S w → w.head? = some u → w.getLast? = some v →
      Relation.ReflTransGen (fun a b => S a ∧ S b ∧ Adj g a b) u v
  | [], _, _, _, hu, _ => by simp at hu
  | [a], u, v, hw, hu, hv => by
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at hu hv
    subst hu hv
    exact Relation.ReflTransGen.refl
  | a :: b :: rest, u, v, hw, hu, hv => by
    obtain ⟨ha, hab, hw'⟩ := hw
    simp only [List.head?_cons, Option.some.injEq] at hu
    subst hu
    have hb : S b := by
      cases rest with
      | nil => exact hw'
      | cons c rest => exact hw'.1
    have hv' : (b :: rest).getLast? = some v := by
      rw [List.getLast?_cons_cons] at hv
      exact hv
    exact Relation.ReflTransGen.head ⟨ha, hb, hab⟩
      (reflTransGen_of_walk (b :: rest) b v hw' rfl hv')

end STACS2027.OuterplanarMinor

namespace STACS2027
open STACS2027.OuterplanarMinor

/-- **Outerplanar drawings are closed under minors** (given Euler's inequality for
hypermaps): if `g` has an outerplanar drawing and `h`, a graph on the vertices
`0, …, size - 1`, is a minor of `g`, then `h` has an outerplanar drawing. -/
theorem OuterplanarDrawing.of_hasMinor (hE : HypermapEuler) {g h : Graph} {size : ℕ}
    (hg : OuterplanarDrawing g) (hm : HasMinor g size h)
    (hh : ∀ e ∈ h, e.1 < size ∧ e.2 < size) : OuterplanarDrawing h := by
  obtain ⟨branch, h1, h2, h3, h4⟩ := hm
  have hladj : ∀ u v, Adj g u v → LAdj (simpleEdges g) u v := by
    intro u v huv
    refine ⟨huv.1, ?_⟩
    have he := edge_mem_simpleEdges huv
    by_cases hle : u ≤ v
    · left
      have : edge u v = (u, v) := by simp [edge, Nat.min_eq_left hle, Nat.max_eq_right hle]
      rwa [this] at he
    · right
      have : edge u v = (v, u) := by
        simp [edge, Nat.min_eq_right (by omega : v ≤ u), Nat.max_eq_left (by omega : v ≤ u)]
      rwa [this] at he
  refine outerplanar_of_listMinor hE hh _ (simpleEdges g) branch rfl hg ⟨h1, h2, ?_, ?_⟩
  · intro i hi u hu v hv
    obtain ⟨w, hw1, hw2, hw⟩ := h3 i hi u v hu hv
    have hmono : ∀ a b, (a ∈ branch i ∧ b ∈ branch i ∧ Adj g a b) →
        BStep (simpleEdges g) (branch i) a b :=
      fun a b hab => ⟨hab.1, hab.2.1, hladj a b hab.2.2⟩
    exact Relation.ReflTransGen.mono hmono u v (reflTransGen_of_walk w u v hw hw1 hw2)
  · intro e he _
    obtain ⟨u, v, hu, hv, huv⟩ := h4 e he
    exact ⟨u, hu, v, hv, hladj u v huv⟩

/-- A graph without an outerplanar drawing is not a minor of a graph with one. -/
theorem OuterplanarDrawing.not_hasMinor (hE : HypermapEuler) {g h : Graph} {size : ℕ}
    (hg : OuterplanarDrawing g) (hh : ∀ e ∈ h, e.1 < size ∧ e.2 < size)
    (hn : ¬ OuterplanarDrawing h) : ¬ HasMinor g size h :=
  fun hm => hn (hg.of_hasMinor hE hm hh)

/-- **An outerplanar drawing has no `K₄` and no `K_{2,3}` minor**, given Euler's inequality
for hypermaps and that `K₄` and `K_{2,3}` have no outerplanar drawing. -/
theorem OuterplanarDrawing.outerplanar (hE : HypermapEuler) (h4 : ¬ OuterplanarDrawing k4)
    (h23 : ¬ OuterplanarDrawing k23) {g : Graph} (hg : OuterplanarDrawing g) :
    Outerplanar g :=
  ⟨hg.not_hasMinor hE (by decide) h4, hg.not_hasMinor hE (by decide) h23⟩

end STACS2027
