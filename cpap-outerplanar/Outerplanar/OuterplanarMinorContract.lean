module

public import Outerplanar.OuterplanarMinorDelete
public import NPHardness.PlanarRelabel

/-!
# Outerplanar embeddings are closed under edge contraction

The second hypermap-level half of the closure of outerplanar drawings under minors
(Lemma 19). Contracting an edge `{a, b}` whose two darts lie at different vertices
(`contract`): the edge pair becomes two darts fixed by `edge`, the `node` permutation is
composed with the transposition of `face b` and `face a` (the `node` predecessors of `a` and
`b`), which merges the two vertices into one, and the faces are unchanged. Then the two fixed
darts are excised by Section 5's `shrinkLast`.

* `contract_planar`: the contraction of a planar hypermap is planar (one more `edge` cycle,
  one fewer `node` cycle, the same faces and components);
* `outerFaces_contract`: faces are unchanged and vertices only merge, so every component
  still has a face meeting all its vertices;
* `OuterplanarEmbedding.contractLast`: contracting the last edge `(u, v)`, `u ≠ v`, of an
  outerplanar embedding gives an outerplanar embedding of the remaining edges with `v`
  renamed `u`.
-/

@[expose] public section

namespace STACS2027.OuterplanarMinor
open Complexity Complexity.Planar STACS2027.PlanarGluing STACS2027.PlanarPreprocess
open STACS2027.PlanarPreprocess.Deletion

theorem node_face_a {n : Nat} (G : Hypermap n) (a b : Fin n) (hb : G.edge b = a) :
    G.node (G.face a) = b := by
  have h := G.edgeK b
  rwa [hb] at h

theorem node_face_b {n : Nat} (G : Hypermap n) (a b : Fin n) (ha : G.edge a = b) :
    G.node (G.face b) = a := by
  have h := G.edgeK a
  rwa [ha] at h

theorem face_b_ne_face_a {n : Nat} (G : Hypermap n) (a b : Fin n) (hab : a ≠ b) :
    G.face b ≠ G.face a := fun h => hab (hm_face_inj G _ _ h).symm

/-- The vertices of `a` and `b` are different `node` cycles. -/
theorem contract_sep {n : Nat} (G : Hypermap n) (a b : Fin n) (ha : G.edge a = b)
    (hb : G.edge b = a) (hv : ¬ Reaches G.node a b) :
    cmin G.node (G.face b) ≠ cmin G.node (G.face a) := by
  intro h
  apply hv
  have h1 : Reaches G.node (G.face b) (G.face a) :=
    (cmin_eq_iff_reaches (hm_node_inj G) _ _).mp h
  have h2 : Reaches G.node (G.face b) a := ⟨1, node_face_b G a b ha⟩
  have h3 : Reaches G.node (G.face a) b := ⟨1, node_face_a G a b hb⟩
  exact (h2.symm (hm_node_inj G)).trans (h1.trans h3)

section Contract

variable {n : Nat} (G : Hypermap n) (a b : Fin n) (hab : a ≠ b) (ha : G.edge a = b)
  (hb : G.edge b = a)

/-- **Contracting the edge `{a, b}`**: its darts become fixed by `edge`, the vertices of `a`
and `b` are merged (the `node` permutation is composed with the transposition of their
`node` predecessors `face b` and `face a`), and the faces are unchanged. -/
def contract : Hypermap n where
  edge := transpose G.edge a b
  node := transpose G.node (G.face b) (G.face a)
  face := G.face
  edgeK x := by
    by_cases hxa : x = a
    · subst x
      rw [transpose_a, hb, transpose_b _ (face_b_ne_face_a G a b hab)]
      exact node_face_b G a b ha
    · by_cases hxb : x = b
      · subst x
        rw [transpose_b _ hab, ha, transpose_a]
        exact node_face_a G a b hb
      · rw [transpose_other _ hxa hxb]
        have h1 : G.face (G.edge x) ≠ G.face b := by
          intro h
          exact hxa (hm_edge_inj G _ _ ((hm_face_inj G _ _ h).trans ha.symm))
        have h2 : G.face (G.edge x) ≠ G.face a := by
          intro h
          exact hxb (hm_edge_inj G _ _ ((hm_face_inj G _ _ h).trans hb.symm))
        rw [transpose_other _ h1 h2]
        exact G.edgeK x

theorem contract_node_inj :
    ∀ x y, (contract G a b hab ha hb).node x = (contract G a b hab ha hb).node y → x = y :=
  transpose_injective (hm_node_inj G) _ _

theorem contract_node_face_b : (contract G a b hab ha hb).node (G.face b) = b := by
  change transpose G.node (G.face b) (G.face a) (G.face b) = b
  rw [transpose_a]
  exact node_face_a G a b hb

theorem contract_node_face_a : (contract G a b hab ha hb).node (G.face a) = a := by
  change transpose G.node (G.face b) (G.face a) (G.face a) = a
  rw [transpose_b _ (face_b_ne_face_a G a b hab)]
  exact node_face_b G a b ha

/-- Vertices only merge: a `node` orbit of `G` is within a `node` orbit of the contraction. -/
theorem contract_node_reaches (hv : ¬ Reaches G.node a b) {x y : Fin n}
    (h : Reaches G.node x y) : Reaches (contract G a b hab ha hb).node x y :=
  transpose_merge_orbit (hm_node_inj G) _ _ (contract_sep G a b ha hb hv) h

/-- The vertices of `a` and `b` are merged. -/
theorem contract_node_ab (hv : ¬ Reaches G.node a b) :
    Reaches (contract G a b hab ha hb).node a b := by
  have hm : Reaches (contract G a b hab ha hb).node (G.face b) (G.face a) :=
    transpose_merge_markers (hm_node_inj G) _ _ (contract_sep G a b ha hb hv)
  have h1 : Reaches (contract G a b hab ha hb).node (G.face b) a :=
    hm.trans ⟨1, contract_node_face_a G a b hab ha hb⟩
  have h2 : Reaches (contract G a b hab ha hb).node (G.face b) b :=
    ⟨1, contract_node_face_b G a b hab ha hb⟩
  exact (h1.symm (contract_node_inj G a b hab ha hb)).trans h2

/-- A labelling constant on the vertices of `G` and equal at `a` and `b` is constant on the
vertices of the contraction. -/
theorem contract_node_invariant {β : Type} (φ : Fin n → β) (hφ : ∀ z, φ (G.node z) = φ z)
    (hab' : φ a = φ b) (z : Fin n) : φ ((contract G a b hab ha hb).node z) = φ z := by
  by_cases hz1 : z = G.face b
  · subst z
    rw [contract_node_face_b, ← hab', ← hφ (G.face b), node_face_b G a b ha]
  · by_cases hz2 : z = G.face a
    · subst z
      rw [contract_node_face_a, hab', ← hφ (G.face a), node_face_a G a b hb]
    · change φ (transpose G.node (G.face b) (G.face a) z) = φ z
      rw [transpose_other _ hz1 hz2, hφ]

/-- Every step of the contraction is a path of `G`. -/
theorem contract_step_lift {x y : Fin n} (hs : Linked.Step (contract G a b hab ha hb) x y) :
    LinkedPath G x y := by
  rcases hs with hs | hs | hs
  · exact cut_step_lift G a b hab ha hb (Or.inl hs)
  · change transpose G.node (G.face b) (G.face a) x = y at hs
    by_cases hx1 : x = G.face b
    · subst x
      rw [transpose_a, node_face_a G a b hb] at hs
      subst hs
      exact (LinkedPath.step G (Or.inr (Or.inl (node_face_b G a b ha)))).trans
        (LinkedPath.step G (Or.inl ha))
    · by_cases hx2 : x = G.face a
      · subst x
        rw [transpose_b _ (face_b_ne_face_a G a b hab), node_face_b G a b ha] at hs
        subst hs
        exact (LinkedPath.step G (Or.inr (Or.inl (node_face_a G a b hb)))).trans
          (LinkedPath.step G (Or.inl hb))
      · rw [transpose_other _ hx1 hx2] at hs
        exact LinkedPath.step G (Or.inr (Or.inl hs))
  · exact LinkedPath.step G (Or.inr (Or.inr hs))

/-- Every step of `G` is a path of the contraction. -/
theorem contract_step_of (hv : ¬ Reaches G.node a b) {x y : Fin n} (hs : Linked.Step G x y) :
    LinkedPath (contract G a b hab ha hb) x y := by
  have hab' : LinkedPath (contract G a b hab ha hb) a b :=
    nodeOrbit_linked _ (contract_node_ab G a b hab ha hb hv)
  have hfa : LinkedPath (contract G a b hab ha hb) a (G.face a) :=
    LinkedPath.step _ (Or.inr (Or.inr rfl))
  have hfb : LinkedPath (contract G a b hab ha hb) b (G.face b) :=
    LinkedPath.step _ (Or.inr (Or.inr rfl))
  rcases hs with hs | hs | hs
  · by_cases hxa : x = a
    · subst x; rw [ha] at hs; subst hs; exact hab'
    · by_cases hxb : x = b
      · subst x; rw [hb] at hs; subst hs; exact hab'.symm
      · exact LinkedPath.step _ (Or.inl ((transpose_other G.edge hxa hxb).trans hs))
  · by_cases hx1 : x = G.face b
    · subst x; rw [node_face_b G a b ha] at hs; subst hs
      exact hfb.symm.trans hab'.symm
    · by_cases hx2 : x = G.face a
      · subst x; rw [node_face_a G a b hb] at hs; subst hs
        exact hfa.symm.trans hab'
      · exact LinkedPath.step _ (Or.inr (Or.inl ((transpose_other G.node hx1 hx2).trans hs)))
  · exact LinkedPath.step _ (Or.inr (Or.inr hs))

/-- **The contraction of a planar hypermap is planar.** -/
theorem contract_planar (hv : ¬ Reaches G.node a b) (hP : G.Planar) :
    (contract G a b hab ha hb).Planar := by
  have hC := componentCount_le_of_steps
    (fun _ _ hs => contract_step_of G a b hab ha hb hv hs)
  have heSame : cmin G.edge a = cmin G.edge b :=
    (cmin_eq_iff_reaches (hm_edge_inj G) a b).mpr ⟨1, ha⟩
  have hEc := transpose_split_cycles (hm_edge_inj G) a b hab heSame
  have hNc := transpose_merge_cycles (hm_node_inj G) _ _ (contract_sep G a b ha hb hv)
  rw [planar_iff] at hP ⊢
  unfold Hypermap.eulerRhs at hP ⊢
  change 2 * (contract G a b hab ha hb).componentCount + n ≤
    cycleCount (transpose G.edge a b) + cycleCount (transpose G.node (G.face b) (G.face a)) +
      cycleCount G.face + 1
  omega

/-- **Contracting an edge keeps a face on every vertex of every component.** -/
theorem outerFaces_contract (hv : ¬ Reaches G.node a b) (h : OuterFaces G) :
    OuterFaces (contract G a b hab ha hb) := by
  intro d
  obtain ⟨x0, hx0⟩ := h d
  refine ⟨x0, fun d' hd' => ?_⟩
  obtain ⟨y, hy, hny⟩ := hx0 d'
    (linkedPath_of_steps (fun _ _ hs => contract_step_lift G a b hab ha hb hs) hd')
  exact ⟨y, hy, contract_node_reaches G a b hab ha hb hv hny⟩

end Contract

/-! ## Contracting the last edge of an embedding -/

section Last

variable {n : Nat} (G : Hypermap (n + 2)) (ha : G.edge (penultimate n) = last (n + 1))
  (hb : G.edge (last (n + 1)) = penultimate n)

theorem contract_last_fixed :
    (contract G _ _ (penultimate_ne_last n) ha hb).edge (last (n + 1)) = last (n + 1) := by
  change transpose G.edge (penultimate n) (last (n + 1)) (last (n + 1)) = last (n + 1)
  rw [transpose_b _ (penultimate_ne_last n), ha]

theorem contract_shrink_last_fixed :
    (shrinkLast (contract G _ _ (penultimate_ne_last n) ha hb)
      (contract_last_fixed G ha hb)).edge (last n) = last n := by
  apply embed_injective
  rw [shrinkLast_edge_lift]
  change transpose G.edge (penultimate n) (last (n + 1)) (penultimate n) = penultimate n
  rw [transpose_a, hb]

/-- Contract the last edge and excise its two darts. -/
def contractThenShrink : Hypermap n :=
  shrinkLast (shrinkLast (contract G _ _ (penultimate_ne_last n) ha hb)
    (contract_last_fixed G ha hb)) (contract_shrink_last_fixed G ha hb)

theorem contractThenShrink_edge_lift (x : Fin n) :
    embedPair ((contractThenShrink G ha hb).edge x) = G.edge (embedPair x) := by
  unfold contractThenShrink embedPair
  rw [shrinkLast_edge_lift, shrinkLast_edge_lift]
  exact transpose_other G.edge (embedPair_ne_penultimate x) (embedPair_ne_last x)

theorem contractThenShrink_node_orbit (x y : Fin n) :
    Reaches (contractThenShrink G ha hb).node x y ↔
      Reaches (contract G _ _ (penultimate_ne_last n) ha hb).node (embedPair x) (embedPair y) := by
  rw [contractThenShrink, shrinkLast_node_orbit, shrinkLast_node_orbit]
  rfl

theorem contractThenShrink_planar (hv : ¬ Reaches G.node (penultimate n) (last (n + 1)))
    (hP : G.Planar) : (contractThenShrink G ha hb).Planar :=
  shrinkLast_planar _ _ (shrinkLast_planar _ _ (contract_planar G _ _ _ ha hb hv hP))

theorem outerFaces_contractThenShrink (hv : ¬ Reaches G.node (penultimate n) (last (n + 1)))
    (h : OuterFaces G) : OuterFaces (contractThenShrink G ha hb) :=
  outerFaces_shrinkLast _ _ (outerFaces_shrinkLast _ _ (outerFaces_contract G _ _ _ ha hb hv h))

end Last

/-- Renaming the vertex `v` to `u`. -/
def renameTo {V : Type} [DecidableEq V] (u v w : V) : V := if w = v then u else w

/-- Darts whose vertices agree after renaming `v` to `u` are at the same vertex of the
contraction of an edge from `u` to `v`. -/
theorem contract_node_of_label {V : Type} [DecidableEq V] {n : Nat} (G : Hypermap n)
    (a b : Fin n) (hab : a ≠ b) (ha : G.edge a = b) (hb : G.edge b = a)
    (φ0 : Fin n → Option V) (hn : ∀ x y, Reaches G.node x y ↔ φ0 x = φ0 y) {u v : V}
    (huv : u ≠ v) (hu : φ0 a = some u) (hv : φ0 b = some v) {x y : Fin n}
    (h : (φ0 x).map (renameTo u v) = (φ0 y).map (renameTo u v)) :
    Reaches (contract G a b hab ha hb).node x y := by
  have hsep : ¬ Reaches G.node a b :=
    fun hr => huv (Option.some.inj (hu.symm.trans (((hn a b).mp hr).trans hv)))
  have hC : ∀ {x y}, Reaches G.node x y → Reaches (contract G a b hab ha hb).node x y :=
    fun h => contract_node_reaches G a b hab ha hb hsep h
  have hinj := contract_node_inj G a b hab ha hb
  have hCab := contract_node_ab G a b hab ha hb hsep
  by_cases hxy : φ0 x = φ0 y
  · exact hC ((hn x y).mpr hxy)
  · cases hx : φ0 x with
    | none =>
      cases hy : φ0 y with
      | none => exact absurd (hx.trans hy.symm) hxy
      | some q => rw [hx, hy] at h; simp at h
    | some p =>
      cases hy : φ0 y with
      | none => rw [hx, hy] at h; simp at h
      | some q =>
        rw [hx, hy] at h
        simp only [Option.map_some, Option.some.injEq] at h
        have hpq : p ≠ q := fun he => hxy (by rw [hx, hy, he])
        unfold renameTo at h
        by_cases hpv : p = v
        · subst hpv
          have hqv : q ≠ p := fun he => hpq he.symm
          simp only [ite_true, hqv, ite_false] at h
          subst h
          have hxb : Reaches G.node x b := (hn x b).mpr (hx.trans hv.symm)
          have hya : Reaches G.node y a := (hn y a).mpr (hy.trans hu.symm)
          exact (hC hxb).trans ((hCab.symm hinj).trans ((hC hya).symm hinj))
        · by_cases hqv : q = v
          · subst hqv
            simp only [hpv, ite_false, ite_true] at h
            subst h
            have hxa : Reaches G.node x a := (hn x a).mpr (hx.trans hu.symm)
            have hyb : Reaches G.node y b := (hn y b).mpr (hy.trans hv.symm)
            exact (hC hxa).trans (hCab.trans ((hC hyb).symm hinj))
          · simp only [hpv, hqv, ite_false] at h
            exact absurd h hpq

theorem halfEdgeEnd_last_pair {V : Type} (es : List (V × V)) (u v : V) :
    halfEdgeEnd (es ++ [(u, v)]) (2 * es.length) = some u ∧
      halfEdgeEnd (es ++ [(u, v)]) (2 * es.length + 1) = some v :=
  halfEdgeEnd_of_getElem? _ _ _ _ (by simp)

end STACS2027.OuterplanarMinor

namespace STACS2027
open Complexity Complexity.Planar STACS2027.PlanarGluing STACS2027.PlanarPreprocess
open STACS2027.PlanarPreprocess.Deletion STACS2027.OuterplanarMinor

/-- **Contracting the last edge `(u, v)`, `u ≠ v`, of an outerplanar embedding** gives an
outerplanar embedding of the other edges with `v` renamed `u`. -/
theorem OuterplanarEmbedding.contractLast {V : Type} [DecidableEq V] {es : List (V × V)}
    {u v : V} (huv : u ≠ v) (h : OuterplanarEmbedding (es ++ [(u, v)])) :
    OuterplanarEmbedding (es.map fun e => (renameTo u v e.1, renameTo u v e.2)) := by
  obtain ⟨hu, hv⟩ := halfEdgeEnd_last_pair es u v
  unfold OuterplanarEmbedding at h ⊢
  rw [List.length_append] at h
  simp only [List.length_cons, List.length_nil] at h
  obtain ⟨G, he, hn, hp, ho⟩ := h
  change (∀ d, (G.edge d).val = ed d.val) at he
  rw [List.length_map]
  have hpair := graphEdge_last_pair G he
  -- the two ends of the last edge are different vertices
  have hsep : ¬ Reaches G.node (penultimate (2 * es.length)) (last (2 * es.length + 1)) := by
    intro hr
    have h' := (hn _ _).mp hr
    change halfEdgeEnd (es ++ [(u, v)]) (2 * es.length) =
      halfEdgeEnd (es ++ [(u, v)]) (2 * es.length + 1) at h'
    rw [hu, hv] at h'
    exact huv (Option.some.inj h')
  let φ : Fin (2 * es.length + 2) → Option V := fun z =>
    (halfEdgeEnd (es ++ [(u, v)]) z.val).map (renameTo u v)
  have hφ : ∀ z, φ (G.node z) = φ z := by
    intro z
    have := (hn z (G.node z)).mp ⟨1, rfl⟩
    simp only [φ]
    rw [← this]
  have hφab : φ (penultimate (2 * es.length)) = φ (last (2 * es.length + 1)) := by
    change (halfEdgeEnd (es ++ [(u, v)]) (2 * es.length)).map (renameTo u v) =
      (halfEdgeEnd (es ++ [(u, v)]) (2 * es.length + 1)).map (renameTo u v)
    rw [hu, hv]
    simp [renameTo]
  refine ⟨contractThenShrink G hpair.1 hpair.2, ?_, ?_,
    contractThenShrink_planar G _ _ hsep hp, ?_⟩
  · intro d
    have h := congrArg Fin.val (contractThenShrink_edge_lift G hpair.1 hpair.2 d)
    rw [he] at h
    exact h
  · intro d d'
    change Reaches _ d d' ↔ _
    rw [contractThenShrink_node_orbit, halfEdgeEnd_relabel, halfEdgeEnd_relabel]
    have hd : halfEdgeEnd es d.val = halfEdgeEnd (es ++ [(u, v)]) (embedPair d).val :=
      (halfEdgeEnd_append_left es [(u, v)] d.val d.isLt).symm
    have hd' : halfEdgeEnd es d'.val = halfEdgeEnd (es ++ [(u, v)]) (embedPair d').val :=
      (halfEdgeEnd_append_left es [(u, v)] d'.val d'.isLt).symm
    rw [hd, hd']
    change _ ↔ φ (embedPair d) = φ (embedPair d')
    constructor
    · rintro ⟨k, hk⟩
      rw [← hk]
      exact (iterate_invariant _ φ
        (contract_node_invariant G _ _ (penultimate_ne_last _) hpair.1 hpair.2 φ hφ hφab) k
        (embedPair d)).symm
    · intro heq
      exact contract_node_of_label G _ _ _ hpair.1 hpair.2
        (fun z => halfEdgeEnd (es ++ [(u, v)]) z.val) hn huv hu hv heq
  · exact (outerFaces_iff _).mp
      (outerFaces_contractThenShrink G _ _ hsep ((outerFaces_iff G).mpr ho))

end STACS2027
