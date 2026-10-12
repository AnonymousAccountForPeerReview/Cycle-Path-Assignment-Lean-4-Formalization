module

public import Outerplanar.Algo.Graph
import Mathlib.Tactic

/-!
# Optimal assignment outputs: combination over blocks and relabelling

* `isMinCost_family_iff`: for a complete family `cs` of pairwise different `k`-cycles of
  `g`, the paths `selected c 0` are optimal iff no choice of omitted vertices is cheaper.
* `optimalAssignmentOutput_blocks`: the outputs of the blocks of a palm tree concatenate
  to an output of the graph (blocks are edge-disjoint, every cycle lies in one of them,
  paths in different blocks share no edge, so costs add).
* `optimalAssignmentOutput_relabel`: outputs transfer along a renaming injective on the
  vertices.
* `optimalAssignmentOutput_labels`: an output of the id graph `idEdges g`, with ids replaced
  by labels, is an output of `g`; minors of `idEdges g` are minors of `g`
  (`hasMinor_of_idEdges`, `k23MinorFree_idEdges`, `outerplanar_idEdges`).
-/

@[expose] public section

namespace STACS2027.Algo

/-! ### Families of cycles and the paths `selected c 0` -/

namespace Comb

theorem headD_mem {g : Graph} {k : ℕ} {c : Cycle} (hc : IsCycle g k c) : c.headD 0 ∈ c := by
  have h1 := hc.1
  have h2 := hc.2.1
  cases c with
  | nil => simp at h2; omega
  | cons x xs => simp

theorem selected_zero_perm {g : Graph} {k : ℕ} {c : Cycle} (hc : IsCycle g k c) :
    (selected c 0).Perm (selectedAt c (c.headD 0)) := by
  have hl : 0 < c.length := by have := hc.1; have := hc.2.1; omega
  have h := selected_perm_selectedAt hc hl
  cases c with
  | nil => simp at hl
  | cons x xs => simpa using h

theorem selected_zero_sub {g : Graph} {k : ℕ} {c : Cycle} (hc : IsCycle g k c) :
    ∀ e ∈ selected c 0, e ∈ cycleEdges c :=
  fun _ he => (selectedAt_mem.mp ((selected_zero_perm hc).subset he)).1

theorem cost_selected_zero {g : Graph} {k : ℕ} {cs : List Cycle} (hc : ∀ c ∈ cs, IsCycle g k c) :
    cost (cs.map fun c => selected c 0) = cost (cs.map fun c => selectedAt c (c.headD 0)) :=
  cost_map_eq cs _ _ (List.pairwise_of_forall_mem_list fun c hcm d hdm =>
    overlap_perm (selected_zero_perm (hc c hcm)) (selected_zero_perm (hc d hdm)))

/-- For a complete family of pairwise different `k`-cycles, the paths `selected c 0` are
optimal iff no choice of omitted vertices is cheaper. -/
theorem isMinCost_family_iff {g : Graph} {k : ℕ} {cs : List Cycle}
    (hc : ∀ c ∈ cs, IsCycle g k c) (hn : cs.Pairwise (fun c d => ¬ SameCycle c d))
    (hcover : ∀ c, IsCycle g k c → ∃ d ∈ cs, SameCycle c d) :
    IsMinCost g k (cost (cs.map fun c => selected c 0)) ↔
      ∀ choose : Cycle → ℕ, (∀ c ∈ cs, choose c ∈ c) →
        cost (cs.map fun c => selected c 0) ≤ cost (cs.map fun c => selectedAt c (choose c)) := by
  unfold IsMinCost
  simp only [hasAssignment_iff_complete_family hc hn hcover]
  constructor
  · rintro ⟨-, h⟩ choose hch
    exact h _ ⟨choose, hch, le_rfl⟩
  · intro h
    refine ⟨⟨fun c => c.headD 0, fun c hcm => headD_mem (hc c hcm), (cost_selected_zero hc).ge⟩,
      ?_⟩
    rintro B ⟨choose, hch, hB⟩
    exact (h choose hch).trans hB

/-- A complete family of pairwise different `k`-cycles whose paths `selected c 0` cost
nothing is an optimal output. -/
theorem optimalAssignmentOutput_of_cost_zero {g : Graph} {k : ℕ} {cs : List Cycle}
    (hc : ∀ c ∈ cs, IsCycle g k c) (hn : cs.Pairwise (fun c d => ¬ SameCycle c d))
    (hcover : ∀ c, IsCycle g k c → ∃ d ∈ cs, SameCycle c d)
    (h0 : cost (cs.map fun c => selected c 0) = 0) :
    OptimalAssignmentOutput g k cs.flatten :=
  ⟨cs, rfl, hc, hn, hcover, (isMinCost_family_iff hc hn hcover).mpr fun _ _ => by
    rw [h0]; exact Nat.zero_le _⟩

/-- Costs of edge-disjoint families add. -/
theorem cost_flatMap_disjoint {ι : Type} (hs : List ι) (F : ι → List (List Edge))
    (hd : hs.Pairwise fun i j => ∀ p ∈ F i, ∀ q ∈ F j, overlap p q = 0) :
    cost (hs.flatMap F) = (hs.map fun i => cost (F i)).sum := by
  induction hs with
  | nil => rfl
  | cons i hs ih =>
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hd
    have hz : crossCost (F i) (hs.flatMap F) = 0 := by
      refine (crossCost_zero_iff _ _).mpr fun p hp q hq => ?_
      obtain ⟨j, hj, hq⟩ := List.mem_flatMap.mp hq
      exact h1 j hj p hp q hq
    rw [List.flatMap_cons, cost_append, ih h2, hz, List.map_cons, List.sum_cons]
    omega

theorem flatMap_flatten_eq {ι : Type} (hs : List ι) (out : ι → List ℕ) (F : ι → List Cycle)
    (h : ∀ i ∈ hs, out i = (F i).flatten) : hs.flatMap out = (hs.flatMap F).flatten := by
  induction hs with
  | nil => rfl
  | cons i hs ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.flatten_append, h i (by simp),
      ih (fun j hj => h j (by simp [hj]))]

end Comb

open Comb

/-! ### Combination over the blocks of a palm tree -/

namespace Comb

variable {G : Graph} (P : Palm G)

theorem overlap_zero_of_blocks {h h' : ℕ} (hne : h ≠ h') {p q : List Edge}
    (hp : ∀ e ∈ p, e ∈ P.block h) (hq : ∀ e ∈ q, e ∈ P.block h') : overlap p q = 0 :=
  overlap_eq_zero_of_disjoint fun e he heq =>
    hne (((P.mem_block_iff).mp (hp e he)).2.2.symm.trans ((P.mem_block_iff).mp (hq e heq)).2.2)

/-- Every cycle of `G` lies in the block of a head. -/
theorem cycle_in_head_block {k : ℕ} {c : Cycle} (hc : IsCycle G k c) :
    ∃ h, P.IsHead h ∧ IsCycle (P.block h) k c := by
  obtain ⟨e0, he0⟩ := cycleEdges_nonempty hc
  have hn := pathEdges_normalized _ e0 he0
  have he0' : edge e0.1 e0.2 ∈ cycleEdges c := by rw [hn]; exact he0
  have hall := P.cycle_in_block hc he0'
  have hadj : Adj G e0.1 e0.2 := ⟨hc.edge_endpoints_ne he0, by rw [hn]; exact hc.2.2.2 e0 he0⟩
  obtain ⟨hxv, hxr, -⟩ := P.lower_facts hadj
  exact ⟨_, (P.head_spec hxv hxr).1, hc.1, hc.2.1, hc.2.2.1, hall⟩

/-- Edge-disjoint blocks: the cost of a family of paths, each in the block of its cycle,
is the sum over the blocks. -/
theorem cost_blocks {hs : List ℕ} (hnd : hs.Nodup) (F : ℕ → List Cycle) (f : Cycle → List Edge)
    (hf : ∀ h ∈ hs, ∀ c ∈ F h, ∀ e ∈ f c, e ∈ P.block h) :
    cost ((hs.flatMap F).map f) = (hs.map fun h => cost ((F h).map f)).sum := by
  rw [List.map_flatMap]
  apply cost_flatMap_disjoint
  refine hnd.imp_of_mem fun {h h'} hh hh' hne p hp q hq => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
  exact overlap_zero_of_blocks P hne (hf h hh c hc) (hf h' hh' d hd)

end Comb

/-- **Combination over blocks**: optimal outputs of the blocks of a palm tree of `G`, for a
duplicate-free list `hs` of indices containing every head, concatenate to an optimal
output of `G`. -/
theorem optimalAssignmentOutput_blocks {G : Graph} (P : Palm G) {k : ℕ}
    {hs : List ℕ} (hnd : hs.Nodup) (hheads : ∀ h, P.IsHead h → h ∈ hs) {out : ℕ → List ℕ}
    (hout : ∀ h ∈ hs, OptimalAssignmentOutput (P.block h) k (out h)) :
    OptimalAssignmentOutput G k (hs.flatMap out) := by
  classical
  have hex : ∀ h, ∃ cs : List Cycle, h ∈ hs → (out h = cs.flatten ∧
      (∀ c ∈ cs, IsCycle (P.block h) k c) ∧ cs.Pairwise (fun c d => ¬ SameCycle c d) ∧
      (∀ c, IsCycle (P.block h) k c → ∃ d ∈ cs, SameCycle c d) ∧
      IsMinCost (P.block h) k (cost (cs.map fun c => selected c 0))) := by
    intro h
    by_cases hh : h ∈ hs
    · obtain ⟨cs, hcs⟩ := hout h hh
      exact ⟨cs, fun _ => hcs⟩
    · exact ⟨[], fun h' => absurd h' hh⟩
  choose F hF using hex
  have hmem : ∀ {c}, c ∈ hs.flatMap F → ∃ h ∈ hs, c ∈ F h := List.mem_flatMap.mp
  have hcyc : ∀ h ∈ hs, ∀ c ∈ F h, ∀ e ∈ cycleEdges c, e ∈ P.block h :=
    fun h hh c hc => ((hF h hh).2.1 c hc).2.2.2
  have hc : ∀ c ∈ hs.flatMap F, IsCycle G k c := by
    intro c hcm
    obtain ⟨h, hh, hc⟩ := hmem hcm
    exact ((hF h hh).2.1 c hc).graph_mono fun _ he => P.block_sub h _ he
  have hn : (hs.flatMap F).Pairwise (fun c d => ¬ SameCycle c d) := by
    refine List.pairwise_flatMap.mpr ⟨fun h hh => (hF h hh).2.2.1, ?_⟩
    refine hnd.imp_of_mem fun {h h'} hh hh' hne c hcm d hdm hs => ?_
    obtain ⟨e, he⟩ := cycleEdges_nonempty ((hF h hh).2.1 c hcm)
    exact hne (((P.mem_block_iff).mp (hcyc h hh c hcm e he)).2.2.symm.trans
      ((P.mem_block_iff).mp (hcyc h' hh' d hdm e (hs.1 e he))).2.2)
  have hcover : ∀ c, IsCycle G k c → ∃ d ∈ hs.flatMap F, SameCycle c d := by
    intro c hcG
    obtain ⟨h, hh, hcb⟩ := cycle_in_head_block P hcG
    obtain ⟨d, hd, hs⟩ := (hF h (hheads h hh)).2.2.2.1 c hcb
    exact ⟨d, List.mem_flatMap.mpr ⟨h, hheads h hh, hd⟩, hs⟩
  refine ⟨hs.flatMap F, flatMap_flatten_eq hs out F fun h hh => (hF h hh).1, hc, hn, hcover, ?_⟩
  refine (isMinCost_family_iff hc hn hcover).mpr fun choose hch => ?_
  rw [cost_blocks P hnd F _ fun h hh c hcm e he => hcyc h hh c hcm e
      (selected_zero_sub ((hF h hh).2.1 c hcm) e he),
    cost_blocks P hnd F _ fun h hh c hcm e he => hcyc h hh c hcm e (selectedAt_mem.mp he).1]
  refine sum_map_le hs _ _ fun h hh => ?_
  have hb := hF h hh
  exact (isMinCost_family_iff hb.2.1 hb.2.2.1 hb.2.2.2.1).mp hb.2.2.2.2 choose
    fun c hcm => hch c (List.mem_flatMap.mpr ⟨h, hh, hcm⟩)

/-! ### Relabelling -/

namespace Comb

theorem selected_map (t : ℕ → ℕ) (c : Cycle) (i : ℕ) :
    selected (c.map t) i = (selected c i).map (mapEdge t) := by
  unfold selected
  rw [← pathEdges_map]
  simp [List.map_take, List.map_drop]

/-- Cycles depend only on the simple graph. -/
theorem isCycle_of_edge_iff {g h : Graph} (he : ∀ a b, a ≠ b → (edge a b ∈ g ↔ edge a b ∈ h))
    {k : ℕ} {c : Cycle} (hc : IsCycle g k c) : IsCycle h k c := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, fun e hce => ?_⟩
  have hn := pathEdges_normalized _ e hce
  rw [← hn]
  exact (he _ _ (hc.edge_endpoints_ne hce)).mp (by rw [hn]; exact hc.2.2.2 e hce)

end Comb

/-- **Relabelling**: an optimal output of `G'` (vertices below `n`, edges written smaller
end first), renamed by `t` injective on `[0, n)`, is an optimal output of every graph `G`
with the simple graph of `mapGraph t G'`. -/
theorem optimalAssignmentOutput_relabel {G G' : Graph} {n k : ℕ} (hb : VerticesBelow G' n)
    (hn : ∀ e ∈ G', edge e.1 e.2 = e) (t : ℕ → ℕ)
    (hi : ∀ a, a < n → ∀ b, b < n → t a = t b → a = b)
    (he : ∀ a b, a ≠ b → (edge a b ∈ G ↔ edge a b ∈ mapGraph t G')) {out : List ℕ}
    (h : OptimalAssignmentOutput G' k out) : OptimalAssignmentOutput G k (out.map t) := by
  obtain ⟨cs, rfl, hc, hd, hcover, hmin⟩ := h
  refine ⟨cs.map (List.map t), List.map_flatten, ?_, mapped_family_distinct hb hn hc hd t hi, ?_,
    ?_⟩
  · intro c' hc'
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hc'
    have hcc := hc c hcm
    exact isCycle_of_edge_iff (fun a b hab => (he a b hab).symm) (hcc.map t fun a ha b hb' hab =>
      hi a (hcc.vertex_bound hb a ha) b (hcc.vertex_bound hb b hb') hab)
  · intro c hcG
    obtain ⟨d, hd, rfl⟩ := IsCycle.unmap hb hn t hi (isCycle_of_edge_iff he hcG)
    obtain ⟨d', hd', hs⟩ := hcover d hd
    exact ⟨d'.map t, List.mem_map_of_mem hd', hs.map t⟩
  · have hcost : cost ((cs.map (List.map t)).map fun c => selected c 0) =
        cost (cs.map fun c => selected c 0) := by
      have hm : (cs.map (List.map t)).map (fun c => selected c 0) =
          (cs.map fun c => selected c 0).map (List.map (mapEdge t)) := by
        simp only [List.map_map]
        exact List.map_congr_left fun c _ => selected_map t c 0
      rw [hm, cost_relabel hb hn t hi]
      intro p hp
      obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hp
      exact fun e he => (hc c hcm).2.2.2 e (selected_zero_sub (hc c hcm) e he)
    rw [hcost, isMinCost_proper he]
    simpa only [IsMinCost, hasAssignment_relabel hb hn t hi] using hmin

/-! ### Back to labels -/

namespace Comb

theorem eraseDups_nodup' : ∀ (n : ℕ) (l : List ℕ), l.length ≤ n → l.eraseDups.Nodup
  | _, [], _ => by simp
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons]
    have hlen : (as.filter fun b => !b == a).length ≤ n :=
      Nat.le_trans (List.length_filter_le _ _) (by simp at h; omega)
    refine List.nodup_cons.mpr ⟨fun ha => ?_, eraseDups_nodup' n _ hlen⟩
    have := List.mem_filter.mp (List.mem_eraseDups.mp ha)
    simp at this

theorem labels_nodup (g : Graph) : (labels g).Nodup :=
  eraseDups_nodup' _ _ le_rfl

theorem mem_proper {g : Graph} {e : Edge} : e ∈ proper g ↔ e ∈ g ∧ e.1 < e.2 := by
  simp [proper]

theorem mem_labels_of_proper {g : Graph} {e : Edge} (he : e ∈ proper g) :
    e.1 ∈ labels g ∧ e.2 ∈ labels g := by
  simp only [labels, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨⟨e, he, by simp⟩, ⟨e, he, by simp⟩⟩

theorem labelOf_idOf {g : Graph} {x : ℕ} (hx : x ∈ labels g) : labelOf g (idOf g x) = x := by
  have hlt : (labels g).idxOf x < (labels g).length := List.idxOf_lt_length_iff.mpr hx
  simp only [labelOf, idOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
    Option.getD_some]
  exact List.getElem_idxOf hlt

theorem idOf_lt {g : Graph} {x : ℕ} (hx : x ∈ labels g) : idOf g x < numV g :=
  List.idxOf_lt_length_iff.mpr hx

theorem labelOf_mem {g : Graph} {v : ℕ} (hv : v < numV g) : labelOf g v ∈ labels g := by
  simp only [labelOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv, Option.getD_some]
  exact List.getElem_mem hv

theorem labelOf_inj {g : Graph} : ∀ a, a < numV g → ∀ b, b < numV g →
    labelOf g a = labelOf g b → a = b := by
  intro a ha b hb heq
  simp only [labelOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha,
    List.getElem?_eq_getElem hb, Option.getD_some] at heq
  exact (List.Nodup.getElem_inj_iff (labels_nodup g)).mp heq

theorem mem_idEdges {g : Graph} {e : Edge} :
    e ∈ idEdges g ↔ ∃ d ∈ proper g, e = edge (idOf g d.1) (idOf g d.2) := by
  simp only [idEdges, List.mem_eraseDups, List.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩; exact ⟨d, hd, rfl⟩
  · rintro ⟨d, hd, rfl⟩; exact ⟨d, hd, rfl⟩

theorem edge_edge (a b : ℕ) : edge (edge a b).1 (edge a b).2 = edge a b := by
  simp only [edge]
  rw [min_eq_left (min_le_max), max_eq_right (min_le_max)]

theorem idEdges_below (g : Graph) : VerticesBelow (idEdges g) (numV g) := by
  intro e he
  obtain ⟨d, hd, rfl⟩ := mem_idEdges.mp he
  have hl := mem_labels_of_proper hd
  exact (edge_below _ _ _).mpr ⟨idOf_lt hl.1, idOf_lt hl.2⟩

theorem idEdges_normalized (g : Graph) : ∀ e ∈ idEdges g, edge e.1 e.2 = e := by
  intro e he
  obtain ⟨d, -, rfl⟩ := mem_idEdges.mp he
  exact edge_edge _ _

theorem mapEdge_labelOf {g : Graph} {d : Edge} (hd : d ∈ proper g) :
    mapEdge (labelOf g) (edge (idOf g d.1) (idOf g d.2)) = d := by
  have hl := mem_labels_of_proper hd
  have hlt := (mem_proper.mp hd).2
  rw [mapEdge_edge, labelOf_idOf hl.1, labelOf_idOf hl.2]
  simp [edge, Nat.min_eq_left hlt.le, Nat.max_eq_right hlt.le]

/-- The id graph renamed by `labelOf` has the simple graph of `g`. -/
theorem edge_iff_idEdges (g : Graph) :
    ∀ a b, a ≠ b → (edge a b ∈ g ↔ edge a b ∈ mapGraph (labelOf g) (idEdges g)) := by
  intro a b hab
  constructor
  · intro he
    have hp : edge a b ∈ proper g := mem_proper.mpr ⟨he, by simp only [edge]; omega⟩
    exact List.mem_map.mpr ⟨_, mem_idEdges.mpr ⟨_, hp, rfl⟩, mapEdge_labelOf hp⟩
  · intro he
    obtain ⟨d', hd', heq⟩ := List.mem_map.mp he
    obtain ⟨d, hd, rfl⟩ := mem_idEdges.mp hd'
    rw [← heq, mapEdge_labelOf hd]
    exact (mem_proper.mp hd).1

end Comb

/-- **Back to labels**: an optimal output of the id graph, with ids replaced by labels, is
an optimal output of `g`. -/
theorem optimalAssignmentOutput_labels {g : Graph} {k : ℕ} {out : List ℕ}
    (h : OptimalAssignmentOutput (idEdges g) k out) :
    OptimalAssignmentOutput g k (out.map (labelOf g)) :=
  optimalAssignmentOutput_relabel (idEdges_below g) (idEdges_normalized g) (labelOf g) labelOf_inj
    (edge_iff_idEdges g) h

/-- The output of `solveWith` is the concatenation of the outputs of the blocks, with ids
replaced by labels. -/
theorem solveWith_eq_map (solveBlock : List Edge → List (List ℕ)) (g : Graph) :
    solveWith solveBlock g = (((blocksOf g).flatMap solveBlock).flatten).map (labelOf g) := by
  rw [solveWith, List.map_flatten, List.flatMap_def]

/-! ### Minors of the id graph -/

namespace Comb

theorem walkWithin_map {g h : Graph} {S T : ℕ → Prop} (t : ℕ → ℕ)
    (hadj : ∀ u v, Adj g u v → Adj h (t u) (t v)) (hST : ∀ x, S x → T (t x)) :
    ∀ {w : List ℕ}, WalkWithin g S w → WalkWithin h T (w.map t)
  | [], _ => trivial
  | [a], hw => hST a hw
  | a :: b :: _, ⟨ha, hab, hw⟩ => ⟨hST a ha, hadj a b hab, walkWithin_map t hadj hST hw⟩

/-- Minors are preserved by an injective renaming preserving adjacency. -/
theorem HasMinor.map {g h : Graph} {s : ℕ} {H : Graph} (t : ℕ → ℕ) (ht : Function.Injective t)
    (hadj : ∀ u v, Adj g u v → Adj h (t u) (t v)) (hm : HasMinor g s H) : HasMinor h s H := by
  obtain ⟨branch, h1, h2, h3, h4⟩ := hm
  refine ⟨fun i => (branch i).map t, fun i hi => by simpa using h1 i hi, ?_, ?_, ?_⟩
  · intro i j hi hj hij v hv hv'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    obtain ⟨u', hu', heq⟩ := List.mem_map.mp hv'
    exact h2 i j hi hj hij u hu (ht heq ▸ hu')
  · intro i hi x y hx hy
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
    obtain ⟨w, hw1, hw2, hw⟩ := h3 i hi u v hu hv
    refine ⟨w.map t, by simp [List.head?_map, hw1], by simp [List.getLast?_map, hw2], ?_⟩
    exact walkWithin_map t hadj (fun x hx => List.mem_map_of_mem hx) hw
  · intro e he
    obtain ⟨u, v, hu, hv, huv⟩ := h4 e he
    exact ⟨t u, t v, List.mem_map_of_mem hu, List.mem_map_of_mem hv, hadj u v huv⟩

/-- `labelOf g`, extended injectively beyond the ids. -/
def labelExt (g : Graph) (v : ℕ) : ℕ :=
  if v < numV g then labelOf g v else (labels g).sum + 1 + v

theorem labelExt_injective (g : Graph) : Function.Injective (labelExt g) := by
  intro a b heq
  unfold labelExt at heq
  by_cases ha : a < numV g <;> by_cases hb : b < numV g <;>
    simp only [ha, hb, ↓reduceIte] at heq
  · exact labelOf_inj a ha b hb heq
  · have := List.le_sum_of_mem (labelOf_mem ha); omega
  · have := List.le_sum_of_mem (labelOf_mem hb); omega
  · omega

theorem adj_labelExt {g : Graph} {u v : ℕ} (h : Adj (idEdges g) u v) :
    Adj g (labelExt g u) (labelExt g v) := by
  obtain ⟨huv, he⟩ := h
  obtain ⟨hu, hv⟩ := (edge_below u v _).mp (idEdges_below g _ he)
  simp only [labelExt, hu, hv, ↓reduceIte]
  have hne : labelOf g u ≠ labelOf g v := fun heq => huv (labelOf_inj u hu v hv heq)
  refine ⟨hne, (edge_iff_idEdges g _ _ hne).mpr ?_⟩
  rw [← mapEdge_edge]
  exact List.mem_map_of_mem he

end Comb

/-- Minors of the id graph are minors of `g`. -/
theorem hasMinor_of_idEdges {g : Graph} {s : ℕ} {H : Graph} (h : HasMinor (idEdges g) s H) :
    HasMinor g s H :=
  Comb.HasMinor.map (labelExt g) (labelExt_injective g) (fun _ _ => adj_labelExt) h

theorem k23MinorFree_idEdges {g : Graph} (h : K23MinorFree g) : K23MinorFree (idEdges g) :=
  fun hm => h (hasMinor_of_idEdges hm)

theorem not_hasMinor_k4_idEdges {g : Graph} (h : ¬ HasMinor g 4 k4) :
    ¬ HasMinor (idEdges g) 4 k4 :=
  fun hm => h (hasMinor_of_idEdges hm)

theorem outerplanar_idEdges {g : Graph} (h : Outerplanar g) : Outerplanar (idEdges g) :=
  ⟨not_hasMinor_k4_idEdges h.1, k23MinorFree_idEdges h.2⟩

end STACS2027.Algo
