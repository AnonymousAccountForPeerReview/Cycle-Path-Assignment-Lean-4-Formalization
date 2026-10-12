module

public import NPHardness.SubdivisionSequence
public import NPHardness.Gadgets

/-! Certified straight-chain programs for the subdivisions in Figure 4. -/

@[expose] public section
namespace STACS2027

def VerticesBelow (g : Graph) (n : Nat) : Prop := ∀ e ∈ g, e.1 < n ∧ e.2 < n

theorem edge_below (a b n : Nat) :
    (edge a b).1 < n ∧ (edge a b).2 < n ↔ a < n ∧ b < n := by
  simp only [edge]
  omega

theorem VerticesBelow.mono {g : Graph} {m n : Nat} (h : VerticesBelow g m) (hmn : m ≤ n) :
    VerticesBelow g n := fun e he => ⟨Nat.lt_of_lt_of_le (h e he).1 hmn,
      Nat.lt_of_lt_of_le (h e he).2 hmn⟩

theorem VerticesBelow.fresh {g : Graph} {n : Nat} (h : VerticesBelow g n) : FreshVertex g n := by
  intro a b he
  have h' := (edge_below a b n).mp (h _ he)
  exact ⟨by omega, by omega⟩

theorem subdivideOnce_below {g : Graph} {a b n : Nat} (h : VerticesBelow g n)
    (ha : a < n) (hb : b < n) : VerticesBelow (subdivideOnce g a b n) (n + 1) := by
  intro e he
  rcases mem_subdivideOnce.mp he with rfl | rfl | ⟨he, _⟩
  · apply (edge_below ..).mpr; omega
  · apply (edge_below ..).mpr; omega
  · exact ⟨by have := (h e he).1; omega, by have := (h e he).2; omega⟩

def chainSteps (a b next : Nat) : Nat → List SubdivisionStep
  | 0 => []
  | s + 1 => ⟨a, b, next⟩ :: chainSteps next b (next + 1) s

theorem chainSteps_below {g : Graph} (a b next s : Nat) (hg : VerticesBelow g next)
    (ha : a < next) (hb : b < next) :
    VerticesBelow (subdivisionGraph g (chainSteps a b next s)) (next + s) := by
  induction s generalizing g a next with
  | zero => simpa [chainSteps, subdivisionGraph] using hg
  | succ s ih =>
    have h := ih next (next + 1) (subdivideOnce_below hg ha hb)
      (by omega) (by omega)
    simpa only [chainSteps, subdivisionGraph, Nat.add_assoc, Nat.add_comm 1 s] using h

theorem chainSteps_valid {g : Graph} (a b next s : Nat) (hg : VerticesBelow g next)
    (hab : a ≠ b) (he : edge a b ∈ g) : validSubdivision g (chainSteps a b next s) := by
  induction s generalizing g a next with
  | zero => trivial
  | succ s ih =>
    have hv := (edge_below a b next).mp (hg _ he)
    refine ⟨hab, he, hg.fresh, ?_⟩
    exact ih next (next + 1) (subdivideOnce_below hg hv.1 hv.2) (by omega)
      (mem_subdivideOnce.mpr (Or.inr (Or.inl rfl)))

theorem chainSteps_unchanged (a b next s : Nat) (e : Edge)
    (he : e.1 < next ∧ e.2 < next) (hne : e ≠ edge a b) :
    expandedEdge (chainSteps a b next s) e = [e] := by
  induction s generalizing a next with
  | zero => rfl
  | succ s ih =>
    have hne' : e ≠ edge next b := by
      intro h; rw [h] at he
      have hbad := (edge_below next b next).mp he
      omega
    simp only [chainSteps, expandedEdge, splitEdge, hne, ↓reduceIte,
      List.flatMap_singleton]
    exact ih next (next + 1) ⟨by omega, by omega⟩ hne'

theorem chainSteps_expands (a b next s : Nat) (hab : a ≠ b)
    (ha : a < next) (hb : b < next) :
    expandedEdge (chainSteps a b next s) (edge a b) = subdividedEdge a b next s := by
  induction s generalizing a next with
  | zero => rfl
  | succ s ih =>
    have hfirst : edge a next ≠ edge next b := by
      intro h
      rw [edge_comm a next, edge_left_inj] at h
      exact hab h
    have hv : (edge a next).1 < next + 1 ∧ (edge a next).2 < next + 1 :=
      (edge_below ..).mpr ⟨by omega, by omega⟩
    simp only [chainSteps, expandedEdge, splitEdge, ↓reduceIte, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    rw [chainSteps_unchanged next b (next + 1) s _ hv hfirst,
      ih next (next + 1) (by omega) (by omega) (by omega)]
    rfl

theorem subdivisionGraph_append (g : Graph) (ss ts : List SubdivisionStep) :
    subdivisionGraph g (ss ++ ts) = subdivisionGraph (subdivisionGraph g ss) ts := by
  induction ss generalizing g with
  | nil => rfl
  | cons s ss ih => exact ih _

theorem validSubdivision_append (g : Graph) (ss ts : List SubdivisionStep) :
    validSubdivision g (ss ++ ts) ↔
      validSubdivision g ss ∧ validSubdivision (subdivisionGraph g ss) ts := by
  induction ss generalizing g with
  | nil => simp [validSubdivision, subdivisionGraph]
  | cons s ss ih =>
    simp only [List.cons_append, validSubdivision, subdivisionGraph, ih, and_assoc]

theorem expandedEdge_append (ss ts : List SubdivisionStep) (e : Edge) :
    expandedEdge (ss ++ ts) e = (expandedEdge ss e).flatMap (expandedEdge ts) := by
  induction ss generalizing e with
  | nil => simp [expandedEdge]
  | cons s ss ih =>
    simp only [List.cons_append, expandedEdge, List.flatMap_assoc]
    congr 1
    funext x
    exact ih x

theorem subdivisionGraph_membership (g : Graph) (ss : List SubdivisionStep)
    (hv : validSubdivision g ss) (e : Edge) :
    e ∈ subdivisionGraph g ss ↔ e ∈ g.flatMap (expandedEdge ss) := by
  induction ss generalizing g with
  | nil => simp [subdivisionGraph, expandedEdge]
  | cons s ss ih =>
    obtain ⟨_, he, _, ht⟩ := hv
    rw [subdivisionGraph, ih _ ht]
    have hm : ∀ d, d ∈ subdivideOnce g s.source s.target s.fresh ↔
        d ∈ liftEdges s.source s.target s.fresh g := by
      intro d
      rw [mem_subdivideOnce, mem_liftEdges]
      simp [he, or_comm, or_left_comm]
    simp only [List.mem_flatMap, hm, liftEdges, List.mem_flatMap, expandedEdge,
      List.mem_flatMap]
    constructor
    · rintro ⟨d, ⟨b, hb, hd⟩, h⟩
      exact ⟨b, hb, d, hd, h⟩
    · rintro ⟨b, hb, d, hd, h⟩
      exact ⟨d, ⟨b, hb, hd⟩, h⟩

theorem chainSteps_retains {g : Graph} (a b next s : Nat) (hg : VerticesBelow g next)
    (hab : a ≠ b) (habg : edge a b ∈ g) (e : Edge) (he : e ∈ g) (hne : e ≠ edge a b) :
    e ∈ subdivisionGraph g (chainSteps a b next s) := by
  rw [subdivisionGraph_membership g _ (chainSteps_valid a b next s hg hab habg)]
  apply List.mem_flatMap.mpr
  exact ⟨e, he, by rw [chainSteps_unchanged a b next s e (hg e he) hne]; simp⟩

def linkSteps (next : Nat) : List Link → List SubdivisionStep
  | [] => []
  | l :: ls => chainSteps l.source l.target next l.subdivisions ++
      linkSteps (next + l.subdivisions) ls

def linkEdges (ls : List Link) : Graph := ls.map fun l => edge l.source l.target

def subdivisionCount (ls : List Link) : Nat := (ls.map Link.subdivisions).sum

theorem subdividedEdge_below (a b next s : Nat) (ha : a < next) (hb : b < next) :
    VerticesBelow (subdividedEdge a b next s) (next + s) := by
  induction s generalizing a next with
  | zero =>
    intro e he
    have heq : e = edge a b := by simpa [subdividedEdge] using he
    subst e
    exact (edge_below ..).mpr ⟨ha, hb⟩
  | succ s ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · apply (edge_below ..).mpr; omega
    · have h := ih next (next + 1) (by omega) (by omega) e he
      constructor <;> omega

theorem subdividedEdge_avoids (a b next s : Nat) (e : Edge)
    (he : e.1 < next ∧ e.2 < next) (hne : e ≠ edge a b) :
    e ∉ subdividedEdge a b next s := by
  induction s generalizing a next with
  | zero => simpa [subdividedEdge] using hne
  | succ s ih =>
    intro h
    rcases List.mem_cons.mp h with h | h
    · have hbad := (edge_below a next next).mp (h ▸ he)
      omega
    · apply ih next (next + 1) ⟨by omega, by omega⟩ ?_ h
      intro heq
      have hbad := (edge_below next b next).mp (heq ▸ he)
      omega

theorem linkSteps_unchanged (next : Nat) (ls : List Link) (e : Edge)
    (he : e.1 < next ∧ e.2 < next) (hne : e ∉ linkEdges ls) :
    expandedEdge (linkSteps next ls) e = [e] := by
  induction ls generalizing next with
  | nil => rfl
  | cons l ls ih =>
    have hh : e ≠ edge l.source l.target := by intro h; apply hne; simp [linkEdges, h]
    have ht : e ∉ linkEdges ls := fun h => hne (List.mem_cons_of_mem _ h)
    rw [linkSteps, expandedEdge_append, chainSteps_unchanged _ _ _ _ e he hh,
      List.flatMap_singleton]
    exact ih (next + l.subdivisions) ⟨by omega, by omega⟩ ht

theorem linkSteps_head (next : Nat) (l : Link) (ls : List Link)
    (hb : VerticesBelow (linkEdges (l :: ls)) next)
    (hn : (linkEdges (l :: ls)).Nodup) (hne : l.source ≠ l.target) :
    expandedEdge (linkSteps next (l :: ls)) (edge l.source l.target) =
      subdividedEdge l.source l.target next l.subdivisions := by
  have hv := (edge_below l.source l.target next).mp (hb _ (by simp [linkEdges]))
  have hno := (List.nodup_cons.mp hn).1
  rw [linkSteps, expandedEdge_append, chainSteps_expands _ _ _ _ hne hv.1 hv.2]
  have hflat : (subdividedEdge l.source l.target next l.subdivisions).flatMap
      (expandedEdge (linkSteps (next + l.subdivisions) ls)) =
      (subdividedEdge l.source l.target next l.subdivisions).flatMap (fun e => [e]) := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro e he
    apply linkSteps_unchanged
    · exact subdividedEdge_below _ _ _ _ hv.1 hv.2 e he
    · intro hm
      have heb := hb e (List.mem_cons_of_mem _ hm)
      have hne' : e ≠ edge l.source l.target := by intro h; subst e; exact hno hm
      exact subdividedEdge_avoids _ _ _ _ e heb hne' he
  simpa using hflat

theorem linkSteps_tail (next : Nat) (l : Link) (ls : List Link) (e : Edge)
    (he : e.1 < next ∧ e.2 < next) (hne : e ≠ edge l.source l.target) :
    expandedEdge (linkSteps next (l :: ls)) e =
      expandedEdge (linkSteps (next + l.subdivisions) ls) e := by
  rw [linkSteps, expandedEdge_append, chainSteps_unchanged _ _ _ _ e he hne,
    List.flatMap_singleton]

theorem linkSteps_edge_length (next : Nat) (ls : List Link)
    (hb : VerticesBelow (linkEdges ls) next) (hn : (linkEdges ls).Nodup)
    (hp : ∀ l ∈ ls, l.source ≠ l.target) (l : Link) (hl : l ∈ ls) :
    (expandedEdge (linkSteps next ls) (edge l.source l.target)).length = l.subdivisions + 1 := by
  induction ls generalizing next with
  | nil => simp at hl
  | cons r rs ih =>
    rcases List.mem_cons.mp hl with rfl | hl
    · rw [linkSteps_head next l rs hb hn (hp l (by simp)), subdividedEdge_length]
    · have hmem : edge l.source l.target ∈ linkEdges rs := List.mem_map.mpr ⟨l, hl, rfl⟩
      have he := hb _ (List.mem_cons_of_mem _ hmem)
      have hne : edge l.source l.target ≠ edge r.source r.target := by
        intro h
        apply (List.nodup_cons.mp hn).1
        change edge r.source r.target ∈ linkEdges rs
        rw [← h]
        exact hmem
      rw [linkSteps_tail next r rs _ he hne]
      apply ih (next + r.subdivisions) ?_ (List.nodup_cons.mp hn).2
        (fun l hl => hp l (by simp [hl])) hl
      intro e he
      have h := hb e (List.mem_cons_of_mem _ he)
      constructor <;> omega

theorem realizeLinks_eq_expanded (next : Nat) (ls : List Link)
    (hb : VerticesBelow (linkEdges ls) next) (hn : (linkEdges ls).Nodup)
    (hp : ∀ l ∈ ls, l.source ≠ l.target) :
    (linkEdges ls).flatMap (expandedEdge (linkSteps next ls)) = realizeLinks next ls := by
  induction ls generalizing next with
  | nil => rfl
  | cons l ls ih =>
    change expandedEdge (linkSteps next (l :: ls)) (edge l.source l.target) ++
      (linkEdges ls).flatMap (expandedEdge (linkSteps next (l :: ls))) = _
    rw [linkSteps_head next l ls hb hn (hp l (by simp))]
    have htail : (linkEdges ls).flatMap (expandedEdge (linkSteps next (l :: ls))) =
        (linkEdges ls).flatMap (expandedEdge (linkSteps (next + l.subdivisions) ls)) := by
      apply congrArg List.flatten
      apply List.map_congr_left
      intro e he
      apply linkSteps_tail
      · exact hb e (List.mem_cons_of_mem _ he)
      · intro h
        apply (List.nodup_cons.mp hn).1
        change edge l.source l.target ∈ linkEdges ls
        rw [← h]
        exact he
    rw [htail, ih (next + l.subdivisions) ?_ (List.nodup_cons.mp hn).2
      (fun r hr => hp r (by simp [hr]))]
    · rfl
    · intro e he
      have h := hb e (List.mem_cons_of_mem _ he)
      constructor <;> omega

theorem linkSteps_valid {g : Graph} (next : Nat) (ls : List Link)
    (hg : VerticesBelow g next) (hn : (linkEdges ls).Nodup)
    (hl : ∀ l ∈ ls, l.source ≠ l.target ∧ edge l.source l.target ∈ g) :
    validSubdivision g (linkSteps next ls) := by
  induction ls generalizing g next with
  | nil => trivial
  | cons l ls ih =>
    obtain ⟨he, ht⟩ := List.nodup_cons.mp hn
    obtain ⟨hne, hmem⟩ := hl l (by simp)
    have hb := (edge_below l.source l.target next).mp (hg _ hmem)
    rw [linkSteps, validSubdivision_append]
    refine ⟨chainSteps_valid _ _ _ _ hg hne hmem, ?_⟩
    apply ih _ (chainSteps_below _ _ _ _ hg hb.1 hb.2) ht
    intro r hr
    obtain ⟨hrne, hrmem⟩ := hl r (by simp [hr])
    refine ⟨hrne, chainSteps_retains _ _ _ _ hg hne hmem _ hrmem ?_⟩
    intro heq
    apply he
    exact List.mem_map.mpr ⟨r, hr, heq⟩

theorem linkSteps_from_base_valid (next : Nat) (ls : List Link)
    (hb : VerticesBelow (linkEdges ls) next) (hn : (linkEdges ls).Nodup)
    (hp : ∀ l ∈ ls, l.source ≠ l.target) : validSubdivision (linkEdges ls) (linkSteps next ls) :=
  linkSteps_valid next ls hb hn (fun l hl => ⟨hp l hl, List.mem_map.mpr ⟨l, hl, rfl⟩⟩)

/-- The certified subdivision program realizes exactly the constructor used
by the gadget certificates, including its concrete fresh-vertex numbering. -/
theorem realizeLinks_membership (next : Nat) (ls : List Link)
    (hb : VerticesBelow (linkEdges ls) next) (hn : (linkEdges ls).Nodup)
    (hp : ∀ l ∈ ls, l.source ≠ l.target) (e : Edge) :
    e ∈ subdivisionGraph (linkEdges ls) (linkSteps next ls) ↔ e ∈ realizeLinks next ls := by
  rw [subdivisionGraph_membership _ _ (linkSteps_from_base_valid next ls hb hn hp),
    realizeLinks_eq_expanded next ls hb hn hp]

theorem realizeLinks_cycle_projection (next : Nat) (ls : List Link)
    (hb : VerticesBelow (linkEdges ls) next) (hn : (linkEdges ls).Nodup)
    (hp : ∀ l ∈ ls, l.source ≠ l.target) {k : Nat} {c : Cycle}
    (hc : IsCycle (realizeLinks next ls) k c) :
    ∃ l d, IsCycle (linkEdges ls) l d ∧
      (cycleEdges c).Perm ((cycleEdges d).flatMap (expandedEdge (linkSteps next ls))) := by
  apply subdivision_cycle_projection _ _ (linkSteps_from_base_valid next ls hb hn hp)
  exact ⟨hc.1, hc.2.1, hc.2.2.1,
    fun e he => (realizeLinks_membership next ls hb hn hp e).mpr (hc.2.2.2 e he)⟩

end STACS2027
