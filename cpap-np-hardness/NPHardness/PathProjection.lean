module

public import NPHardness.SimplePaths
public import NPHardness.SubdivisionPrograms

/-! Exact projection of paths whose endpoints are original vertices. -/

@[expose] public section
namespace STACS2027

theorem subdivideOnce_path_projection {g : Graph} {a b z start stop : Nat}
    (he : edge a b ∈ g) (hf : FreshVertex g z) {p : List Nat}
    (hp : IsSimplePath (subdivideOnce g a b z) start stop p)
    (hstart : z ≠ start) (hstop : z ≠ stop) :
    ∃ d, IsSimplePath g start stop d ∧ (pathEdges p).Perm (liftEdges a b z (pathEdges d)) := by
  by_cases hz : z ∈ p
  · exact subdivideOnce_path_contract he hf hp hz hstart hstop
  · refine ⟨p, ⟨hp.1, hp.2.1, hp.2.2.1, pathEdges_old_of_avoids hp.2.2.2 hz⟩, ?_⟩
    have hab : edge a b ∉ pathEdges p := fun h => subdivideOnce_old_edge_absent hf he (hp.2.2.2 _ h)
    rw [liftEdges_of_absent a b z _ hab]

theorem subdivision_path_projection (g : Graph) (ss : List SubdivisionStep)
    (hv : validSubdivision g ss) {start stop : Nat}
    (hs : ∀ s ∈ ss, s.fresh ≠ start ∧ s.fresh ≠ stop) {p : List Nat}
    (hp : IsSimplePath (subdivisionGraph g ss) start stop p) :
    ∃ d, IsSimplePath g start stop d ∧ (pathEdges p).Perm ((pathEdges d).flatMap (expandedEdge ss)) := by
  induction ss generalizing g p with
  | nil => exact ⟨p,hp,by simp [expandedEdge]⟩
  | cons s ss ih =>
    obtain ⟨_,he,hf,ht⟩ := hv
    obtain ⟨d,hd,hperm⟩ := ih _ ht (fun t hm => hs t (by simp [hm])) hp
    obtain ⟨e,hec,heq⟩ := subdivideOnce_path_projection he hf hd (hs s (by simp)).1 (hs s (by simp)).2
    refine ⟨e,hec,?_⟩
    have hx := hperm.trans (heq.flatMap_right (expandedEdge ss))
    simpa only [liftEdges, List.flatMap_assoc, expandedEdge] using hx

theorem chainSteps_fresh_bound (a b next n : Nat) :
    ∀ s ∈ chainSteps a b next n, next ≤ s.fresh := by
  induction n generalizing a next with
  | zero => simp [chainSteps]
  | succ n ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact Nat.le_refl _
    · have h := ih next (next + 1) s hs
      omega

theorem linkSteps_fresh_bound (next : Nat) (ls : List Link) :
    ∀ s ∈ linkSteps next ls, next ≤ s.fresh := by
  induction ls generalizing next with
  | nil => simp [linkSteps]
  | cons l ls ih =>
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact chainSteps_fresh_bound _ _ _ _ s hs
    · have h := ih (next + l.subdivisions) s hs
      omega

theorem realizeLinks_path_projection (next : Nat) (ls : List Link)
    (hb : VerticesBelow (linkEdges ls) next) (hn : (linkEdges ls).Nodup)
    (hl : ∀ l ∈ ls, l.source ≠ l.target) {start stop : Nat}
    (ha : start < next) (hz : stop < next) {p : List Nat}
    (hp : IsSimplePath (realizeLinks next ls) start stop p) :
    ∃ d, IsSimplePath (linkEdges ls) start stop d ∧
      (pathEdges p).Perm ((pathEdges d).flatMap (expandedEdge (linkSteps next ls))) := by
  apply subdivision_path_projection _ _ (linkSteps_from_base_valid next ls hb hn hl)
  · intro s hs
    have h := linkSteps_fresh_bound next ls s hs
    constructor <;> omega
  · exact ⟨hp.1, hp.2.1, hp.2.2.1, fun e he =>
      (realizeLinks_membership next ls hb hn hl e).mpr (hp.2.2.2 e he)⟩

def pathWeight (w : Edge → Nat) (p : List Nat) : Nat := ((pathEdges p).map w).sum

theorem pathWeight_endpoint_bound (g : Graph) (w : Edge → Nat) (height : Nat → Nat)
    (hl : ∀ a b, edge a b ∈ g → height b ≤ height a + w (edge a b))
    {a b : Nat} {p : List Nat} (hp : IsSimplePath g a b p) :
    height b ≤ height a + pathWeight w p := by
  have h : ∀ p : List Nat, ∀ a b, p.head? = some a → p.getLast? = some b →
      (∀ e ∈ pathEdges p, e ∈ g) → height b ≤ height a + pathWeight w p := by
    intro p
    induction p with
    | nil => intro a b hh ht he; simp at hh
    | cons v p ih =>
      intro a b hh ht he
      have hva : v = a := by simpa using hh
      subst a
      cases p with
      | nil =>
        have hvb : v = b := by simpa using ht
        simp [← hvb, pathWeight, pathEdges]
      | cons u us =>
        have heu : edge v u ∈ g := he _ (by simp [pathEdges])
        have htail : ∀ e ∈ pathEdges (u :: us), e ∈ g :=
          fun e hem => he e (by simp [pathEdges, hem])
        have hb := ih u b rfl (by simpa using ht) htail
        have hstep := hl v u heu
        simp only [pathWeight, pathEdges, List.map_cons, List.sum_cons] at hb ⊢
        omega
  exact h p a b hp.2.1 hp.2.2.1 hp.2.2.2

end STACS2027
