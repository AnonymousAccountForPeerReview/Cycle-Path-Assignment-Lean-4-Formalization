module

public import NPHardness.PlanarOperationsPrograms
public import NPHardness.PlanarGluingLists
public import NPHardness.RegisteredGadgetEmbeddings

/-!
Every parameterized Figure 4 gadget is planar in the registered hypermap
sense. The proof follows the existing concrete subdivision program, with
its actual fresh-vertex labels and its actual edge-list multiplicities.
-/

@[expose] public section
namespace STACS2027
open Complexity

/-- One concrete subdivision at the current unused upper-bound label. -/
theorem planar_subdivideOnce_bounded {g : Graph} {a b next : Nat}
    (hn : g.Nodup) (hb : VerticesBelow g next) (he : edge a b ∈ g)
    (hp : PlanarGraph g) : PlanarGraph (subdivideOnce g a b next) := by
  let es := g.filter (· != edge a b)
  have hperm : g.Perm (es ++ [edge a b]) := by
    have h : g.Perm (edge a b :: es) := by
      simpa only [hn.erase_eq_filter] using List.perm_cons_erase he
    exact h.trans (List.perm_append_comm (l₁ := [edge a b]) (l₂ := es))
  have hsource := (PlanarGluing.planarGraph_perm hperm).mp hp
  have hsub := PlanarOperations.Subdivision.planar_subdivide es [edge a b] (fun _ => next)
    (by intro u hu v hv _; simp only [List.length_singleton] at hu hv; omega)
    (by
      intro e he' u _
      have hm : e ∈ g := hperm.mem_iff.mpr he'
      exact ⟨Nat.ne_of_lt (hb e hm).1,Nat.ne_of_lt (hb e hm).2⟩) hsource
  have hab := (edge_below a b next).mp (hb _ he)
  have ht := (splitEdges_singleton_perm a b next hab.1 hab.2).append_left es
  have hq : (es ++ [edge a next,edge next b]).Perm (subdivideOnce g a b next) :=
    List.perm_append_comm
  exact (PlanarGluing.planarGraph_perm (ht.trans hq)).mp hsub

/-- Repeated subdivisions along one original edge preserve registered planarity. -/
theorem planar_chainSteps {g : Graph} (a b next s : Nat)
    (hg : VerticesBelow g next) (hn : g.Nodup) (hab : a ≠ b)
    (he : edge a b ∈ g) (hp : PlanarGraph g) :
    PlanarGraph (subdivisionGraph g (chainSteps a b next s)) := by
  induction s generalizing g a next with
  | zero => exact hp
  | succ s ih =>
    have hv := (edge_below a b next).mp (hg _ he)
    exact ih next (next+1) (subdivideOnce_below hg hv.1 hv.2)
      (subdivideOnce_nodup hn hab he hg.fresh) (by omega)
      (mem_subdivideOnce.mpr (Or.inr (Or.inl rfl)))
      (planar_subdivideOnce_bounded hn hg he hp)

/-- The full straight-chain program preserves registered planarity. -/
theorem planar_linkSteps {g : Graph} (next : Nat) (ls : List Link)
    (hg : VerticesBelow g next) (hgn : g.Nodup) (hn : (linkEdges ls).Nodup)
    (hl : ∀ l ∈ ls, l.source ≠ l.target ∧ edge l.source l.target ∈ g)
    (hp : PlanarGraph g) : PlanarGraph (subdivisionGraph g (linkSteps next ls)) := by
  induction ls generalizing g next with
  | nil => exact hp
  | cons l ls ih =>
    obtain ⟨he,ht⟩ := List.nodup_cons.mp hn
    obtain ⟨hne,hmem⟩ := hl l (by simp)
    have hb := (edge_below l.source l.target next).mp (hg _ hmem)
    rw [linkSteps,subdivisionGraph_append]
    apply ih _ (chainSteps_below _ _ _ _ hg hb.1 hb.2)
      (subdivisionGraph_nodup _ _ hgn (chainSteps_valid _ _ _ _ hg hne hmem)) ht
    · intro r hr
      obtain ⟨hrne,hrmem⟩ := hl r (by simp [hr])
      refine ⟨hrne,chainSteps_retains _ _ _ _ hg hne hmem _ hrmem ?_⟩
      intro heq
      apply he
      exact List.mem_map.mpr ⟨r,hr,heq⟩
    · exact planar_chainSteps _ _ _ _ hg hgn hne hmem hp

/-- Every actual graph produced by `realizeLinks` is planar whenever its simple
skeleton is planar and its stated freshness conditions hold. -/
theorem planar_realizeLinks (next : Nat) (ls : List Link)
    (hb : VerticesBelow (linkEdges ls) next) (hn : (linkEdges ls).Nodup)
    (hp : ∀ l ∈ ls, l.source ≠ l.target) (hplanar : PlanarGraph (linkEdges ls)) :
    PlanarGraph (realizeLinks next ls) := by
  have hs := planar_linkSteps next ls hb hn hn
    (fun l hl => ⟨hp l hl,List.mem_map.mpr ⟨l,hl,rfl⟩⟩) hplanar
  exact (PlanarGluing.planarGraph_perm (realizeLinks_perm_subdivisionGraph next ls hb hn hp)).mpr hs

theorem variableGraph_planar (k : Nat) : PlanarGraph (variableGraph k) := by
  obtain ⟨hb,hn,hp⟩ := variable_links_wellformed k
  exact planar_realizeLinks _ _ hb hn hp variable_skeleton_planar

theorem clauseThreeGraph_planar (k : Nat) : PlanarGraph (clauseThreeGraph k) := by
  obtain ⟨hb,hn,hp⟩ := clauseThree_links_wellformed k
  exact planar_realizeLinks _ _ hb hn hp clauseThree_skeleton_planar

theorem clauseTwoGraph_planar (k : Nat) : PlanarGraph (clauseTwoGraph k) := by
  obtain ⟨hb,hn,hp⟩ := clauseTwo_links_wellformed k
  exact planar_realizeLinks _ _ hb hn hp clauseTwo_skeleton_planar

end STACS2027
