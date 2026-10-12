module

public import NPHardness.ClauseTwoProfiles
public import NPHardness.Acyclic

/-!
Removing the green edges leaves a five-vertex cyclic core with attached trees.
Consequently every longer skeleton cycle uses a green edge. Only triangles
and quadrangles need a separate finite profile certificate.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

@[expose] public section
namespace STACS2027

def clauseTwoNonGreen : Graph := clauseTwoSkeleton.filter fun e => !clauseTwoGreen.contains e
def clauseTwoCore : List Nat := [19,20,21,22,23]
def clauseTwoCoreRank (v : Nat) : Nat :=
  [4,5,3,3,4,5,7,8,8,6,2,1,2,3,2,5,6,7,3,0,0,0,0,0][v]!

theorem clauseTwo_core_rank_certificate : ∀ v a b : Fin 24,
    clauseTwoCoreRank v.val ≠ 0 →
    edge v.val a.val ∈ clauseTwoNonGreen → edge v.val b.val ∈ clauseTwoNonGreen →
    clauseTwoCoreRank a.val ≤ clauseTwoCoreRank v.val →
    clauseTwoCoreRank b.val ≤ clauseTwoCoreRank v.val → a = b := by decide

theorem clauseTwo_core_zero_certificate : ∀ v : Fin 24,
    clauseTwoCoreRank v.val = 0 → v.val ∈ clauseTwoCore := by decide

theorem clauseTwo_nonGreen_core_rank : CycleCoreRank clauseTwoNonGreen clauseTwoCoreRank := by
  intro v a b hv ha hb hra hrb
  have hbound := (clauseTwo_links_wellformed 5).1
  have hba := (edge_below v a 24).mp (hbound _ (List.mem_filter.mp ha).1)
  have hbb := (edge_below v b 24).mp (hbound _ (List.mem_filter.mp hb).1)
  have h := clauseTwo_core_rank_certificate ⟨v, hba.1⟩ ⟨a, hba.2⟩ ⟨b, hbb.2⟩ hv ha hb hra hrb
  exact congrArg Fin.val h

theorem clauseTwo_nonGreen_cycle_bound {r : Nat} {c : Cycle}
    (hc : IsCycle clauseTwoNonGreen r c) : r ≤ 5 := by
  have hz := clauseTwo_nonGreen_core_rank.cycle_zero hc
  have hs : c ⊆ clauseTwoCore := by
    intro v hv
    obtain ⟨w, _, he⟩ := hc.vertex_incident hv
    have hbase := (List.mem_filter.mp (hc.2.2.2 _ he)).1
    have hvb := ((edge_below v w 24).mp ((clauseTwo_links_wellformed 5).1 _ hbase)).1
    exact clauseTwo_core_zero_certificate ⟨v, hvb⟩ (hz v hv)
  have h := hc.2.2.1.length_le_of_subset hs
  simpa only [hc.2.1, clauseTwoCore, List.length_cons, List.length_nil] using h

theorem clauseTwo_long_cycle_uses_green {r : Nat} {c : Cycle}
    (hc : IsCycle clauseTwoSkeleton r c) (hr : 5 < r) : 1 ≤ colourCount clauseTwoGreen c := by
  classical
  have hex : ∃ e ∈ cycleEdges c, e ∈ clauseTwoGreen := by
    by_cases h : ∃ e ∈ cycleEdges c, e ∈ clauseTwoGreen
    · exact h
    have hc' : IsCycle clauseTwoNonGreen r c := by
      refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
      intro e he
      apply List.mem_filter.mpr
      exact ⟨hc.2.2.2 e he, by simpa using (fun hg => h ⟨e, he, hg⟩)⟩
    have hbound := clauseTwo_nonGreen_cycle_bound hc'
    omega
  obtain ⟨e, he, hg⟩ := hex
  have hmem : e ∈ (cycleEdges c).filter clauseTwoGreen.contains := by simp [he, hg]
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem hmem)

theorem clauseTwo_short_profile_certificate :
    ∀ c ∈ cycles clauseTwoSkeleton 3 ++ cycles clauseTwoSkeleton 4,
      clauseTwoProfile c ∈ clauseTwoExcludedProfiles := by decide

end STACS2027
