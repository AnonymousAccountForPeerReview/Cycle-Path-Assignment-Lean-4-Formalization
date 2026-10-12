module

public import ApproximationHardness.Embed.Computed
public import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega

/-!
# Linear accounting for the embedding solver

Every consumed group disappears permanently. Its identifier is either a dart
below `2E` or a group created at a plan node below `4E`, with identifier `4E + v`.
Thus all merges together consume at most `8E` groups, independently of the
lengths of their classes. This is the amortized event bound for a linked implementation.
-/

@[expose] public section

namespace STACS2027.Embed.ForestData

variable {F : ForestData} (hF : F.Valid)

/-- The identifiers consumed by all nodes, in node order. -/
def consumptionIds (post : List Nat) : List Nat :=
  post.flatMap fun v => ((F.sol hF).consAt v).map Prod.fst

theorem consAt_ids_nodup (v : Nat) : (((F.sol hF).consAt v).map Prod.fst).Nodup := by
  by_cases hn : (F.sol hF).consAt v = []
  · simp [hn]
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil ((F.sol hF).consAt v) hn
    obtain ⟨p, q, hf⟩ := Sol.Good.fork_of_cons (good hF) hx
    exact ((tree hF).cons_ok (good hF) hf).2.1

/-- No identifier is consumed by two different nodes or twice at the same node. -/
theorem consumptionIds_nodup {post : List Nat} (hP : PostOrder F hF post) :
    (consumptionIds hF post).Nodup := by
  unfold consumptionIds
  apply List.nodup_flatMap.mpr
  refine ⟨fun v _ => consAt_ids_nodup hF v, hP.nodup.imp ?_⟩
  intro v w hne g hg hw
  obtain ⟨x, hx, hxg⟩ := List.mem_map.mp hg
  obtain ⟨y, hy, hyg⟩ := List.mem_map.mp hw
  exact hne ((tree hF).consumed_unique (good hF) hx hy (hxg.trans hyg.symm)).1

/-- All consumed identifiers lie in the linear-size identifier range. -/
theorem consumptionIds_lt {post : List Nat} (hP : PostOrder F hF post) :
    ∀ g ∈ consumptionIds hF post, g < 8 * F.E := by
  intro g hg
  obtain ⟨v, hv, hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
  rcases consumed_gid_or_dart hF hx with ⟨w, hbw, hwv, he⟩ | hlt
  · have hw : w ∈ post := (hP.below v w hbw hwv hv).1
    have hb := hP.lt w hw
    rw [he]
    unfold gid
    omega
  · omega

/-- At most linearly many group-consumption events occur in the entire solver. -/
theorem consumptionIds_length_le {post : List Nat} (hP : PostOrder F hF post) :
    (consumptionIds hF post).length ≤ 8 * F.E :=
  length_le_of_nodup_lt _ _ (consumptionIds_nodup hF hP) (consumptionIds_lt hF hP)

/-- Post-order visits and group consumption together have a linear bound. -/
theorem solver_events_le {post : List Nat} (hP : PostOrder F hF post) :
    post.length + (consumptionIds hF post).length ≤ 12 * F.E := by
  have hp := length_le_of_nodup_lt (4 * F.E) post hP.nodup hP.lt
  have hc := consumptionIds_length_le hF hP
  omega

end STACS2027.Embed.ForestData
