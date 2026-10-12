module

public import NPHardness.PlanarPreprocessDeletionGraph
public import NPHardness.PlanarPreprocessDeletionComponents
public import NPHardness.PlanarPreprocessIncidence
public import NPHardness.PlanarGluingPadding
public import Complexity.Planar.GridTarget

/-! Edge deletion and the complete preprocessing planarity bridge, using the
actual registered hypermap predicate throughout. -/

@[expose] public section
namespace STACS2027.PlanarPreprocess
open Complexity Complexity.SAT Complexity.Planar STACS2027.PlanarGluing
open Deletion

theorem cutThenShrink_planar {n : Nat} (G : Hypermap (n+2))
    (ha : G.edge (penultimate n) = last (n+1)) (hb : G.edge (last (n+1)) = penultimate n)
    (hp : G.Planar) : (cutThenShrink G ha hb).Planar := by
  apply shrinkLast_planar
  apply shrinkLast_planar
  exact cut_planar G _ _ (penultimate_ne_last n) ha hb hp

/-- Removing a stored edge, including a loop or one of several parallel
edges, preserves the registered planarity predicate. -/
theorem planarGraph_dropLast {V : Type} (es : List (V×V)) (e : V×V)
    (hp : PlanarGraph (es++[e])) : PlanarGraph es := by
  unfold PlanarGraph at hp ⊢
  rw [List.length_append] at hp
  simp only [List.length_cons,List.length_nil] at hp
  obtain ⟨G,he,hn,hp⟩ := hp
  change (∀ d, (G.edge d).val = ed d.val) at he
  refine ⟨cutThenShrink G (graphEdge_last_pair G he).1 (graphEdge_last_pair G he).2,?_,?_,?_⟩
  · exact cutThenShrink_graphEdge G he
  · exact cutThenShrink_graphNodes es e G he hn
  · exact cutThenShrink_planar G _ _ hp

theorem planarGraph_sublist_prefix {V : Type} {es ts : List (V×V)} (h : es.Sublist ts) :
    ∀ pre : List (V×V), PlanarGraph (pre++ts) → PlanarGraph (pre++es) := by
  induction h with
  | slnil => intro pre hp; exact hp
  | @cons es ts e h ih =>
    intro pre hp
    have he : (pre++e::ts).Perm ((pre++ts)++[e]) := by
      simpa only [List.append_assoc,List.singleton_append] using
        (List.perm_append_comm (l₁ := [e]) (l₂ := ts)).append_left pre
    exact ih pre (planarGraph_dropLast _ e ((planarGraph_perm he).mp hp))
  | @cons_cons es ts e h ih =>
    intro pre hp
    have he : PlanarGraph ((pre++[e])++ts) := by
      simpa only [List.append_assoc,List.singleton_append] using hp
    have ht := ih (pre++[e]) he
    simpa only [List.append_assoc,List.singleton_append] using ht

/-- Genuine subgraph closure, retaining the edge-list multiplicities. -/
theorem planarGraph_sublist {V : Type} {es ts : List (V×V)}
    (h : es.Sublist ts) (hp : PlanarGraph ts) : PlanarGraph es := by
  simpa only [List.nil_append] using planarGraph_sublist_prefix h [] hp

theorem Prunes.planar {g f : CNF} (h : Prunes g f) (hp : PlanarGraph (incidenceGraph f)) :
    PlanarGraph (incidenceGraph g) := by
  obtain ⟨ρ,hρ,hs⟩ := h.incidence_sublist
  exact (planarGraph_map_injective (incidenceGraph g) (renameClause ρ)
    (renameClause_injective hρ)).mp (planarGraph_sublist hs hp)

theorem normalized_output_planar {f : CNF} {t : Nat} {mem : LinearPreprocessUnits.Memory}
    (h : LinearPreprocessUnits.Executes (LinearPreprocessInit.initialAdj (normalizeClauses f)) t
      (.running (LinearPreprocessInit.initialMemory (normalizeClauses f))
        (List.range (normalizeClauses f).length)) (.done mem))
    (hp : PlanarGraph (incidenceGraph f)) :
    PlanarGraph (incidenceGraph (LinearPreprocessUnits.contents (normalizeClauses f).length mem)) :=
  (normalized_output_prunes h).planar hp

/-- The graph pipeline's actual queue result and charged padding also preserve
planarity.  No equality with the older, differently ordered unit pass is used. -/
theorem normalized_output_padded_planar {f : CNF} {t : Nat} {mem : LinearPreprocessUnits.Memory}
    (h : LinearPreprocessUnits.Executes (LinearPreprocessInit.initialAdj (normalizeClauses f)) t
      (.running (LinearPreprocessInit.initialMemory (normalizeClauses f))
        (List.range (normalizeClauses f).length)) (.done mem))
    (hp : PlanarGraph (incidenceGraph f)) :
    PlanarGraph (incidenceGraph (padFormula
      (f.length-(LinearPreprocessUnits.contents (normalizeClauses f).length mem).length)
      (LinearPreprocessUnits.contents (normalizeClauses f).length mem))) :=
  planar_incidence_padFormula _ _ (normalized_output_planar h hp)

theorem contradiction_padded_planar (budget : Nat) :
    PlanarGraph (incidenceGraph (padFormula (budget+1) [])) :=
  planar_incidence_padFormula _ _ Complexity.Planar.Grid.planarGraph_nil

end STACS2027.PlanarPreprocess
