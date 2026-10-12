module

public import ApproximationHardness.Embed.Orient
public import ApproximationHardness.Embed.IncGraph
public import ApproximationHardness.Planar.ExplicitOrientation
import Lean.Elab.Tactic.Omega

/-!
# The planar embedding of the incidence graph, as computed

For a Definition 7 formula `f` whose incidence graph is planar: search the incidence graph
(`incDG f`), run the solver on the plan of the resulting forest, orient its groups by the
orientation pass from any arrays recording its merges, and read off the bits; the rotation list
of the resulting embedding (`rotOut`) is a planar rotation list of the incidence graph
(`rotOut_planar`).
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.SAT Complexity.Planar STACS2027.PlanarGluing STACS2027.PlanarAssembly

namespace ForestData

variable {F : ForestData} (hF : F.Valid)
include hF

/-- The nodes below a node of the plan: itself, or vertices of its subtree. -/
theorem below_desc {v w : Nat} (h : (F.plan hF).Below v w) : w = v ∨ (F.IsVertex w ∧
    ((F.IsVertex v ∧ F.Desc v w) ∨ ∃ r, v = F.top r ∧ F.IsVertex r ∧ F.IsRoot r ∧ F.Desc r w)) := by
  induction h with
  | refl => exact Or.inl rfl
  | @step w c _ hc ih =>
    right
    have hcp : Item.node c ∈ F.parts w := hc
    have hchild : ∀ {u : Nat}, F.IsVertex u → ∀ q ∈ F.dartsAt u, F.IsDown q → c = F.rep (pair q) →
        F.IsVertex c ∧ F.Desc u c := by
      intro u _ q hq hqd hcq
      obtain ⟨hql, hqr⟩ := mem_dartsAt.mp hq
      obtain ⟨h1, _, h3⟩ := down_child hF hql hqd
      subst hcq
      exact ⟨h1, ⟨1, by show F.up _ = u; rw [h3, hqr]⟩⟩
    rcases node_part hcp with ⟨hw, q, hq, -, hqd, hcq⟩ | ⟨r, hr, hroot, hwt, hc'⟩
    · obtain ⟨hcv, hdesc⟩ := hchild hw q hq hqd hcq
      refine ⟨hcv, ?_⟩
      rcases ih with rfl | ⟨_, (⟨hv, hvw⟩ | ⟨r, hvt, hr, hroot, hrw⟩)⟩
      · exact Or.inl ⟨hw, hdesc⟩
      · exact Or.inl ⟨hv, desc_trans hvw hdesc⟩
      · exact Or.inr ⟨r, hvt, hr, hroot, desc_trans hrw hdesc⟩
    · -- `w` is the top of `r`, a top is only below itself
      have hwv : w = v := by
        rcases ih with h | ⟨hwv', _⟩
        · exact h
        · exact absurd (hwt ▸ hwv') (top_isTop hr hroot).1
      subst hwv
      have hcr : F.IsVertex c ∧ F.Desc r c := by
        rcases hc' with rfl | ⟨hzl, hzd, hcz⟩
        · exact ⟨hr, desc_refl _⟩
        · exact hchild hr _ (zOf_mem hzl).1 hzd hcz
      exact ⟨hcr.1, Or.inr ⟨r, hwt, hr, hroot, hcr.2⟩⟩

end ForestData

namespace DG

variable {G : DG} (hG : G.Ok)
include hG

/-- The post-order of the search orders the plan of its forest. -/
theorem postOrder_final : ForestData.PostOrder (G.fd G.final) (valid_final hG) G.final.post := by
  obtain ⟨hnd, hmem, hdesc, htop⟩ := post_final hG
  have hF := valid_final hG
  refine ⟨hnd, fun v hv => ?_, fun v x hx => ?_, fun v w hb hwv hv => ?_⟩
  · show v < 4 * G.E
    rcases (hmem v).mp hv with ⟨h, _⟩ | ⟨h1, h2, _⟩ <;> omega
  · obtain ⟨p, q, hf⟩ := Sol.Good.fork_of_cons (ForestData.good hF) hx
    have hpq : (G.fd G.final).parts v = [p, q] := hf.parts
    by_cases hvv : (G.fd G.final).IsVertex v
    · exact (hmem v).mpr (Or.inl hvv)
    · by_cases hvt : (G.fd G.final).IsTop v
      · obtain ⟨h1, h2, h3⟩ := hvt
        exact (hmem v).mpr (Or.inr ⟨h1, h2.1, h2.2, h3⟩)
      · rw [ForestData.parts_other hvv hvt] at hpq; simp at hpq
  · rcases ForestData.below_desc hF hb with h | ⟨hw, (⟨hvv, hd⟩ | ⟨r, rfl, hr, hroot, hd⟩)⟩
    · exact absurd h hwv
    · exact ⟨(hmem w).mpr (Or.inl hw), hdesc v w hvv.1 hvv.2 hd hw.1 hw.2 hwv⟩
    · exact ⟨(hmem w).mpr (Or.inl hw), htop r w hr.1 hr.2 hroot hd hw.1 hw.2⟩

end DG

/-! ### The formula -/

variable {f : CNF}

/-- The forest of the search of the incidence graph. -/
def incF (f : CNF) : ForestData := (incDG f).fd (incDG f).final

theorem incF_valid (hf : BoundedOccurrence f) : (incF f).Valid := DG.valid_final (incOk hf)

/-- The bits read off an orientation. -/
def incBits (hf : BoundedOccurrence f) (o : Nat → Bool) : Nat → Bool :=
  ((incF f).sol (incF_valid hf)).bit o

/-- **The output rotation list**: for every dart, the dart before it around its vertex. -/
def rotOut (hf : BoundedOccurrence f) (o : Nat → Bool) : List Nat :=
  (List.range (2 * f.flatten.length)).map (ForestData.rotInvN (incF_valid hf) (incBits hf o))

theorem nonempty_of_bounded (hf : BoundedOccurrence f) : NonemptyClauses f := fun c hc e => by
  rcases hf.1 c hc with h | h <;> rw [e] at h <;> simp at h

theorem incidence_reaches_iff (hf : BoundedOccurrence f) {d d' : Nat} (hd : d < 2 * f.flatten.length)
    (hd' : d' < 2 * f.flatten.length) :
    halfEdgeEnd (incidenceGraph f) d = halfEdgeEnd (incidenceGraph f) d' ↔ (incF f).rep d' = (incF f).rep d := by
  show _ ↔ incRep f d' = incRep f d
  rw [incRep_eq_iff (nonempty_of_bounded hf) hd' hd]
  exact eq_comm

/-- **The rotation list of a consistent orientation is planar.** -/
theorem rotOut_planar (hf : BoundedOccurrence f) (hp : PlanarGraph (incidenceGraph f)) {o : Nat → Bool}
    (ho : ((incF f).sol (incF_valid hf)).Consistent o) : IsPlanarRotation f (rotOut hf o) := by
  have hF := incF_valid hf
  have hlen := incidence_length f
  -- the embedding given by planarity
  have hex : ∃ G : Hypermap (2 * (incF f).E), IsGraphEdge G.edge ∧
      (∀ d d', Reaches G.node d d' ↔ (incF f).rep d'.val = (incF f).rep d.val) ∧ G.Planar := by
    unfold PlanarGraph at hp
    rw [hlen] at hp
    obtain ⟨G, he, hn, hpl⟩ := hp
    refine ⟨G, he, fun d d' => ?_, hpl⟩
    rw [← incidence_reaches_iff hf d.isLt d'.isLt]
    exact hn d d'
  have hpl := ForestData.planar_of_consistent hF hex ho
  obtain ⟨he, hn⟩ := ForestData.hyp_valid hF (incBits hf o)
  unfold IsPlanarRotation
  rw [hlen]
  refine ⟨ForestData.hyp hF (incBits hf o), fun d => he d, fun d d' => ?_, hpl, by simp [rotOut], fun d => ?_⟩
  · rw [incidence_reaches_iff hf d.isLt d'.isLt]
    exact hn d d'
  · simp only [rotOut, List.getElem?_map, List.getElem?_range d.isLt, Option.map_some]
    rfl

end STACS2027.Embed
