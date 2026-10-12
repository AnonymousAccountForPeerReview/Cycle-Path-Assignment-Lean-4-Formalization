module

public import NPHardness.PlanarAssemblyFaces

/-!
Local boundary-routing data for simultaneous assembly. The data describe how
original gadget-face segments meet the cyclic order of incidence darts. They
do not assume planarity or any property of assembled face-cycle labels.
The resulting theorem supplies the global face-count lower bound, including
all retained parallel-port digons and all untouched interior gadget faces.
-/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar

/-- Combinatorial boundary order connecting local outer faces to a source
incidence rotation. `boundary` labels an unmarked segment by its source dart.
`before_port` and `after_port` express the required cyclic-order agreement. -/
structure BoundaryRouting {n m : Nat} {G : Hypermap n} (P : PortPairing G) (I : Hypermap m) where
  port : Fin m → Fin n
  marked_port : ∀ i, P.marked (port i) = true
  every_marked : ∀ d, P.marked d = true → ∃ i, port i=d
  pair_port : ∀ i, P.pair (port i) = port (I.edge i)
  edge_involution : ∀ i, I.edge (I.edge i) = i
  boundary : Fin n → Option (Fin m)
  after_port : ∀ i, boundary (G.face (port i)) = some (I.edge i)
  before_port : ∀ i, boundary (faceInverse G (port i)) = some (faceInverse I i)
  unmarked_step : ∀ d, P.marked d = false → P.marked (G.face d) = false →
    boundary (G.face d) = boundary d

namespace BoundaryRouting
variable {n m : Nat} {G : Hypermap n} {P : PortPairing G} {I : Hypermap m}
  (B : BoundaryRouting P I)

/-- Interior roots are actual original face minima on untouched boundary-free
segments. This finite count is independent of the assembled face minima. -/
def interiorRoot (d : Fin n) : Bool :=
  CycleMin G.face d && !P.marked d && decide (B.boundary d = none)

def interiorFaceCount : Nat := (List.finRange n).countP B.interiorRoot

/-- An invariant distinguishing retained-edge digons, untouched local interior
faces, and the faces of the source incidence embedding. -/
noncomputable def faceLabel (d : Fin n) : Nat × Nat :=
  if P.marked d then (0,(cmin P.assembled.face d).val)
  else match B.boundary d with
    | none => (1,(cmin G.face d).val)
    | some i => (2,(cmin I.face i).val)

theorem faceLabel_step (d : Fin n) : B.faceLabel (P.assembled.face d) = B.faceLabel d := by
  cases hd : P.marked d
  · have hn := P.assembled_face_preserves_marked d
    rw [hd] at hn
    simp only [faceLabel,hd,hn,Bool.false_eq_true,↓reduceIte]
    cases hf : P.marked (G.face d)
    · have hnew : P.assembled.face d = G.face d := by
        rw [P.assembled_face_unmarked hd,hf]; rfl
      rw [hnew,B.unmarked_step d hd hf]
      cases hb : B.boundary d
      · simp only [cmin_step (hm_face_inj G)]
      · rfl
    · obtain ⟨i,hi⟩ := B.every_marked _ hf
      have hbefore : d = faceInverse G (B.port i) := by
        rw [hi,faceInverse_face]
      have hnew : P.assembled.face d = G.face (B.port (I.edge i)) := by
        rw [P.assembled_face_unmarked hd,hf]
        simp only [↓reduceIte,← hi,B.pair_port]
      rw [hnew,B.after_port,B.edge_involution,hbefore,B.before_port]
      have hc := cmin_step (hm_face_inj I) (faceInverse I i)
      rw [face_faceInverse] at hc
      change (2,(cmin I.face i).val) = (2,(cmin I.face (faceInverse I i)).val)
      rw [hc]
  · have hn := P.assembled_face_preserves_marked d
    rw [hd] at hn
    simp only [faceLabel,hd,hn,↓reduceIte,cmin_step (hm_face_inj P.assembled)]

theorem tagged_nodup {k : Nat} (tag : Nat) (q : Fin k → Bool) :
    (((List.finRange k).filter q).map (fun d => (tag,d.val))).Nodup := by
  apply nodup_map_of_injOn' _ ((List.nodup_finRange k).filter q)
  intro a _ b _ h
  exact Fin.ext (congrArg Prod.snd h)

theorem tags_disjoint {k l : Nat} (a b : Nat) (ha : a≠b)
    (q : Fin k → Bool) (r : Fin l → Bool) :
    ∀ x ∈ (((List.finRange k).filter q).map (fun d => (a,d.val))),
      ∀ y ∈ (((List.finRange l).filter r).map (fun d => (b,d.val))), x ≠ y := by
  intro x hx y hy heq
  obtain ⟨u,_,hu⟩ := List.mem_map.mp hx
  obtain ⟨v,_,hv⟩ := List.mem_map.mp hy
  have he := congrArg Prod.fst (hu.trans (heq.trans hv.symm))
  exact ha he

/-- Face lower bound used by the Euler calculation for global assembly. -/
theorem face_count_lower_bound :
    P.digonCount + B.interiorFaceCount + cycleCount I.face ≤ cycleCount P.assembled.face := by
  let ds := ((List.finRange n).filter P.digonRoot).map (fun d => (0,d.val))
  let ins := ((List.finRange n).filter B.interiorRoot).map (fun d => (1,d.val))
  let src := ((List.finRange m).filter (CycleMin I.face)).map (fun d => (2,d.val))
  let labels := ds ++ (ins ++ src)
  have hnd : labels.Nodup := by
    rw [List.nodup_append,List.nodup_append]
    refine ⟨tagged_nodup 0 _,⟨tagged_nodup 1 _,tagged_nodup 2 _,?_⟩,?_⟩
    · exact tags_disjoint 1 2 (by decide) _ _
    · intro x hx y hy hxy
      rcases List.mem_append.mp hy with hy | hy
      · exact tags_disjoint 0 1 (by decide) _ _ x hx y hy hxy
      · exact tags_disjoint 0 2 (by decide) _ _ x hx y hy hxy
  have hatt : ∀ l ∈ labels, ∃ x : Fin n, B.faceLabel x = l := by
    intro l hl
    simp only [labels,ds,ins,src,List.mem_append,List.mem_map,List.mem_filter] at hl
    rcases hl with ⟨d,⟨_,hd⟩,rfl⟩ | ⟨d,⟨_,hd⟩,rfl⟩ | ⟨i,⟨_,hi⟩,rfl⟩
    · have hh := P.marked_cycleMin_eq d
      rw [hd] at hh
      have hparts : CycleMin P.assembled.face d = true ∧ P.marked d = true := by
        simpa only [Bool.and_eq_true] using hh
      refine ⟨d,?_⟩
      simp only [faceLabel,hparts.2,↓reduceIte]
      rw [(cmin_eq_iff (hm_face_inj P.assembled) d).mpr hparts.1]
    · simp only [interiorRoot,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq] at hd
      refine ⟨d,?_⟩
      simp only [faceLabel,hd.1.2,Bool.false_eq_true,↓reduceIte,hd.2]
      rw [(cmin_eq_iff (hm_face_inj G) d).mpr hd.1.1]
    · refine ⟨G.face (B.port (I.edge i)),?_⟩
      have hu := P.face_separated _ (B.marked_port (I.edge i))
      simp only [faceLabel,hu,Bool.false_eq_true,↓reduceIte,B.after_port,B.edge_involution]
      rw [(cmin_eq_iff (hm_face_inj I) i).mpr hi]
  have hlen : labels.length = P.digonCount + B.interiorFaceCount + cycleCount I.face := by
    simp only [labels,ds,ins,src,List.length_append,List.length_map,
      ← List.countP_eq_length_filter,PortPairing.digonCount,interiorFaceCount,cycleCount_eq]
    omega
  have hbound := Subdiv.cycleCount_ge_labels P.assembled.face B.faceLabel B.faceLabel_step labels hnd hatt
  rw [hlen] at hbound
  exact hbound

end BoundaryRouting
end STACS2027.PlanarAssembly
