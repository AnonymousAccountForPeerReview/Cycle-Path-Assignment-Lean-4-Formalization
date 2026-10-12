module

public import NPHardness.PlanarGluingSpherical

/-! A concrete spherical embedding of a two-edge path, used for fresh
padding clauses in the incidence graph. -/

@[expose] public section
namespace STACS2027.PlanarGluing
open Complexity Complexity.Planar

def pathEdges : List (Nat × Nat) := [(0, 1), (2, 1)]

def pathEmbedding : EmbedTables where
  n2 := 2
  EN := fun d => [0, 1, 2, 1].getD d 0
  N := fun d => [0, 3, 2, 1].getD d 0
  F := fun d => [3, 0, 1, 2].getD d 0
  R := fun d => [0, 0, 0, 1].getD d 0
  FL := fun _ => 0
  CL := fun _ => 0
  D := fun d => [0, 1, 3, 2].getD d 0
  SU := fun d => [0, 0, 3, 1].getD d 0
  cR := runCount (fun d => decide ([0, 0, 0, 1].getD d 0 = 0))
  cF := runCount (fun d => decide (0 = d))
  cC := runCount (fun d => decide (0 = d))

theorem pathEmbedding_valid : Planar.EmbedOK pathEmbedding := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 4, pathEmbedding.N d < 4 ∧ pathEmbedding.F d < 4) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ h : Fin 2, pathEmbedding.N (pathEmbedding.F (2*h+1)) = 2*h ∧ pathEmbedding.N (pathEmbedding.F (2*h)) = 2*h+1) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 4, pathEmbedding.EN (pathEmbedding.N d) = pathEmbedding.EN d) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 4, pathEmbedding.R (pathEmbedding.N d) = pathEmbedding.R d+1 ∨ pathEmbedding.R (pathEmbedding.N d) = 0) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 4, pathEmbedding.R d < 4) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ h : Fin 2, (0 < pathEmbedding.R (2*h) → pathEmbedding.R (pathEmbedding.F (2*h+1))+1 = pathEmbedding.R (2*h)) ∧ (0 < pathEmbedding.R (2*h+1) → pathEmbedding.R (pathEmbedding.F (2*h))+1 = pathEmbedding.R (2*h+1))) ⟨d, hd⟩
  · intro d hd d' hd'
    exact (by decide : ∀ d d' : Fin 4, pathEmbedding.EN d = pathEmbedding.EN d' → pathEmbedding.R d = 0 → pathEmbedding.R d' = 0 → d.val = d'.val) ⟨d, hd⟩ ⟨d', hd'⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 4, pathEmbedding.FL d ≤ d ∧ pathEmbedding.FL (pathEmbedding.F d) = pathEmbedding.FL d) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 4, pathEmbedding.CL d ≤ d ∧ (pathEmbedding.D d = 0 ↔ pathEmbedding.CL d = d)) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 4, 0 < pathEmbedding.D d → pathEmbedding.SU d < 4 ∧ pathEmbedding.D (pathEmbedding.SU d)+1 = pathEmbedding.D d ∧ pathEmbedding.CL (pathEmbedding.SU d) = pathEmbedding.CL d ∧ (pathEmbedding.SU d = Planar.ed d ∨ pathEmbedding.SU d = pathEmbedding.N d ∨ pathEmbedding.SU d = pathEmbedding.F d)) ⟨d, hd⟩
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [pathEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [pathEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [pathEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · decide

theorem pathEmbedding_ends :
    ∀ d, d < 2 * pathEmbedding.n2 → halfEdgeEnd pathEdges d = some (pathEmbedding.EN d) := by
  intro d hd
  exact (by decide : ∀ d : Fin 4, halfEdgeEnd pathEdges d = some (pathEmbedding.EN d)) ⟨d, hd⟩

/-- Registered tables satisfying the strict final Euler check give a
spherical graph witness. -/
def sphericalOfTables (es : List (Nat × Nat)) (t : EmbedTables) (h : EmbedOK t)
    (hlen : es.length = t.n2)
    (hends : ∀ d, d < 2 * t.n2 → halfEdgeEnd es d = some (t.EN d))
    (hEuler : 2 * t.cC (2 * t.n2) + t.n2 ≤ t.cR (2 * t.n2) + t.cF (2 * t.n2)) :
    SphericalEmbedding es :=
  SphericalEmbedding.of_data hlen h.hypermap (fun _ => rfl) (fun d d' => by
    rw [hends d.val d.isLt, hends d'.val d'.isLt]
    constructor
    · rintro ⟨k, hk⟩
      have := h.iterate_EN k d.isLt
      rw [← h.iterate_node k d, hk] at this
      rw [this]
    · intro hE
      obtain ⟨k, hk⟩ := h.orbit d.isLt d'.isLt (Option.some.inj hE)
      exact ⟨k, Fin.ext (by rw [h.iterate_node k d, hk])⟩)
    (tables_spherical h hEuler)

def pathSpherical : SphericalEmbedding pathEdges :=
  sphericalOfTables pathEdges pathEmbedding pathEmbedding_valid rfl pathEmbedding_ends (by decide)

/-- A path with any three distinct vertex names has a strict spherical embedding. -/
def sphericalTwoEdgePath {V : Type} (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    SphericalEmbedding [(a, c), (b, c)] := by
  let f : Nat → V := fun i => if i = 0 then a else if i = 1 then c else b
  have hinj : ∀ d d' : Fin (2 * pathEdges.length),
      (halfEdgeEnd pathEdges d.val).map f = (halfEdgeEnd pathEdges d'.val).map f →
      halfEdgeEnd pathEdges d.val = halfEdgeEnd pathEdges d'.val := by
    intro d d' he
    have hd : d.val = 0 ∨ d.val = 1 ∨ d.val = 2 ∨ d.val = 3 := by
      have hh : d.val < 4 := d.isLt
      omega
    have hd' : d'.val = 0 ∨ d'.val = 1 ∨ d'.val = 2 ∨ d'.val = 3 := by
      have hh : d'.val < 4 := d'.isLt
      omega
    rcases hd with hd | hd | hd | hd <;> rcases hd' with hd' | hd' | hd' | hd' <;>
      simp [halfEdgeEnd, pathEdges, hd, hd', f, hab, hac, hbc, Ne.symm hab, Ne.symm hac,
        Ne.symm hbc] at he ⊢
  have h := pathSpherical.relabel_ends f hinj
  simpa [pathEdges, f] using h

end STACS2027.PlanarGluing
