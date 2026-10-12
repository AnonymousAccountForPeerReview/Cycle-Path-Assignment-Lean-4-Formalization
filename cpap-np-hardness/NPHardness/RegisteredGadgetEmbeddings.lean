module

public import NPHardness.PlanarFoundation
public import NPHardness.GadgetProjection

/-!
Concrete embeddings of the three Figure 4 skeletons, checked against the
registered `Complexity.Planar.EmbedOK` predicate. The tables were found using
an external development aid; all certificate proofs use kernel `decide`.
No external program, axiom, or `native_decide` is trusted by these proofs.
Subdivision and global attachment preservation are separate obligations.
-/

@[expose] public section
namespace STACS2027
open Complexity
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def variableEmbedding : Planar.EmbedTables where
  n2 := 8
  EN := fun d => [0, 1, 1, 2, 3, 4, 5, 6, 0, 3, 1, 4, 4, 5, 2, 6].getD d 0
  N := fun d => [8, 2, 10, 14, 9, 11, 13, 15, 0, 4, 1, 12, 5, 6, 3, 7].getD d 0
  F := fun d => [10, 8, 14, 1, 12, 9, 15, 13, 4, 0, 5, 2, 6, 11, 7, 3].getD d 0
  R := fun d => [0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 2, 1, 2, 1, 1, 1].getD d 0
  FL := fun d => [0, 1, 2, 1, 1, 0, 1, 2, 1, 0, 0, 2, 1, 2, 2, 1].getD d 0
  CL := fun d => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD d 0
  D := fun d => [0, 1, 3, 2, 2, 2, 4, 4, 1, 1, 2, 3, 3, 4, 3, 3].getD d 0
  SU := fun d => [0, 0, 3, 1, 9, 9, 15, 15, 0, 0, 1, 10, 5, 11, 3, 3].getD d 0
  cR := Planar.runCount (fun d => decide ([0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 2, 1, 2, 1, 1, 1].getD d 0 = 0))
  cF := Planar.runCount (fun d => decide ([0, 1, 2, 1, 1, 0, 1, 2, 1, 0, 0, 2, 1, 2, 2, 1].getD d 0 = d))
  cC := Planar.runCount (fun d => decide ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD d 0 = d))

theorem variableEmbedding_valid : Planar.EmbedOK variableEmbedding := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 16, variableEmbedding.N d < 16 ∧ variableEmbedding.F d < 16) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ h : Fin 8, variableEmbedding.N (variableEmbedding.F (2*h+1)) = 2*h ∧ variableEmbedding.N (variableEmbedding.F (2*h)) = 2*h+1) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 16, variableEmbedding.EN (variableEmbedding.N d) = variableEmbedding.EN d) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 16, variableEmbedding.R (variableEmbedding.N d) = variableEmbedding.R d+1 ∨ variableEmbedding.R (variableEmbedding.N d) = 0) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 16, variableEmbedding.R d < 16) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ h : Fin 8, (0 < variableEmbedding.R (2*h) → variableEmbedding.R (variableEmbedding.F (2*h+1))+1 = variableEmbedding.R (2*h)) ∧ (0 < variableEmbedding.R (2*h+1) → variableEmbedding.R (variableEmbedding.F (2*h))+1 = variableEmbedding.R (2*h+1))) ⟨d, hd⟩
  · intro d hd d' hd'
    exact (by decide : ∀ d d' : Fin 16, variableEmbedding.EN d = variableEmbedding.EN d' → variableEmbedding.R d = 0 → variableEmbedding.R d' = 0 → d.val = d'.val) ⟨d, hd⟩ ⟨d', hd'⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 16, variableEmbedding.FL d ≤ d ∧ variableEmbedding.FL (variableEmbedding.F d) = variableEmbedding.FL d) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 16, variableEmbedding.CL d ≤ d ∧ (variableEmbedding.D d = 0 ↔ variableEmbedding.CL d = d)) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 16, 0 < variableEmbedding.D d → variableEmbedding.SU d < 16 ∧ variableEmbedding.D (variableEmbedding.SU d)+1 = variableEmbedding.D d ∧ variableEmbedding.CL (variableEmbedding.SU d) = variableEmbedding.CL d ∧ (variableEmbedding.SU d = Planar.ed d ∨ variableEmbedding.SU d = variableEmbedding.N d ∨ variableEmbedding.SU d = variableEmbedding.F d)) ⟨d, hd⟩
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [variableEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [variableEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [variableEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · decide

theorem variableEmbedding_ends :
    ∀ d, d < 2 * variableEmbedding.n2 → halfEdgeEnd variableSkeleton d = some (variableEmbedding.EN d) := by
  intro d hd
  exact (by decide : ∀ d : Fin 16, halfEdgeEnd variableSkeleton d = some (variableEmbedding.EN d)) ⟨d, hd⟩

theorem variable_skeleton_planar : PlanarGraph variableSkeleton :=
  variableEmbedding_valid.planarGraph rfl (fun v => v) (fun _ _ h => h) variableEmbedding_ends

/-- Every designated port meets one common face of this embedding. -/
theorem variable_skeleton_ports_cofacial :
    ∀ e ∈ variablePorts, ∃ d : Fin 16, ∃ i : Fin 16,
      iterate variableEmbedding.F i 1 = d ∧ variableSkeleton[d.val / 2]? = some e := by
  decide

def clauseThreeEmbedding : Planar.EmbedTables where
  n2 := 24
  EN := fun d => [0, 1, 0, 12, 0, 13, 1, 2, 2, 3, 2, 14, 3, 4, 3, 10, 4, 5, 4, 15, 5, 6, 6, 7, 6, 16, 7, 8, 8, 9, 8, 17, 9, 10, 9, 15, 10, 11, 11, 12, 11, 14, 13, 14, 15, 16, 16, 17].getD d 0
  N := fun d => [4, 6, 0, 39, 2, 42, 1, 8, 10, 12, 7, 41, 14, 16, 9, 33, 18, 20, 13, 44, 17, 22, 24, 26, 21, 46, 23, 28, 30, 32, 27, 47, 34, 36, 29, 19, 15, 38, 40, 3, 37, 43, 5, 11, 35, 25, 45, 31].getD d 0
  F := fun d => [6, 2, 39, 4, 42, 0, 10, 1, 14, 7, 43, 8, 18, 9, 36, 12, 20, 13, 35, 16, 24, 17, 26, 21, 45, 22, 30, 23, 34, 27, 47, 28, 15, 29, 44, 32, 40, 33, 3, 37, 11, 38, 41, 5, 46, 19, 31, 25].getD d 0
  R := fun d => [0, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 1, 2, 2, 2, 0, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1].getD d 0
  FL := fun d => [0, 1, 1, 3, 3, 0, 0, 1, 8, 1, 0, 8, 12, 1, 8, 12, 16, 1, 12, 16, 16, 1, 22, 1, 16, 22, 22, 1, 28, 1, 22, 28, 12, 1, 28, 12, 8, 1, 3, 1, 8, 3, 3, 0, 28, 16, 28, 22].getD d 0
  CL := fun d => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD d 0
  D := fun d => [0, 1, 1, 2, 2, 1, 2, 2, 4, 3, 3, 4, 5, 4, 4, 5, 6, 5, 5, 6, 6, 6, 8, 7, 7, 8, 8, 8, 8, 7, 9, 9, 6, 6, 8, 7, 5, 4, 3, 3, 4, 3, 2, 2, 8, 7, 8, 9].getD d 0
  SU := fun d => [0, 0, 0, 2, 2, 0, 1, 1, 10, 7, 7, 10, 14, 9, 9, 14, 18, 13, 13, 18, 17, 17, 24, 21, 21, 24, 23, 23, 29, 32, 27, 28, 15, 36, 29, 32, 37, 38, 3, 3, 41, 43, 5, 5, 35, 19, 45, 46].getD d 0
  cR := Planar.runCount (fun d => decide ([0, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 1, 2, 2, 2, 0, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1].getD d 0 = 0))
  cF := Planar.runCount (fun d => decide ([0, 1, 1, 3, 3, 0, 0, 1, 8, 1, 0, 8, 12, 1, 8, 12, 16, 1, 12, 16, 16, 1, 22, 1, 16, 22, 22, 1, 28, 1, 22, 28, 12, 1, 28, 12, 8, 1, 3, 1, 8, 3, 3, 0, 28, 16, 28, 22].getD d 0 = d))
  cC := Planar.runCount (fun d => decide ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD d 0 = d))

theorem clauseThreeEmbedding_valid : Planar.EmbedOK clauseThreeEmbedding := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 48, clauseThreeEmbedding.N d < 48 ∧ clauseThreeEmbedding.F d < 48) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ h : Fin 24, clauseThreeEmbedding.N (clauseThreeEmbedding.F (2*h+1)) = 2*h ∧ clauseThreeEmbedding.N (clauseThreeEmbedding.F (2*h)) = 2*h+1) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 48, clauseThreeEmbedding.EN (clauseThreeEmbedding.N d) = clauseThreeEmbedding.EN d) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 48, clauseThreeEmbedding.R (clauseThreeEmbedding.N d) = clauseThreeEmbedding.R d+1 ∨ clauseThreeEmbedding.R (clauseThreeEmbedding.N d) = 0) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 48, clauseThreeEmbedding.R d < 48) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ h : Fin 24, (0 < clauseThreeEmbedding.R (2*h) → clauseThreeEmbedding.R (clauseThreeEmbedding.F (2*h+1))+1 = clauseThreeEmbedding.R (2*h)) ∧ (0 < clauseThreeEmbedding.R (2*h+1) → clauseThreeEmbedding.R (clauseThreeEmbedding.F (2*h))+1 = clauseThreeEmbedding.R (2*h+1))) ⟨d, hd⟩
  · intro d hd d' hd'
    exact (by decide : ∀ d d' : Fin 48, clauseThreeEmbedding.EN d = clauseThreeEmbedding.EN d' → clauseThreeEmbedding.R d = 0 → clauseThreeEmbedding.R d' = 0 → d.val = d'.val) ⟨d, hd⟩ ⟨d', hd'⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 48, clauseThreeEmbedding.FL d ≤ d ∧ clauseThreeEmbedding.FL (clauseThreeEmbedding.F d) = clauseThreeEmbedding.FL d) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 48, clauseThreeEmbedding.CL d ≤ d ∧ (clauseThreeEmbedding.D d = 0 ↔ clauseThreeEmbedding.CL d = d)) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 48, 0 < clauseThreeEmbedding.D d → clauseThreeEmbedding.SU d < 48 ∧ clauseThreeEmbedding.D (clauseThreeEmbedding.SU d)+1 = clauseThreeEmbedding.D d ∧ clauseThreeEmbedding.CL (clauseThreeEmbedding.SU d) = clauseThreeEmbedding.CL d ∧ (clauseThreeEmbedding.SU d = Planar.ed d ∨ clauseThreeEmbedding.SU d = clauseThreeEmbedding.N d ∨ clauseThreeEmbedding.SU d = clauseThreeEmbedding.F d)) ⟨d, hd⟩
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [clauseThreeEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [clauseThreeEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [clauseThreeEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · decide

theorem clauseThreeEmbedding_ends :
    ∀ d, d < 2 * clauseThreeEmbedding.n2 → halfEdgeEnd clauseThree5 d = some (clauseThreeEmbedding.EN d) := by
  intro d hd
  exact (by decide : ∀ d : Fin 48, halfEdgeEnd clauseThree5 d = some (clauseThreeEmbedding.EN d)) ⟨d, hd⟩

theorem clauseThree_skeleton_planar : PlanarGraph clauseThree5 :=
  clauseThreeEmbedding_valid.planarGraph rfl (fun v => v) (fun _ _ h => h) clauseThreeEmbedding_ends

/-- Every designated port meets one common face of this embedding. -/
theorem clauseThree_skeleton_ports_cofacial :
    ∀ e ∈ clausePorts, ∃ d : Fin 48, ∃ i : Fin 48,
      iterate clauseThreeEmbedding.F i 1 = d ∧ clauseThree5[d.val / 2]? = some e := by
  decide

def clauseTwoEmbedding : Planar.EmbedTables where
  n2 := 34
  EN := fun d => [0, 1, 0, 12, 0, 13, 1, 2, 2, 3, 2, 14, 3, 4, 3, 10, 4, 5, 4, 15, 5, 6, 6, 7, 6, 16, 7, 8, 8, 9, 8, 17, 9, 10, 9, 15, 10, 11, 11, 12, 11, 14, 13, 14, 15, 16, 16, 17, 10, 18, 11, 20, 18, 19, 19, 20, 19, 22, 20, 21, 20, 23, 21, 22, 21, 23, 22, 23].getD d 0
  N := fun d => [4, 6, 0, 39, 2, 42, 1, 8, 10, 12, 7, 41, 14, 16, 9, 33, 18, 20, 13, 44, 17, 22, 24, 26, 21, 46, 23, 28, 30, 32, 27, 47, 34, 36, 29, 19, 48, 38, 40, 3, 50, 43, 5, 11, 35, 25, 45, 31, 15, 52, 37, 55, 49, 56, 53, 58, 54, 66, 60, 62, 51, 65, 64, 57, 59, 67, 63, 61].getD d 0
  F := fun d => [6, 2, 39, 4, 42, 0, 10, 1, 14, 7, 43, 8, 18, 9, 48, 12, 20, 13, 35, 16, 24, 17, 26, 21, 45, 22, 30, 23, 34, 27, 47, 28, 15, 29, 44, 32, 50, 33, 3, 37, 11, 38, 41, 5, 46, 19, 31, 25, 52, 36, 60, 40, 54, 49, 51, 56, 63, 53, 64, 55, 67, 58, 66, 59, 61, 62, 65, 57].getD d 0
  R := fun d => [0, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 1, 2, 2, 2, 0, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 0, 3, 0, 1, 0, 2, 1, 1, 0, 2, 0, 3, 0, 1, 2, 2, 1, 1, 2].getD d 0
  FL := fun d => [0, 1, 1, 3, 3, 0, 0, 1, 8, 1, 0, 8, 12, 1, 8, 12, 16, 1, 12, 16, 16, 1, 22, 1, 16, 22, 22, 1, 28, 1, 22, 28, 12, 1, 28, 12, 36, 1, 3, 1, 8, 3, 3, 0, 28, 16, 28, 22, 8, 36, 36, 8, 8, 36, 8, 55, 55, 36, 58, 55, 36, 58, 62, 55, 58, 62, 62, 36].getD d 0
  CL := fun d => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD d 0
  D := fun d => [0, 1, 1, 2, 2, 1, 2, 2, 4, 3, 3, 4, 5, 4, 4, 5, 6, 5, 5, 6, 6, 6, 8, 7, 7, 8, 8, 8, 8, 7, 9, 9, 6, 6, 8, 7, 5, 4, 3, 3, 4, 3, 2, 2, 8, 7, 8, 9, 6, 6, 5, 5, 7, 7, 6, 7, 7, 8, 7, 8, 6, 7, 9, 9, 8, 9, 9, 8].getD d 0
  SU := fun d => [0, 0, 0, 2, 2, 0, 1, 1, 10, 7, 7, 10, 14, 9, 9, 14, 18, 13, 13, 18, 17, 17, 24, 21, 21, 24, 23, 23, 29, 32, 27, 28, 15, 36, 29, 32, 37, 38, 3, 3, 41, 43, 5, 5, 35, 19, 45, 46, 15, 36, 37, 40, 49, 49, 51, 54, 54, 53, 60, 58, 51, 60, 64, 57, 61, 67, 67, 61].getD d 0
  cR := Planar.runCount (fun d => decide ([0, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 1, 2, 2, 2, 0, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 0, 3, 0, 1, 0, 2, 1, 1, 0, 2, 0, 3, 0, 1, 2, 2, 1, 1, 2].getD d 0 = 0))
  cF := Planar.runCount (fun d => decide ([0, 1, 1, 3, 3, 0, 0, 1, 8, 1, 0, 8, 12, 1, 8, 12, 16, 1, 12, 16, 16, 1, 22, 1, 16, 22, 22, 1, 28, 1, 22, 28, 12, 1, 28, 12, 36, 1, 3, 1, 8, 3, 3, 0, 28, 16, 28, 22, 8, 36, 36, 8, 8, 36, 8, 55, 55, 36, 58, 55, 36, 58, 62, 55, 58, 62, 62, 36].getD d 0 = d))
  cC := Planar.runCount (fun d => decide ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD d 0 = d))

theorem clauseTwoEmbedding_valid : Planar.EmbedOK clauseTwoEmbedding := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 68, clauseTwoEmbedding.N d < 68 ∧ clauseTwoEmbedding.F d < 68) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ h : Fin 34, clauseTwoEmbedding.N (clauseTwoEmbedding.F (2*h+1)) = 2*h ∧ clauseTwoEmbedding.N (clauseTwoEmbedding.F (2*h)) = 2*h+1) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 68, clauseTwoEmbedding.EN (clauseTwoEmbedding.N d) = clauseTwoEmbedding.EN d) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 68, clauseTwoEmbedding.R (clauseTwoEmbedding.N d) = clauseTwoEmbedding.R d+1 ∨ clauseTwoEmbedding.R (clauseTwoEmbedding.N d) = 0) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 68, clauseTwoEmbedding.R d < 68) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ h : Fin 34, (0 < clauseTwoEmbedding.R (2*h) → clauseTwoEmbedding.R (clauseTwoEmbedding.F (2*h+1))+1 = clauseTwoEmbedding.R (2*h)) ∧ (0 < clauseTwoEmbedding.R (2*h+1) → clauseTwoEmbedding.R (clauseTwoEmbedding.F (2*h))+1 = clauseTwoEmbedding.R (2*h+1))) ⟨d, hd⟩
  · intro d hd d' hd'
    exact (by decide : ∀ d d' : Fin 68, clauseTwoEmbedding.EN d = clauseTwoEmbedding.EN d' → clauseTwoEmbedding.R d = 0 → clauseTwoEmbedding.R d' = 0 → d.val = d'.val) ⟨d, hd⟩ ⟨d', hd'⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 68, clauseTwoEmbedding.FL d ≤ d ∧ clauseTwoEmbedding.FL (clauseTwoEmbedding.F d) = clauseTwoEmbedding.FL d) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 68, clauseTwoEmbedding.CL d ≤ d ∧ (clauseTwoEmbedding.D d = 0 ↔ clauseTwoEmbedding.CL d = d)) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 68, 0 < clauseTwoEmbedding.D d → clauseTwoEmbedding.SU d < 68 ∧ clauseTwoEmbedding.D (clauseTwoEmbedding.SU d)+1 = clauseTwoEmbedding.D d ∧ clauseTwoEmbedding.CL (clauseTwoEmbedding.SU d) = clauseTwoEmbedding.CL d ∧ (clauseTwoEmbedding.SU d = Planar.ed d ∨ clauseTwoEmbedding.SU d = clauseTwoEmbedding.N d ∨ clauseTwoEmbedding.SU d = clauseTwoEmbedding.F d)) ⟨d, hd⟩
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [clauseTwoEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [clauseTwoEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [clauseTwoEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · decide

theorem clauseTwoEmbedding_ends :
    ∀ d, d < 2 * clauseTwoEmbedding.n2 → halfEdgeEnd clauseTwoSkeleton d = some (clauseTwoEmbedding.EN d) := by
  intro d hd
  exact (by decide : ∀ d : Fin 68, halfEdgeEnd clauseTwoSkeleton d = some (clauseTwoEmbedding.EN d)) ⟨d, hd⟩

theorem clauseTwo_skeleton_planar : PlanarGraph clauseTwoSkeleton :=
  clauseTwoEmbedding_valid.planarGraph rfl (fun v => v) (fun _ _ h => h) clauseTwoEmbedding_ends

/-- Every designated port meets one common face of this embedding. -/
theorem clauseTwo_skeleton_ports_cofacial :
    ∀ e ∈ clausePorts.take 2, ∃ d : Fin 68, ∃ i : Fin 68,
      iterate clauseTwoEmbedding.F i 1 = d ∧ clauseTwoSkeleton[d.val / 2]? = some e := by
  decide

end STACS2027
