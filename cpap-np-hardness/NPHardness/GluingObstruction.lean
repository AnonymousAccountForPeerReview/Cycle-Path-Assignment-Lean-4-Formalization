module

public import NPHardness.OrientedGluing
public import NPHardness.PlanarFoundation

/-!
A concrete example for endpoint orientation. The source satisfies exactly
Definition 7 and has a registered planar incidence embedding. The fixed map
contains an explicit K3,3 subdivision. A suitable endpoint choice instead has
a registered planar embedding. These are finite kernel-checked certificates;
no Kuratowski theorem or general planar-gluing result is asserted here.
-/

@[expose] public section
namespace STACS2027
open Complexity Complexity.SAT
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def gluingObstructionFormula : CNF :=
  [[⟨0,false⟩,⟨1,false⟩], [⟨0,false⟩,⟨1,false⟩], [⟨0,true⟩,⟨1,true⟩]]

theorem gluingObstruction_bounded : BoundedOccurrence gluingObstructionFormula := by
  refine ⟨by decide, ?_, ?_⟩
  all_goals
    intro v
    cases v with
    | zero => decide
    | succ v =>
      cases v with
      | zero => decide
      | succ v => simp [occurrences, gluingObstructionFormula]

theorem gluingObstruction_distinct : ClauseVariablesDistinct gluingObstructionFormula := by
  unfold ClauseVariablesDistinct
  decide

def gluingRepairFlips (p : PlacedLiteral) : Bool := p.literal.var == 1

def gluingObstruction_incidenceEmbedding : Planar.EmbedTables where
  n2 := 6
  EN := fun d => [0, 1, 2, 1, 0, 3, 2, 3, 0, 5, 2, 5].getD d 0
  N := fun d => [8, 3, 6, 1, 0, 7, 10, 5, 4, 11, 2, 9].getD d 0
  F := fun d => [3, 4, 1, 10, 7, 8, 5, 2, 11, 0, 9, 6].getD d 0
  R := fun d => [0, 0, 0, 1, 2, 0, 1, 1, 1, 0, 2, 1].getD d 0
  FL := fun d => [0, 1, 1, 0, 1, 5, 5, 1, 5, 0, 0, 5].getD d 0
  CL := fun d => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD d 0
  D := fun d => [0, 1, 2, 2, 1, 2, 3, 3, 2, 1, 2, 2].getD d 0
  SU := fun d => [0, 0, 1, 1, 0, 4, 5, 2, 4, 0, 9, 9].getD d 0
  cR := Planar.runCount (fun d => decide ([0, 0, 0, 1, 2, 0, 1, 1, 1, 0, 2, 1].getD d 0 = 0))
  cF := Planar.runCount (fun d => decide ([0, 1, 1, 0, 1, 5, 5, 1, 5, 0, 0, 5].getD d 0 = d))
  cC := Planar.runCount (fun d => decide ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD d 0 = d))

theorem gluingObstruction_incidenceEmbedding_valid : Planar.EmbedOK gluingObstruction_incidenceEmbedding := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 12, gluingObstruction_incidenceEmbedding.N d < 12 ∧ gluingObstruction_incidenceEmbedding.F d < 12) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ h : Fin 6, gluingObstruction_incidenceEmbedding.N (gluingObstruction_incidenceEmbedding.F (2*h+1)) = 2*h ∧ gluingObstruction_incidenceEmbedding.N (gluingObstruction_incidenceEmbedding.F (2*h)) = 2*h+1) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 12, gluingObstruction_incidenceEmbedding.EN (gluingObstruction_incidenceEmbedding.N d) = gluingObstruction_incidenceEmbedding.EN d) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 12, gluingObstruction_incidenceEmbedding.R (gluingObstruction_incidenceEmbedding.N d) = gluingObstruction_incidenceEmbedding.R d+1 ∨ gluingObstruction_incidenceEmbedding.R (gluingObstruction_incidenceEmbedding.N d) = 0) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 12, gluingObstruction_incidenceEmbedding.R d < 12) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ h : Fin 6, (0 < gluingObstruction_incidenceEmbedding.R (2*h) → gluingObstruction_incidenceEmbedding.R (gluingObstruction_incidenceEmbedding.F (2*h+1))+1 = gluingObstruction_incidenceEmbedding.R (2*h)) ∧ (0 < gluingObstruction_incidenceEmbedding.R (2*h+1) → gluingObstruction_incidenceEmbedding.R (gluingObstruction_incidenceEmbedding.F (2*h))+1 = gluingObstruction_incidenceEmbedding.R (2*h+1))) ⟨d, hd⟩
  · have hroot : ∀ d : Fin 12, gluingObstruction_incidenceEmbedding.R d = 0 →
        d.val = [0, 1, 2, 5, 0, 9].getD (gluingObstruction_incidenceEmbedding.EN d) 0 := by decide
    intro d hd d' hd' he h0 h0'
    have h1 := hroot ⟨d,hd⟩ h0
    have h2 := hroot ⟨d',hd'⟩ h0'
    dsimp only at h1 h2
    rw [he] at h1
    exact h1.trans h2.symm
  · intro d hd
    exact (by decide : ∀ d : Fin 12, gluingObstruction_incidenceEmbedding.FL d ≤ d ∧ gluingObstruction_incidenceEmbedding.FL (gluingObstruction_incidenceEmbedding.F d) = gluingObstruction_incidenceEmbedding.FL d) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 12, gluingObstruction_incidenceEmbedding.CL d ≤ d ∧ (gluingObstruction_incidenceEmbedding.D d = 0 ↔ gluingObstruction_incidenceEmbedding.CL d = d)) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 12, 0 < gluingObstruction_incidenceEmbedding.D d → gluingObstruction_incidenceEmbedding.SU d < 12 ∧ gluingObstruction_incidenceEmbedding.D (gluingObstruction_incidenceEmbedding.SU d)+1 = gluingObstruction_incidenceEmbedding.D d ∧ gluingObstruction_incidenceEmbedding.CL (gluingObstruction_incidenceEmbedding.SU d) = gluingObstruction_incidenceEmbedding.CL d ∧ (gluingObstruction_incidenceEmbedding.SU d = Planar.ed d ∨ gluingObstruction_incidenceEmbedding.SU d = gluingObstruction_incidenceEmbedding.N d ∨ gluingObstruction_incidenceEmbedding.SU d = gluingObstruction_incidenceEmbedding.F d)) ⟨d, hd⟩
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [gluingObstruction_incidenceEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [gluingObstruction_incidenceEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [gluingObstruction_incidenceEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · decide

theorem gluingObstruction_incidenceEmbedding_ends :
    ∀ d, d < 2 * gluingObstruction_incidenceEmbedding.n2 → halfEdgeEnd (incidenceGraph gluingObstructionFormula) d = some (Planar.decodeEnd (gluingObstruction_incidenceEmbedding.EN d)) := by
  intro d hd
  exact (by decide : ∀ d : Fin 12, halfEdgeEnd (incidenceGraph gluingObstructionFormula) d = some (Planar.decodeEnd (gluingObstruction_incidenceEmbedding.EN d))) ⟨d, hd⟩

theorem gluingObstruction_incidence_planar : PlanarGraph (incidenceGraph gluingObstructionFormula) :=
  gluingObstruction_incidenceEmbedding_valid.planarGraph rfl Planar.decodeEnd (fun _ _ h => Planar.decodeEnd_injective h) gluingObstruction_incidenceEmbedding_ends

/-- A K3,3 subdivision certificate with six distinct branch vertices and
nine simple branch-to-branch paths. Path interiors avoid every branch vertex
and are disjoint for distinct pairs of branch indices. -/
structure K33Subdivision (g : Graph) where
  left : Fin 3 → Nat
  right : Fin 3 → Nat
  branches_nodup : ((List.finRange 3).map left ++ (List.finRange 3).map right).Nodup
  paths : Fin 3 → Fin 3 → List Nat
  paths_valid : ∀ i j, IsSimplePath g (left i) (right j) (paths i j)
  interior_avoids_branches : ∀ i j, ∀ v ∈ ((paths i j).drop 1).dropLast,
    v ∉ (List.finRange 3).map left ++ (List.finRange 3).map right
  interiors_disjoint : ∀ i j i' j', (i,j) ≠ (i',j') →
    ∀ v ∈ ((paths i j).drop 1).dropLast, v ∉ ((paths i' j').drop 1).dropLast

def gluingObstructionPaths (i j : Fin 3) : List Nat :=
  [[29, 53], [29, 28, 81, 91, 92, 83, 84, 85, 93, 94, 97, 96, 95, 86, 89, 77, 3, 4, 63, 64], [29, 65, 66], [52, 53], [52, 64], [52, 5, 6, 102, 114, 111, 120, 123, 122, 119, 118, 110, 109, 108, 117, 116, 106, 31, 30, 56, 66], [60, 53], [60, 68, 69, 72, 73, 70, 61, 64], [60, 59, 58, 67, 66]].getD (3*i.val+j.val) []

def fixedGluingK33Subdivision : K33Subdivision (formulaGraph 5 gluingObstructionFormula) where
  left := fun i => [29,52,60].getD i.val 0
  right := fun j => [53,64,66].getD j.val 0
  branches_nodup := by decide
  paths := gluingObstructionPaths
  paths_valid := by
    unfold IsSimplePath
    decide
  interior_avoids_branches := by decide
  interiors_disjoint := by decide

theorem fixed_gluing_contains_K33_subdivision :
    Nonempty (K33Subdivision (formulaGraph 5 gluingObstructionFormula)) :=
  ⟨fixedGluingK33Subdivision⟩

def gluingRepairEmbedding : Planar.EmbedTables where
  n2 := 120
  EN := fun d => [0, 7, 1, 7, 1, 2, 3, 4, 5, 6, 0, 3, 1, 4, 4, 5, 2, 6, 25, 32, 26, 32, 26, 27, 28, 29, 30, 31, 25, 28, 26, 29, 29, 30, 27, 31, 4, 5, 4, 62, 4, 63, 5, 52, 52, 53, 52, 64, 30, 53, 53, 60, 29, 30, 30, 65, 29, 56, 56, 57, 56, 66, 57, 58, 58, 59, 58, 67, 59, 60, 59, 65, 60, 61, 61, 62, 61, 64, 63, 64, 65, 66, 66, 67, 60, 68, 61, 70, 68, 69, 69, 70, 69, 72, 70, 71, 70, 73, 71, 72, 71, 73, 72, 73, 0, 3, 0, 87, 0, 88, 3, 77, 77, 78, 77, 89, 28, 78, 78, 85, 25, 28, 28, 90, 25, 81, 81, 82, 81, 91, 82, 83, 83, 84, 83, 92, 84, 85, 84, 90, 85, 86, 86, 87, 86, 89, 88, 89, 90, 91, 91, 92, 85, 93, 86, 95, 93, 94, 94, 95, 94, 97, 95, 96, 95, 98, 96, 97, 96, 98, 97, 98, 2, 6, 2, 112, 2, 113, 6, 102, 102, 103, 102, 114, 31, 103, 103, 110, 27, 31, 31, 115, 27, 106, 106, 107, 106, 116, 107, 108, 108, 109, 108, 117, 109, 110, 109, 115, 110, 111, 111, 112, 111, 114, 113, 114, 115, 116, 116, 117, 110, 118, 111, 120, 118, 119, 119, 120, 119, 122, 120, 121, 120, 123, 121, 122, 121, 123, 122, 123].getD d 0
  N := fun d => [10, 3, 4, 1, 12, 174, 110, 13, 42, 173, 104, 6, 2, 14, 36, 8, 172, 178, 124, 21, 30, 19, 20, 34, 121, 56, 53, 184, 120, 122, 22, 25, 52, 54, 188, 27, 40, 15, 7, 75, 38, 78, 37, 44, 46, 49, 43, 77, 26, 50, 45, 69, 31, 33, 48, 80, 32, 58, 60, 62, 57, 82, 59, 64, 66, 68, 63, 83, 70, 84, 65, 55, 51, 86, 76, 39, 73, 79, 41, 47, 71, 61, 81, 67, 72, 88, 74, 91, 85, 92, 89, 96, 90, 99, 87, 100, 94, 103, 95, 102, 98, 97, 93, 101, 108, 11, 0, 143, 106, 146, 105, 112, 114, 117, 111, 145, 24, 118, 113, 137, 18, 29, 116, 148, 28, 126, 128, 130, 125, 150, 127, 132, 134, 136, 131, 151, 138, 140, 133, 123, 152, 142, 144, 107, 154, 147, 109, 115, 139, 129, 149, 135, 119, 156, 141, 159, 153, 160, 157, 162, 158, 170, 164, 166, 155, 169, 168, 161, 163, 171, 167, 165, 5, 17, 176, 211, 16, 214, 9, 182, 179, 186, 180, 215, 190, 181, 185, 220, 192, 35, 189, 207, 23, 196, 193, 198, 194, 217, 195, 202, 199, 206, 200, 219, 201, 187, 204, 216, 205, 222, 209, 175, 210, 183, 177, 213, 191, 218, 197, 203, 208, 224, 212, 230, 221, 226, 228, 223, 225, 238, 232, 234, 227, 237, 236, 229, 231, 239, 235, 233].getD d 0
  F := fun d => [3, 106, 1, 12, 172, 2, 38, 11, 178, 15, 105, 0, 7, 4, 37, 13, 173, 176, 21, 120, 19, 22, 192, 30, 31, 116, 35, 48, 121, 124, 52, 20, 53, 56, 189, 23, 42, 14, 75, 40, 78, 36, 46, 8, 50, 43, 79, 44, 45, 54, 72, 49, 26, 32, 71, 33, 60, 25, 62, 57, 81, 58, 66, 59, 70, 63, 83, 64, 51, 65, 80, 68, 76, 84, 39, 86, 47, 74, 77, 41, 82, 55, 67, 61, 88, 69, 94, 73, 90, 85, 87, 92, 102, 89, 98, 96, 101, 91, 93, 100, 103, 95, 97, 99, 110, 10, 143, 108, 146, 104, 114, 6, 118, 111, 147, 112, 113, 122, 152, 117, 24, 28, 139, 29, 128, 18, 130, 125, 149, 126, 134, 127, 138, 131, 151, 132, 119, 133, 148, 136, 154, 137, 107, 141, 115, 142, 145, 109, 150, 123, 135, 129, 156, 140, 164, 144, 158, 153, 155, 160, 167, 157, 168, 159, 171, 162, 170, 163, 165, 166, 169, 161, 9, 16, 211, 5, 214, 174, 180, 17, 185, 182, 213, 179, 186, 27, 205, 181, 190, 34, 216, 184, 194, 188, 198, 196, 218, 193, 200, 195, 204, 202, 219, 199, 208, 206, 191, 201, 210, 220, 175, 212, 215, 222, 183, 177, 197, 207, 203, 217, 224, 187, 227, 209, 228, 221, 232, 225, 235, 226, 236, 223, 239, 230, 238, 231, 233, 234, 237, 229].getD d 0
  R := fun d => [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 3, 2, 1, 2, 3, 3, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 2, 1, 4, 2, 2, 1, 4, 3, 2, 5, 0, 4, 0, 1, 0, 1, 0, 2, 0, 4, 1, 2, 0, 3, 1, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 1, 2, 2, 3, 0, 2, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 0, 1, 0, 1, 0, 2, 1, 1, 0, 3, 0, 2, 0, 2, 1, 1, 2, 2, 1, 2, 2, 4, 0, 3, 0, 1, 0, 1, 0, 2, 0, 4, 1, 2, 0, 3, 1, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 1, 2, 2, 2, 0, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 0, 3, 0, 1, 0, 2, 1, 1, 0, 2, 0, 3, 0, 1, 2, 2, 1, 1, 2, 4, 1, 1, 0, 2, 0, 3, 0, 2, 0, 1, 0, 1, 2, 1, 0, 2, 3, 2, 0, 3, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 3, 1, 1, 2, 0, 3, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 0, 1, 0, 1, 0, 1, 3, 2, 0, 1, 0, 2, 0, 1, 2, 2, 1, 1, 2].getD d 0
  FL := fun d => [0, 1, 1, 0, 4, 1, 6, 0, 8, 4, 10, 0, 0, 4, 14, 4, 16, 17, 1, 19, 19, 1, 1, 23, 19, 6, 23, 8, 28, 29, 23, 19, 32, 33, 34, 23, 36, 14, 6, 39, 39, 36, 36, 8, 44, 8, 36, 44, 8, 49, 44, 49, 23, 32, 49, 33, 33, 6, 58, 6, 33, 58, 58, 6, 64, 6, 58, 64, 49, 6, 64, 49, 44, 73, 39, 6, 44, 39, 39, 36, 64, 33, 64, 58, 73, 6, 6, 73, 73, 6, 73, 91, 91, 6, 6, 95, 95, 91, 6, 99, 99, 95, 91, 99, 104, 10, 1, 107, 107, 104, 104, 6, 112, 6, 104, 112, 6, 117, 112, 117, 19, 28, 117, 29, 29, 1, 126, 1, 29, 126, 126, 1, 132, 1, 126, 132, 117, 1, 132, 117, 140, 1, 107, 1, 112, 107, 107, 104, 132, 29, 132, 126, 112, 140, 140, 112, 112, 140, 112, 159, 159, 140, 162, 159, 140, 162, 166, 159, 162, 166, 166, 140, 4, 16, 174, 1, 17, 174, 8, 17, 8, 181, 181, 17, 184, 8, 184, 181, 188, 34, 188, 184, 1, 188, 1, 195, 195, 188, 1, 195, 1, 201, 201, 195, 1, 184, 184, 201, 1, 209, 1, 174, 174, 181, 17, 174, 188, 201, 195, 201, 209, 181, 181, 209, 209, 181, 226, 181, 209, 226, 230, 209, 226, 230, 234, 209, 230, 234, 234, 226].getD d 0
  CL := fun d => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD d 0
  D := fun d => [0, 1, 2, 2, 4, 3, 3, 2, 7, 6, 2, 1, 3, 4, 6, 5, 5, 6, 11, 10, 10, 11, 11, 10, 8, 7, 11, 11, 9, 8, 9, 8, 10, 10, 12, 11, 5, 6, 3, 4, 4, 5, 7, 8, 8, 9, 7, 7, 10, 10, 9, 10, 9, 10, 11, 11, 9, 8, 10, 9, 9, 10, 10, 10, 12, 11, 11, 12, 11, 10, 12, 12, 8, 7, 5, 5, 7, 6, 6, 6, 12, 11, 12, 11, 9, 10, 6, 7, 9, 10, 8, 9, 9, 10, 8, 9, 9, 10, 10, 11, 11, 10, 11, 11, 3, 2, 1, 2, 2, 3, 3, 4, 6, 5, 5, 5, 6, 7, 6, 7, 9, 9, 7, 8, 10, 11, 11, 12, 10, 11, 11, 10, 9, 8, 11, 10, 7, 6, 9, 8, 5, 4, 3, 3, 5, 4, 4, 4, 9, 9, 10, 11, 7, 6, 5, 6, 7, 7, 7, 8, 8, 8, 8, 9, 7, 8, 10, 9, 9, 10, 10, 9, 4, 5, 5, 4, 6, 6, 7, 7, 8, 9, 8, 8, 10, 10, 9, 8, 12, 12, 11, 10, 11, 12, 10, 10, 11, 11, 9, 10, 8, 9, 9, 10, 7, 8, 8, 9, 6, 7, 5, 5, 6, 7, 7, 7, 11, 10, 11, 11, 7, 8, 7, 8, 9, 9, 10, 9, 10, 11, 10, 9, 10, 11, 11, 10, 10, 11, 11, 12].getD d 0
  SU := fun d => [0, 0, 1, 1, 12, 2, 7, 11, 9, 15, 11, 0, 2, 12, 15, 13, 172, 16, 124, 120, 30, 19, 20, 30, 25, 116, 53, 48, 29, 122, 31, 25, 52, 56, 35, 23, 40, 15, 7, 38, 38, 40, 37, 42, 46, 43, 79, 77, 45, 50, 72, 50, 31, 52, 48, 33, 57, 25, 60, 57, 57, 60, 59, 59, 66, 63, 63, 83, 69, 84, 65, 55, 73, 86, 39, 39, 77, 74, 41, 41, 81, 61, 81, 61, 72, 88, 74, 86, 90, 92, 87, 90, 90, 92, 87, 94, 94, 96, 95, 98, 98, 95, 97, 101, 108, 11, 0, 106, 106, 108, 105, 110, 114, 111, 147, 145, 113, 118, 113, 137, 24, 29, 116, 122, 28, 124, 128, 130, 149, 150, 131, 132, 133, 136, 131, 132, 137, 140, 133, 136, 141, 142, 107, 107, 145, 142, 109, 109, 139, 123, 149, 135, 153, 140, 141, 154, 153, 153, 155, 158, 158, 157, 164, 162, 155, 164, 167, 161, 165, 171, 167, 161, 5, 172, 175, 5, 16, 174, 9, 17, 179, 180, 213, 179, 186, 181, 187, 220, 190, 35, 191, 207, 194, 196, 198, 198, 194, 217, 200, 202, 204, 206, 200, 202, 208, 204, 204, 206, 210, 208, 175, 175, 210, 212, 177, 177, 191, 207, 203, 217, 208, 220, 212, 222, 221, 221, 227, 223, 225, 226, 231, 223, 227, 232, 236, 231, 231, 236, 235, 229].getD d 0
  cR := Planar.runCount (fun d => decide ([0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 3, 2, 1, 2, 3, 3, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 2, 1, 4, 2, 2, 1, 4, 3, 2, 5, 0, 4, 0, 1, 0, 1, 0, 2, 0, 4, 1, 2, 0, 3, 1, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 1, 2, 2, 3, 0, 2, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 0, 1, 0, 1, 0, 2, 1, 1, 0, 3, 0, 2, 0, 2, 1, 1, 2, 2, 1, 2, 2, 4, 0, 3, 0, 1, 0, 1, 0, 2, 0, 4, 1, 2, 0, 3, 1, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 1, 2, 2, 2, 0, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 0, 3, 0, 1, 0, 2, 1, 1, 0, 2, 0, 3, 0, 1, 2, 2, 1, 1, 2, 4, 1, 1, 0, 2, 0, 3, 0, 2, 0, 1, 0, 1, 2, 1, 0, 2, 3, 2, 0, 3, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 3, 1, 1, 2, 0, 3, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 0, 1, 0, 1, 0, 1, 3, 2, 0, 1, 0, 2, 0, 1, 2, 2, 1, 1, 2].getD d 0 = 0))
  cF := Planar.runCount (fun d => decide ([0, 1, 1, 0, 4, 1, 6, 0, 8, 4, 10, 0, 0, 4, 14, 4, 16, 17, 1, 19, 19, 1, 1, 23, 19, 6, 23, 8, 28, 29, 23, 19, 32, 33, 34, 23, 36, 14, 6, 39, 39, 36, 36, 8, 44, 8, 36, 44, 8, 49, 44, 49, 23, 32, 49, 33, 33, 6, 58, 6, 33, 58, 58, 6, 64, 6, 58, 64, 49, 6, 64, 49, 44, 73, 39, 6, 44, 39, 39, 36, 64, 33, 64, 58, 73, 6, 6, 73, 73, 6, 73, 91, 91, 6, 6, 95, 95, 91, 6, 99, 99, 95, 91, 99, 104, 10, 1, 107, 107, 104, 104, 6, 112, 6, 104, 112, 6, 117, 112, 117, 19, 28, 117, 29, 29, 1, 126, 1, 29, 126, 126, 1, 132, 1, 126, 132, 117, 1, 132, 117, 140, 1, 107, 1, 112, 107, 107, 104, 132, 29, 132, 126, 112, 140, 140, 112, 112, 140, 112, 159, 159, 140, 162, 159, 140, 162, 166, 159, 162, 166, 166, 140, 4, 16, 174, 1, 17, 174, 8, 17, 8, 181, 181, 17, 184, 8, 184, 181, 188, 34, 188, 184, 1, 188, 1, 195, 195, 188, 1, 195, 1, 201, 201, 195, 1, 184, 184, 201, 1, 209, 1, 174, 174, 181, 17, 174, 188, 201, 195, 201, 209, 181, 181, 209, 209, 181, 226, 181, 209, 226, 230, 209, 226, 230, 234, 209, 230, 234, 234, 226].getD d 0 = d))
  cC := Planar.runCount (fun d => decide ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD d 0 = d))

theorem gluingRepairEmbedding_valid : Planar.EmbedOK gluingRepairEmbedding := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 240, gluingRepairEmbedding.N d < 240 ∧ gluingRepairEmbedding.F d < 240) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ h : Fin 120, gluingRepairEmbedding.N (gluingRepairEmbedding.F (2*h+1)) = 2*h ∧ gluingRepairEmbedding.N (gluingRepairEmbedding.F (2*h)) = 2*h+1) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 240, gluingRepairEmbedding.EN (gluingRepairEmbedding.N d) = gluingRepairEmbedding.EN d) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 240, gluingRepairEmbedding.R (gluingRepairEmbedding.N d) = gluingRepairEmbedding.R d+1 ∨ gluingRepairEmbedding.R (gluingRepairEmbedding.N d) = 0) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 240, gluingRepairEmbedding.R d < 240) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ h : Fin 120, (0 < gluingRepairEmbedding.R (2*h) → gluingRepairEmbedding.R (gluingRepairEmbedding.F (2*h+1))+1 = gluingRepairEmbedding.R (2*h)) ∧ (0 < gluingRepairEmbedding.R (2*h+1) → gluingRepairEmbedding.R (gluingRepairEmbedding.F (2*h))+1 = gluingRepairEmbedding.R (2*h+1))) ⟨d, hd⟩
  · have hroot : ∀ d : Fin 240, gluingRepairEmbedding.R d = 0 →
        d.val = [0, 2, 5, 6, 7, 8, 9, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 20, 23, 24, 25, 26, 27, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43, 45, 0, 0, 57, 59, 63, 65, 51, 73, 39, 41, 47, 55, 61, 67, 85, 89, 87, 95, 93, 97, 0, 0, 0, 111, 113, 0, 0, 125, 127, 131, 133, 119, 141, 107, 109, 115, 123, 129, 135, 153, 157, 155, 163, 161, 165, 0, 0, 0, 179, 181, 0, 0, 193, 195, 199, 201, 187, 209, 175, 177, 183, 191, 197, 203, 221, 225, 223, 231, 229, 233].getD (gluingRepairEmbedding.EN d) 0 := by decide
    intro d hd d' hd' he h0 h0'
    have h1 := hroot ⟨d,hd⟩ h0
    have h2 := hroot ⟨d',hd'⟩ h0'
    dsimp only at h1 h2
    rw [he] at h1
    exact h1.trans h2.symm
  · intro d hd
    exact (by decide : ∀ d : Fin 240, gluingRepairEmbedding.FL d ≤ d ∧ gluingRepairEmbedding.FL (gluingRepairEmbedding.F d) = gluingRepairEmbedding.FL d) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 240, gluingRepairEmbedding.CL d ≤ d ∧ (gluingRepairEmbedding.D d = 0 ↔ gluingRepairEmbedding.CL d = d)) ⟨d, hd⟩
  · intro d hd
    exact (by decide : ∀ d : Fin 240, 0 < gluingRepairEmbedding.D d → gluingRepairEmbedding.SU d < 240 ∧ gluingRepairEmbedding.D (gluingRepairEmbedding.SU d)+1 = gluingRepairEmbedding.D d ∧ gluingRepairEmbedding.CL (gluingRepairEmbedding.SU d) = gluingRepairEmbedding.CL d ∧ (gluingRepairEmbedding.SU d = Planar.ed d ∨ gluingRepairEmbedding.SU d = gluingRepairEmbedding.N d ∨ gluingRepairEmbedding.SU d = gluingRepairEmbedding.F d)) ⟨d, hd⟩
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [gluingRepairEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [gluingRepairEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · refine ⟨rfl, ?_⟩
    intro d _
    simp only [gluingRepairEmbedding, Planar.runCount_succ, decide_eq_true_eq]
    rfl
  · decide

theorem gluingRepairEmbedding_ends :
    ∀ d, d < 2 * gluingRepairEmbedding.n2 → halfEdgeEnd (orientedFormulaGraph gluingRepairFlips 5 gluingObstructionFormula) d = some (id (gluingRepairEmbedding.EN d)) := by
  intro d hd
  exact (by decide : ∀ d : Fin 240, halfEdgeEnd (orientedFormulaGraph gluingRepairFlips 5 gluingObstructionFormula) d = some (id (gluingRepairEmbedding.EN d))) ⟨d, hd⟩

theorem gluingRepair_planar : PlanarGraph (orientedFormulaGraph gluingRepairFlips 5 gluingObstructionFormula) :=
  gluingRepairEmbedding_valid.planarGraph rfl id (fun _ _ h => h) gluingRepairEmbedding_ends

end STACS2027
