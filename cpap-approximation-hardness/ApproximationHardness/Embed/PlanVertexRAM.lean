module

public import ApproximationHardness.Embed.PlanStoreRAM
public import ApproximationHardness.RAM.Pass
import Lean.Elab.Tactic.Omega

/-! Actual finite-loop construction of the vertex and top-node plan tables. -/

@[expose] public section

namespace STACS2027.Embed.PlanRAM

open RAM

abbrev exclusion := 303
abbrev representative := 304
abbrev constant := 305

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest exclusion representative constant

/-- Test one adjacency dart for being a forest dart; remember each encountered back dart. -/
def distinguishedSlot (k : Nat) : Stmt := seqs [readForest dart (3+k) vertex, cachedItem,
  .ifz itemType .skip (seqs [.sub test dart vertexParent, .sub otherTest vertexParent dart,
    .add test test otherTest, .ifz test .skip (.add distinguished dart 0)])]

/-- Compute the distinguished dart from exactly three cached adjacency slots. -/
def distinguishedProgram : Stmt := seqs [readForest degree 2 vertex,
  readForest vertexParent 6 vertex, .const constant 3,
  .sub test degree constant, .sub otherTest constant degree, .add test test otherTest,
  .ifz test (seqs [readForest distinguished 5 vertex,
    distinguishedSlot 0, distinguishedSlot 1, distinguishedSlot 2])
    (.add distinguished DFSRAM.dartCount 0), zStore vertex distinguished]

/-- Initialize the five parts-table cells of one node to the empty-list defaults. -/
def clearParts (index : Nat) : Stmt := seqs [planStore 16 index 0, planStore 17 index 0,
  planStore 18 index 0, planStore 19 index 0, planStore 20 index 0]

/-- Commit the next retained item into the first or second slot. -/
def retainItem : Stmt := seqs [.ifz partCount
  (seqs [planStore 17 vertex itemType, planStore 18 vertex itemValue])
  (seqs [planStore 19 vertex itemType, planStore 20 vertex itemValue]),
  .add partCount partCount 1]

/-- Retain one valid adjacency slot exactly when it is not the excluded dart. -/
def partSlot (k : Nat) : Stmt := seqs [.const constant k, .sub test degree constant,
  .ifz test .skip (seqs [readForest dart (3+k) vertex,
    .sub test dart exclusion, .sub otherTest exclusion dart, .add test test otherTest,
    .ifz test .skip (seqs [cachedItem, retainItem])])]

/-- Construct the ordinary vertex's at-most-two ordered parts. -/
def ordinaryParts : Stmt := seqs [clearParts vertex, .const partCount 0,
  .sub test DFSRAM.dartCount vertexParent,
  .ifz test (.add exclusion distinguished 0) (.add exclusion vertexParent 0),
  partSlot 0, partSlot 1, partSlot 2, planStore 16 vertex partCount]

/-- Construct the top node of a root from its root item and optional distinguished item. -/
def topParts : Stmt := seqs [clearParts topVertex,
  .sub test DFSRAM.dartCount vertexParent,
  .ifz test (seqs [.const itemType 0, .add itemValue vertex 0,
    planStore 17 topVertex itemType, planStore 18 topVertex itemValue,
    .const partCount 1, .sub test DFSRAM.dartCount distinguished,
    .ifz test .skip (seqs [.add dart distinguished 0, cachedItem,
      planStore 19 topVertex itemType, planStore 20 topVertex itemValue, .const partCount 2]),
    planStore 16 topVertex partCount]) .skip]

/-- One vertex iteration writes its distinguished entry, ordinary node, and synthetic top. -/
def vertexTableStep : Stmt := seqs [distinguishedProgram,
  .add topVertex DFSRAM.dartCount vertex,
  .add itemValue vertexBound vertex, planStore 15 vertex itemValue,
  .add itemValue vertexBound topVertex, planStore 15 topVertex itemValue,
  clearParts vertex, clearParts topVertex,
  readForest representative 0 vertex, .sub test representative vertex,
  .sub otherTest vertex representative, .add test test otherTest,
  .ifz test (seqs [ordinaryParts, topParts]) .skip]

/-- The loop body advances exactly one of the bounded dart-indexed vertex positions. -/
def vertexTableBody : Stmt := seqs [vertexTableStep, .add vertex vertex 1,
  .sub remaining remaining 1]

/-- Build both halves of the vertex-plan tables by a fixed-length scan. -/
def vertexTablesProgram : Stmt := seqs [.const vertex 0,
  .add remaining DFSRAM.dartCount 0, .loop remaining vertexTableBody]

theorem distinguishedSlot_loopFree (k : Nat) : LoopFree (distinguishedSlot k) := by
  simp [distinguishedSlot, cachedItem_loopFree, readForest, seqs, LoopFree]

theorem vertexTableStep_loopFree : LoopFree vertexTableStep := by
  simp [vertexTableStep, distinguishedProgram, distinguishedSlot, cachedItem,
    ordinaryParts, topParts, clearParts, partSlot, retainItem, planStore, zStore,
    readForest, seqs, LoopFree]

theorem vertexTableStep_size : size vertexTableStep ≤ 1000 := by decide

theorem vertexTableStep_out (c : Config) : (run vertexTableStep c).out = c.out :=
  run_out_frame _ _ (by decide)

theorem vertexTableStep_reg_frame (c : Config) (r : Nat) (hr : r < 281 ∨ 305 < r) :
    (run vertexTableStep c).reg r = c.reg r := by
  apply run_reg_frame
  have hw : (regsW vertexTableStep).all (fun r => decide (281 ≤ r ∧ r ≤ 305)) = true := by decide
  intro hn
  have := of_decide_eq_true ((List.all_eq_true.mp hw) r hn)
  omega

end STACS2027.Embed.PlanRAM
