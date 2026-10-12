module

public import ApproximationHardness.Embed.EmbedSpec
public import ApproximationHardness.RAM.Program
public import ApproximationHardness.RAM.Bounded
import Lean.Elab.Tactic.Omega

/-!
# A computed planar rotation from the formula alone

The depth-first search and the constraint solver are total Lean functions. This module
constructs their merge records by finite list traversal, discharges the record hypotheses of
the orientation pass, and obtains a planar rotation without an embedding supplied as input.
The list implementation is a semantic construction. The uniform linear-time and linear-space
RAM construction is proved separately in `PlanarEmbeddingRAM`.
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.SAT Complexity.Planar STACS2027.PlanarAssembly

/-- A finite log entry contains a consuming node, a group, and its flip bit. -/
abbrev MergeEntry := Nat × (Nat × Bool)

/-- Search a finite merge log for a group. -/
def selectMerge : List MergeEntry → Nat → Option (Nat × Bool)
  | [], _ => none
  | (v, x) :: rest, g => if x.1 = g then some (v, x.2) else selectMerge rest g

/-- A successful search identifies an actual entry of the log. -/
theorem selectMerge_mem : ∀ (log : List MergeEntry) (g v : Nat) (b : Bool),
    selectMerge log g = some (v, b) → (v, (g, b)) ∈ log
  | [], _, _, _, h => by simp [selectMerge] at h
  | (w, (a, c)) :: rest, g, v, b, h => by
    by_cases ha : a = g
    · simp only [selectMerge, ha, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst ha
      exact List.mem_cons_self ..
    · simp only [selectMerge, ha, ite_false] at h
      exact List.mem_cons_of_mem _ (selectMerge_mem rest g v b h)

/-- When a group has a unique log entry, the search returns that entry. -/
theorem selectMerge_of_mem : ∀ (log : List MergeEntry) (v g : Nat) (b : Bool),
    (v, (g, b)) ∈ log →
    (∀ w a c, (w, (a, c)) ∈ log → a = g → w = v ∧ c = b) →
    selectMerge log g = some (v, b)
  | [], _, _, _, h, _ => by simp at h
  | (w, (a, c)) :: rest, v, g, b, h, hu => by
    by_cases ha : a = g
    · obtain ⟨rfl, rfl⟩ := hu w a c (List.mem_cons_self ..) ha
      simp [selectMerge, ha]
    · rw [selectMerge, ite_eq_right ha]
      apply selectMerge_of_mem rest v g b
      · rcases List.mem_cons.mp h with h | h
        · cases h; exact absurd rfl ha
        · exact h
      · intro w' a' c' hm he
        exact hu w' a' c' (List.mem_cons_of_mem _ hm) he

namespace ForestData

variable {F : ForestData} (hF : F.Valid)

/-- All merges of the solver, in the given node order. -/
def mergeLog (post : List Nat) : List MergeEntry :=
  post.flatMap fun v => ((F.sol hF).consAt v).map fun x => (v, x)

theorem mem_mergeLog {post : List Nat} {v g : Nat} {b : Bool} :
    (v, (g, b)) ∈ mergeLog hF post ↔ v ∈ post ∧ (g, b) ∈ (F.sol hF).consAt v := by
  simp only [mergeLog, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨w, hw, x, hx, he⟩
    cases he
    exact ⟨hw, hx⟩
  · rintro ⟨hv, hx⟩
    exact ⟨v, hv, (g, b), hx, rfl⟩

/-- The parent-array value obtained by finite search of the merge log. -/
def mergeParents (post : List Nat) (g : Nat) : Nat :=
  match selectMerge (mergeLog hF post) g with
  | none => 0
  | some (v, _) => F.gid v + 1

/-- The flip-array value obtained by finite search of the merge log. -/
def mergeFlips (post : List Nat) (g : Nat) : Nat :=
  match selectMerge (mergeLog hF post) g with
  | none => 0
  | some (_, b) => if b then 1 else 0

/-- The finite searches supply all record hypotheses of the orientation pass. -/
theorem merge_records {post : List Nat} (hP : PostOrder F hF post) :
    Records F hF (mergeParents hF post) (mergeFlips hF post) := by
  have selected : ∀ v x, x ∈ (F.sol hF).consAt v →
      selectMerge (mergeLog hF post) x.1 = some (v, x.2) := by
    intro v x hx
    apply selectMerge_of_mem
    · exact (mem_mergeLog hF).mpr ⟨hP.mem v x hx, hx⟩
    · intro w a b hm he
      obtain ⟨_, hw⟩ := (mem_mergeLog hF).mp hm
      obtain ⟨hvw, hxb⟩ := (tree hF).consumed_unique (good hF) hw hx he
      exact ⟨hvw, congrArg Prod.snd hxb⟩
  refine ⟨?_, ?_, ?_⟩
  · intro v x hx
    unfold mergeParents
    rw [selected v x hx]
  · intro v x hx
    unfold mergeFlips
    rw [selected v x hx]
  · intro g hg
    unfold mergeParents at hg
    cases hs : selectMerge (mergeLog hF post) g with
    | none => simp [hs] at hg
    | some row =>
      obtain ⟨v, b⟩ := row
      have hm := selectMerge_mem _ g v b hs
      exact ⟨v, (g, b), ((mem_mergeLog hF).mp hm).2, rfl⟩

end ForestData

/-- Compute the group orientation by search, solver records, and the orientation pass. -/
def computedOrientation {f : CNF} (hf : BoundedOccurrence f) : Nat → Bool :=
  let hF := incF_valid hf
  let post := (incDG f).final.post
  ForestData.orient (incF f) post (ForestData.mergeParents hF post)
    (ForestData.mergeFlips hF post)

theorem computedOrientation_consistent {f : CNF} (hf : BoundedOccurrence f) :
    ((incF f).sol (incF_valid hf)).Consistent (computedOrientation hf) := by
  apply ForestData.orient_consistent
  · exact ForestData.merge_records (incF_valid hf) (DG.postOrder_final (incOk hf))
  · exact DG.postOrder_final (incOk hf)

/-- The planar rotation computed from the formula, with no input embedding. -/
def computedRotation {f : CNF} (hf : BoundedOccurrence f) : List Nat :=
  rotOut hf (computedOrientation hf)

/-- Every bounded-occurrence planar incidence graph receives a computed planar rotation. -/
theorem computedRotation_planar {f : CNF} (hf : BoundedOccurrence f)
    (hp : PlanarGraph (incidenceGraph f)) : IsPlanarRotation f (computedRotation hf) :=
  rotOut_planar hf hp (computedOrientation_consistent hf)

/-- Endpoint choices computed entirely from the formula. -/
def computedChoices {f : CNF} (hf : BoundedOccurrence f) : EndpointChoices :=
  choicesOfBits f (orientationBits f fun d => (computedRotation hf).getD d 0)

/-- The computed endpoint choices give a planar gadget graph whenever the formula is planar. -/
theorem computedChoices_planar (k : Nat) {f : CNF} (hf : BoundedOccurrence f)
    (hp : PlanarGraph (incidenceGraph f)) :
    PlanarGraph (orientedFormulaGraph (computedChoices hf) k f) :=
  orientationBits_planar k hf (computedRotation_planar hf hp)

/-- The planar reduction graph and its satisfiability equivalence, for one graph computed
from the formula alone. No planar rotation is supplied to this construction. -/
theorem computed_reduction_planar {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f)
    (hp : PlanarGraph (incidenceGraph f)) :
    PlanarGraph (orientedFormulaGraph (computedChoices hf) k f) ∧
      (Satisfiable f ↔ HasAssignment (orientedFormulaGraph (computedChoices hf) k f) k f.length) :=
  ⟨computedChoices_planar k hf hp,
    orientedFormulaGraph_sat_iff_assignment (computedChoices hf) hk hf hd⟩

/-- A uniform RAM program computes a planar rotation from a formula alone in linear time
and space. The witness is proved in `PlanarEmbeddingRAM.planarEmbedding_linear_ram`. -/
def PlanarEmbeddingLinearRAM : Prop :=
  ∃ (prog : RAM.Stmt) (C : Nat), ∀ f : CNF, BoundedOccurrence f →
    PlanarGraph (incidenceGraph f) → ∃ (rot : List Nat) (t : Nat),
      RAM.ComputesIn prog (RAM.ramInput f) rot t
        (C * ((RAM.ramInput f).length + variableBound f + 1)) ∧
      t ≤ C * ((RAM.ramInput f).length + variableBound f + 1) ∧ IsPlanarRotation f rot

end STACS2027.Embed
