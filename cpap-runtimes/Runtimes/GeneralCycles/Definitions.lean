module

public import Runtimes.C4.Canon

/-!
# Endpoint-index enumeration of arbitrary fixed-length cycles

Vertex labels are values, never addresses. Tuples are ordered first by their
vertex lists, then by their endpoint-index lists. The secondary comparison
selects exactly one index representation even when an input endpoint repeats.
Artifact date: 2026-10-12.
-/

@[expose] public section

namespace STACS2027.Runtimes.GeneralCycles

open STACS2027

def endpoints (g : Graph) : List ℕ := g.flatMap fun e => [e.1, e.2]

def tuples (N : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (List.range N).flatMap fun i => (tuples N k).map (i :: ·)

def tupleLabels (g : Graph) (indices : List ℕ) : Cycle :=
  indices.map fun i => (endpoints g).getD i 0

def Valid (g : Graph) (k : ℕ) (indices : List ℕ) : Prop :=
  IsCycle g k (tupleLabels g indices)

def Earlier (g : Graph) (indices previous : List ℕ) : Prop :=
  tupleLabels g previous < tupleLabels g indices ∨
    (tupleLabels g previous = tupleLabels g indices ∧ previous < indices)

instance (g : Graph) (k : ℕ) (indices : List ℕ) : Decidable (Valid g k indices) :=
  inferInstanceAs (Decidable (IsCycle g k (tupleLabels g indices)))

instance (g : Graph) (indices previous : List ℕ) : Decidable (Earlier g indices previous) := by
  unfold Earlier
  infer_instance

def Accepted (g : Graph) (k : ℕ) (indices : List ℕ) : Prop :=
  Valid g k indices ∧ ∀ previous ∈ tuples (endpoints g).length k,
    Valid g k previous → SameCycle (tupleLabels g previous) (tupleLabels g indices) →
      ¬ Earlier g indices previous

instance (g : Graph) (k : ℕ) (indices : List ℕ) : Decidable (Accepted g k indices) := by
  unfold Accepted
  infer_instance

def outputCycles (g : Graph) (k : ℕ) : List Cycle :=
  ((tuples (endpoints g).length k).filter fun indices => decide (Accepted g k indices)).map
    (tupleLabels g)

end STACS2027.Runtimes.GeneralCycles
