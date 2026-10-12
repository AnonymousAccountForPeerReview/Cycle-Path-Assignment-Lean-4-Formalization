module

public import NPHardness.RegisteredFoundation
public import NPHardness.GraphEncoding
public import Complexity.Planar.EmbedComplete

/-!
Section 5 uses the registered `Complexity.PlanarGraph` predicate directly.
No second definition of planarity, or assumed equivalence between two
definitions of planarity, is introduced here. Embedding tables are the
registered certificate format. Their existence is not an embedding algorithm.
-/

@[expose] public section
namespace STACS2027
open Complexity Complexity.SAT

/-- Definition 7 together with planarity of its incidence multigraph. -/
def PlanarBoundedSATLanguage (input : SAT.Word) : Prop :=
  ∃ f, decode input = some f ∧ BoundedOccurrence f ∧
    PlanarGraph (incidenceGraph f) ∧ Satisfiable f

theorem planarBoundedSAT_encode_iff (f : CNF) :
    PlanarBoundedSATLanguage (encode f) ↔
      BoundedOccurrence f ∧ PlanarGraph (incidenceGraph f) ∧ Satisfiable f := by
  simp [PlanarBoundedSATLanguage]

/-- Planar CPAP for fixed `k`: the words of `CPAP k` whose written graph is planar. Planarity
is required of the target graph itself, not of a source formula. -/
def PlanarCPAP (k : Nat) (input : SAT.Word) : Prop :=
  ∃ f, encode f = input ∧ ValidGraphInstructions f ∧
    PlanarGraph (instructionGraph f) ∧
    HasAssignment (instructionGraph f) k (instructionBudget f)

theorem planarCPAP_encode_iff (k : Nat) (f : CNF) :
    PlanarCPAP k (encode f) ↔ ValidGraphInstructions f ∧
      PlanarGraph (instructionGraph f) ∧
      HasAssignment (instructionGraph f) k (instructionBudget f) := by
  constructor
  · rintro ⟨g, hg, h⟩
    obtain rfl := SAT.encode_injective _ _ hg
    exact h
  · exact fun h => ⟨f, rfl, h⟩

/-- Planar (≤1,≤2)-CNF: the registered (≤1,≤2) restriction, with a planar variable–clause
incidence graph. -/
def IsPlanarLeOneLeTwoCNF (f : CNF) : Prop :=
  IsLeOneLeTwoCNF f ∧ PlanarGraph (incidenceGraph f)

/-- Planar (≤1,≤2)-SAT: the words `encode f` with `f` satisfiable and satisfying
`IsPlanarLeOneLeTwoCNF`. -/
def PlanarLeOneLeTwoSAT (input : SAT.Word) : Prop :=
  ∃ f, encode f = input ∧ IsPlanarLeOneLeTwoCNF f ∧ Satisfiable f

/-- The language is the planar Definition 7 language used in the proofs. -/
theorem planarLeOneLeTwoSAT_eq : PlanarLeOneLeTwoSAT = PlanarBoundedSATLanguage := by
  funext input
  apply propext
  simp only [PlanarLeOneLeTwoSAT, IsPlanarLeOneLeTwoCNF, PlanarBoundedSATLanguage,
    SAT.decode_eq_some_iff, ← boundedOccurrence_iff_registered]
  simp only [eq_comm, and_assoc]

theorem GraphOutput.planar_encode_iff {f : CNF} {g : Graph} {budget : Nat}
    (h : GraphOutput f g budget) (k : Nat) :
    PlanarCPAP k (encode f) ↔ PlanarGraph g ∧ HasAssignment g k budget := by
  rw [planarCPAP_encode_iff, h.2.1, h.2.2]
  exact and_iff_right h.1

end STACS2027
