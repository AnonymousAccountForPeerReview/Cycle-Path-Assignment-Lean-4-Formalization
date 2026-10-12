module

public import NPHardness.PlanarSourcePackedCorrect
public import NPHardness.PlanarBoundedMembership

/-!
Unconditional NP-completeness of the planar bounded-occurrence SAT language
used by Section 5, Definition 7. All three restrictions concern the same
decoded CNF. The reduction is an explicit two-stage clause program, compiled
to the registered polynomial-time single-tape machine model.

The proof reuses the registered ANONYMIZED–ANONYMIZED emitter, grid construction, compiler,
and NP definitions. Its new occurrence-ring construction preserves actual
incidence planarity and has at most one positive and two negative occurrences
per variable. No independently hard restrictions are combined by assumption.
-/

@[expose] public section
namespace STACS2027
open Complexity Complexity.SAT

/-- Every registered NP language reduces in polynomial time to the planar
Definition 7 language, on all binary inputs. -/
theorem planarBoundedSAT_np_hard : NPHard PlanarBoundedSATLanguage := by
  intro L hL
  obtain ⟨P,hP⟩ := CookLevinEmitter.inNP_emitter hL
  refine ⟨fun x => encode (PlanarSource.Packed.output P x),
    PlanarSource.Packed.output_polyTime P,?_⟩
  intro x
  rw [hP x,SAT_encode_iff,planarBoundedSAT_encode_iff]
  have h := PlanarSource.Packed.output_correct P x
  exact ⟨fun hs => ⟨h.1,h.2.1,h.2.2.mpr hs⟩,fun hs => h.2.2.mp hs.2.2⟩

/-- Definition 7, including actual incidence planarity, is NP-complete with
the registered verifier, machine model, and binary CNF encoding. -/
theorem planarBoundedSAT_np_complete : NPComplete PlanarBoundedSATLanguage :=
  ⟨planarBoundedSAT_inNP,planarBoundedSAT_np_hard⟩

/-- Planar (≤1,≤2)-SAT is NP-complete: the registered (≤1,≤2) restriction together with a
planar variable–clause incidence graph. -/
theorem planarLeOneLeTwoSAT_np_complete : NPComplete PlanarLeOneLeTwoSAT := by
  rw [planarLeOneLeTwoSAT_eq]
  exact planarBoundedSAT_np_complete

end STACS2027
