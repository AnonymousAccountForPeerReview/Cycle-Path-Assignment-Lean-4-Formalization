module

public import NPHardness.SourceWordPlanar
public import NPHardness.SourceWordSafety

/-! Complete source-family runtime interface: the actual word-machine run
computes the planar graph, uses linearly many charged record/pointer steps,
and has a single logarithmic numeric-payload width for every prefix. -/

@[expose] public section
namespace STACS2027.SourceWord
open Complexity Complexity.SAT Complexity.Planar Grid WordPipeline PlanarSource

theorem ringGrid_linear_word_planar {k : Nat} (hk : 5≤k) (W m : Nat)
    (bits : Nat→Nat→Bool×Bool) :
    let f:=gridCNF W m bits
    let input:=Formula.ringFormula f (Packed.incidenceNext f) (Formula.sourceSigns f)
    ∃t w, Runs (step k input.length input) t (initial input)
        (.graph f.flatten.length (Formula.sourceSigns f)
          ⟨.done,historyMemory input.flatten,
            (orientedFormulaGraph (sourceEndpointChoices (Formula.sourceSigns f)) k input).reverse⟩) ∧
      t≤(variableBound input+1)*linearCoefficient k ∧
      w≤(variableBound input+1).log2+((4*linearCoefficient k+11)*(gadgetWidth k+1)).log2+2 ∧
      PlanarGraph (orientedFormulaGraph (sourceEndpointChoices (Formula.sourceSigns f)) k input).reverse ∧
      (Satisfiable f ↔ HasAssignment
        (orientedFormulaGraph (sourceEndpointChoices (Formula.sourceSigns f)) k input).reverse k input.length) ∧
      ∀u s,u≤t→Runs (step k input.length input) u (initial input) s→WordsFit k w input s := by
  dsimp only
  obtain ⟨t,w,hr,ht,hw,hs,hwords⟩ := linear_word_construction hk (gridCNF W m bits) _
    (grid_next_bounded W m bits) (Packed.ringGrid_correct W m bits).1
    (Packed.ringGrid_distinct W m bits)
  rw [ringGrid_input_variableBound]
  refine ⟨t,w,hr,ht,hw,?_,(Packed.ringGrid_correct W m bits).2.2.symm.trans hs,hwords⟩
  exact (PlanarGluing.planarGraph_perm (List.reverse_perm _)).mpr
    (Packed.ringGrid_graph_planar k W m bits)

/-- The exact NP-hard source reduction output is handled without a supplied
orientation table or geometric certificate. The bound is stated in terms of
its actual variable bound; all scalar payloads satisfy the uniform word bound. -/
theorem packed_linear_word_planar {k : Nat} (hk : 5≤k)
    (P : Complexity.StackTableauEmitter.ClauseProgram 1) (x : SAT.Word) :
    let f:=Emit.gridOut P x
    let input:=Packed.output P x
    ∃t w, Runs (step k input.length input) t (initial input)
        (.graph f.flatten.length (Formula.sourceSigns f)
          ⟨.done,historyMemory input.flatten,
            (orientedFormulaGraph (sourceEndpointChoices (Formula.sourceSigns f)) k input).reverse⟩) ∧
      t≤(variableBound input+1)*linearCoefficient k ∧
      w≤(variableBound input+1).log2+((4*linearCoefficient k+11)*(gadgetWidth k+1)).log2+2 ∧
      PlanarGraph (orientedFormulaGraph (sourceEndpointChoices (Formula.sourceSigns f)) k input).reverse ∧
      (Satisfiable (P.emit x (fun _=>x.length)) ↔ HasAssignment
        (orientedFormulaGraph (sourceEndpointChoices (Formula.sourceSigns f)) k input).reverse k input.length) ∧
      ∀u s,u≤t→Runs (step k input.length input) u (initial input) s→WordsFit k w input s := by
  dsimp only
  have h : ∃t w, Runs (step k (Packed.output P x).length (Packed.output P x)) t (initial (Packed.output P x))
        (.graph (Emit.gridOut P x).flatten.length (Formula.sourceSigns (Emit.gridOut P x))
          ⟨.done,historyMemory (Packed.output P x).flatten,
            (orientedFormulaGraph (sourceEndpointChoices (Formula.sourceSigns (Emit.gridOut P x))) k (Packed.output P x)).reverse⟩) ∧
      t≤(variableBound (Packed.output P x)+1)*linearCoefficient k ∧
      w≤(variableBound (Packed.output P x)+1).log2+((4*linearCoefficient k+11)*(gadgetWidth k+1)).log2+2 ∧
      PlanarGraph (orientedFormulaGraph (sourceEndpointChoices (Formula.sourceSigns (Emit.gridOut P x))) k (Packed.output P x)).reverse ∧
      (Satisfiable (Emit.gridOut P x) ↔ HasAssignment
        (orientedFormulaGraph (sourceEndpointChoices (Formula.sourceSigns (Emit.gridOut P x))) k (Packed.output P x)).reverse k (Packed.output P x).length) ∧
      ∀u s,u≤t→Runs (step k (Packed.output P x).length (Packed.output P x)) u (initial (Packed.output P x)) s→
        WordsFit k w (Packed.output P x) s := by
    rw [Packed.output_ringFormula,Emit.gridOut_eq]
    exact ringGrid_linear_word_planar hk _ _ _
  obtain ⟨t,w,hr,ht,hw,hp,hs,hwords⟩ := h
  exact ⟨t,w,hr,ht,hw,hp,(Emit.gridOut_sat P x).symm.trans hs,hwords⟩

end STACS2027.SourceWord
