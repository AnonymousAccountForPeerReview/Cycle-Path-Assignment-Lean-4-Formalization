module

public import NPHardness.GraphEmitter

/-! Unconditional machine-based NP-hardness for the unrestricted CPAP graph
language, for every fixed k ≥ 5. No planar-hardness claim is made here. -/

@[expose] public section
namespace STACS2027
open Complexity Complexity.SAT Complexity.StackTableauEmitter

theorem graphEmitter_correct {n k : Nat} (hk : 5 ≤ k) (p : ClauseProgram n) (C D : NumExpr n)
    (input : SAT.Word) (env : Env n) (hf : p.Fits input env (C.eval env))
    (hwf : (sourceWheelEmitter p C).Fits input env (D.eval env))
    (hsz : ∀ c ∈ p.emit input env, c.length = 2 ∨ c.length = 3) :
    CPAP k (encode ((graphEmitter k p C D).emit input env)) ↔ Satisfiable (p.emit input env) := by
  let S := emitterSlots p (C.eval env)
  let V := C.eval env+1
  let N := V*(2*(3*S))
  let xs := allocatedEmit p input env (C.eval env) 0
  let ws := allocatedEmit (sourceWheelEmitter p C) input env (D.eval env) S
  have hs : ∀ x ∈ xs, x.1 < S := by
    intro x hx
    have h := (allocatedEmit_bounds p input env _ 0 hf x hx).2
    simpa only [Nat.zero_add] using h
  have hxsz : ∀ x ∈ xs, x.2.length = 2 ∨ x.2.length = 3 := by
    intro x hx
    apply hsz x.2
    rw [← allocatedEmit_forget p input env (C.eval env) 0]
    exact List.mem_map.mpr ⟨x,hx,rfl⟩
  have hxc : ∀ x ∈ xs, x.2.length ≤ 3 ∧ ∀ l ∈ x.2, l.var < V := by
    intro x hx
    refine ⟨by have := hxsz x hx; omega,?_⟩
    intro l hl
    have hh := (allocatedEmit_literals p input env _ 0 hf x hx).2 l hl
    change l.var < C.eval env+1
    omega
  have hxn : xs.Pairwise (fun x y => y.1 < x.1) := allocatedEmit_descending p input env _ 0 hf
  have hwn : ws.Pairwise (fun x y => y.1 < x.1) := allocatedEmit_descending _ input env _ S hwf
  have hwb : ∀ w ∈ ws, S ≤ w.1 := fun w hw => (allocatedEmit_bounds _ input env _ S hwf w hw).1
  have hws : ws.map Prod.snd = gridWheelFamily V (3*S) := by
    rw [allocatedEmit_forget,sourceWheelEmitter_emit]
  have hplace := gridLocated_placement hws hs hxc hxn
  have htags := gridLocated_tags_nodup hwn hwb hxn hs
  have hcorrect := locatedGraph_sat_iff_assignment hk (gridBoundedFormula_bounded hs hxsz hxn)
    (gridBoundedFormula_distinct hs (fun x hx => (hxc x hx).1) hxn)
    (gridLocated S ws xs) hplace htags (gridBoundedFormula_variableBound hs hxc)
  have hlen : (gridBoundedFormula V S xs).length = ws.length+xs.length := by
    have he := congrArg List.length hws
    simp only [List.length_map] at he
    simp only [gridBoundedFormula,List.length_append,List.length_map,gridCopyFormula]
    rw [← he]
  have hout := graphEmitter_output k p C D input env
  have hlang := hout.encode_iff k
  change CPAP k (encode ((graphEmitter k p C D).emit input env)) ↔
    HasAssignment (locatedGraph k N (gridLocated S ws xs)) k (ws.length+xs.length) at hlang
  rw [← hlen] at hlang
  have hsat := gridBoundedFormula_satisfiable hs hxc
  rw [allocatedEmit_forget] at hsat
  exact hlang.trans (hcorrect.symm.trans hsat)

/-- The graph emitter compiles to the original finite single-tape machine.
The bound is on its execution, not merely the number of emitted edges. -/
theorem graphEmitter_polyTime (k : Nat) (p : ClauseProgram 1) (C D : NumExpr 1) :
    PolyTime (fun input => encode ((graphEmitter k p C D).emit input (fun _ => input.length))) :=
  polyTime_emitter (graphEmitter k p C D)

/-- Every fixed k ≥ 5 gives an NP-hard CPAP language under the foundation's
original polynomial-time many-one reductions. Graphs need not be planar. -/
theorem cpap_np_hard {k : Nat} (hk : 5 ≤ k) : NPHard (CPAP k) := by
  intro L hL
  obtain ⟨p,hp,hsz⟩ := inNP_twoThreeEmitter hL
  obtain ⟨a,b,hbound⟩ := p.envelope_polynomial
  let C := CookLevinEmitter.boundExpr a b
  have hf (input : SAT.Word) : p.Fits input (fun _ => input.length) (C.eval (fun _ => input.length)) := by
    apply p.fits_of_envelope input _ input.length _ (fun _ => Nat.le_refl _)
    simpa [C] using hbound input.length
  obtain ⟨c,d,hwbound⟩ := (sourceWheelEmitter p C).envelope_polynomial
  let D := CookLevinEmitter.boundExpr c d
  have hwf (input : SAT.Word) : (sourceWheelEmitter p C).Fits input (fun _ => input.length)
      (D.eval (fun _ => input.length)) := by
    apply (sourceWheelEmitter p C).fits_of_envelope input _ input.length _ (fun _ => Nat.le_refl _)
    simpa [D] using hwbound input.length
  refine ⟨fun input => encode ((graphEmitter k p C D).emit input (fun _ => input.length)),
    graphEmitter_polyTime k p C D,?_⟩
  intro input
  exact (hp input).trans (graphEmitter_correct hk p C D input _ (hf input) (hwf input) (hsz input)).symm

end STACS2027
