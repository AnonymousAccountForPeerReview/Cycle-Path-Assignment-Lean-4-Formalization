module

public import NPHardness.PlanarSourcePackedRingPhase
public import NPHardness.PlanarSourceRotationTablePacked

/-! Exact local emitted ring edges from structural descriptor coverage,
registered angular keys, and duplicate-free active occurrence indices. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar Comb
open RotationTable

theorem successorProgram_registered {n : Nat} {f : CNF} (hf : CombOK f)
    (p : Occurrence n) (xs : List (Occurrence n)) (w : SAT.Word) (env : Env n)
    (signs : Nat → Bool)
    (hp : EntryCorrect f (p.eval w env))
    (hx : ∀ q ∈ xs, EntryCorrect f (q.eval w env))
    (hlp : (p.eval w env).live = true)
    (hc : ∀ e, e ∈ activeIndices (p.eval w env) (xs.map (fun q => q.eval w env)) ↔
      e < nM f ∧ vr f (oj f e) (ot f e) = (p.eval w env).variable)
    (hn : (activeIndices (p.eval w env) (xs.map (fun q => q.eval w env))).Nodup)
    (hs : ∀ q ∈ xs, (q.eval w env).live = true → q.sign.eval w env = signs (q.index.eval env)) :
    let next := rnext (incidenceOrder f (p.eval w env).variable) (p.index.eval env)
    (successorProgram p xs).emit w env =
      [[⟨p.index.eval env,p.sign.eval w env⟩,⟨next,!(signs next)⟩]] := by
  let next := rnext (incidenceOrder f (p.eval w env).variable) (p.index.eval env)
  change (successorProgram p xs).emit w env =
    [[⟨p.index.eval env,p.sign.eval w env⟩,⟨next,!(signs next)⟩]]
  have hg (q : Occurrence n) (hq : q ∈ xs) :
      (successorTest p q xs).eval w env = true ↔
        Active (p.eval w env) (q.eval w env) ∧ q.index.eval env = next := by
    constructor
    · intro h
      have ha := (successorTest_eval p q xs w env).mp h |>.2.1
      have he := (successorTest_iff_registered hf p q xs w env hp (hx q hq) hx hlp ha hc).mp h
      exact ⟨ha,he.symm⟩
    · rintro ⟨ha,he⟩
      exact (successorTest_iff_registered hf p q xs w env hp (hx q hq) hx hlp ha hc).mpr he.symm
  have hfilter :
      (xs.filter (fun q => (successorTest p q xs).eval w env)).map (fun q => q.index.eval env) =
        (activeIndices (p.eval w env) (xs.map (fun q => q.eval w env))).filter (fun i => i == next) := by
    have hall : ∀ ys : List (Occurrence n), (∀ q ∈ ys, q ∈ xs) →
        (ys.filter (fun q => (successorTest p q xs).eval w env)).map (fun q => q.index.eval env) =
          (activeIndices (p.eval w env) (ys.map (fun q => q.eval w env))).filter (fun i => i == next) := by
      intro ys
      induction ys with
      | nil => intro hy; rfl
      | cons q ys ih =>
          intro hy
          have hq := hg q (hy q (by simp))
          have hi := ih (fun r hr => hy r (by simp [hr]))
          by_cases ha : Active (p.eval w env) (q.eval w env) <;>
            by_cases he : q.index.eval env = next <;>
            simp_all [activeIndices, Active, Occurrence.eval]
    exact hall xs (fun q hq => hq)
  have hp' := hp hlp
  have hv : (p.eval w env).variable < nK f := by
    rw [hp'.2.1]
    have ho := occ_spec f _ hp'.1
    exact vr_lt _ _ ho.1 ho.2.1
  have hpMem : (p.index.eval env) ∈ incidenceOrder f (p.eval w env).variable :=
    (mem_incidenceOrder f hv).mpr ⟨hp'.1,hp'.2.1.symm⟩
  have hnMem : next ∈ activeIndices (p.eval w env) (xs.map (fun q => q.eval w env)) := by
    apply (hc next).mpr
    exact (mem_incidenceOrder f hv).mp
      (rnext_mem (incidenceOrder_nodup hf _) hpMem)
  apply successorProgram_exact p xs w env next (signs next)
  · rw [hfilter]
    exact hn.filter _
  · intro i
    rw [hfilter, List.mem_filter, beq_iff_eq]
    exact ⟨fun h => h.2, fun h => by subst i; exact ⟨hnMem,rfl⟩⟩
  · intro q hq hqt
    have h := (hg q hq).mp hqt
    rw [hs q hq h.1.1, h.2]

end STACS2027.PlanarSource.Packed
