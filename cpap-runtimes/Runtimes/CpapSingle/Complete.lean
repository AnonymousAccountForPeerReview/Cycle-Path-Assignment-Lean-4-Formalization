module

public import Runtimes.CpapSingle.HeaderEnumeration
public import Runtimes.CpapSingle.GraphLength
public import Runtimes.C4.Statement
import Mathlib.Tactic

/-! # Corollary 3 as one concrete RAM program, including cycle enumeration -/

@[expose] public section

namespace STACS2027.Runtimes

open STACS2027 STACS2027.Algo STACS2027.RAM Flow CpapSingle

def cyclePayload (cs : List Cycle) : List Nat := 4::cs.length::cs.flatten

/-- A single program parses a graph, enumerates its four-cycles, solves the reduction,
and extracts an optimal assignment. The almost-linear flow algorithm is an explicit cited
hypothesis; all transitions between the other stages are actual bounded RAM code. -/
theorem fourCycleAssignment_single_explicit {F : RAM.Stmt} {T : Nat→Nat}
    (hF : MinCostFlowSolver F T) :
    ∃ (prog : RAM.Stmt) (C : Nat),∀ g : Graph,
      ∃ (cs : List Cycle) (pos : List Nat) (steps : Nat),
        cs.Perm (cycles g 4) ∧
        RAM.ComputesIn prog (graphInput g) pos steps
          (C*(labelBound g+(cycles g 4).length+g.length+1+
            min (numV g*numV g) (C4.pow43 g.length))+16*T (30*(cycles g 4).length+5)) ∧
        steps≤C*((cycles g 4).length+g.length+1+
            min (numV g*numV g) (C4.pow43 g.length))+16*T (30*(cycles g 4).length+5) ∧
        pos.length=cs.length ∧ (∀ p∈pos,p<4) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 4 (cost (List.zipWith selected cs pos)) := by
  obtain ⟨flowProg,CF,hflow⟩ := cpap4_flow_single hF
  refine ⟨pipe3 lenGraph headerEnumerator RAM.EchoDemo.echo flowProg,
    4*(C4.CF+9)+4*C4.CS4+4*CF+1000,fun g=>?_⟩
  let cs := C4.enumOutS g
  let xs := cyclePayload cs
  have hperm : cs.Perm (cycles g 4) := C4.enumOutS_perm g
  have hlen : cs.length=(cycles g 4).length := hperm.length_eq
  have hxs : xs.length=4*(cycles g 4).length+2 := by
    dsimp only [xs,cyclePayload,cs]
    rw [List.length_cons,List.length_cons,C4.length_flatten_enumOutS]
  obtain ⟨tE,htE,heE⟩ := HTB.computesIn (headerEnumerator_spec g le_rfl)
  have heHeader : RAM.ComputesIn headerEnumerator (graphInput g) (xs.length::xs) tE (C4.c4Space g) := by
    rw [hxs]
    simpa only [xs,cyclePayload,cs,C4.length_enumOutS] using heE
  obtain ⟨tQ,htQ,heQ⟩ := RAM.EchoDemo.echo_computesIn xs
  obtain ⟨pos,tF,heF,htF,hpos,hlt,hvalid,hopt⟩ := hflow g cs hperm
  have heLast : RAM.ComputesIn flowProg (graphInput g++xs) pos tF
      (CF*(labelBound g+cs.length+g.length+1)+4*T (30*cs.length+5)) := by
    simpa [xs,cyclePayload,flowInput,verts] using heF
  obtain ⟨steps,he,ht⟩ := pipe3_spec (lenGraph_spec g) heHeader heQ heLast
  have hspace := C4.c4Space_le g
  refine ⟨cs,pos,steps,hperm,he.mono ?_,?_,hpos,hlt,hvalid,hopt⟩
  · rw [List.length_cons,hxs,length_graphInput,hlen]
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc] at hspace ⊢
    omega
  · rw [length_graphInput] at ht
    rw [hxs] at htQ
    rw [hlen] at htF
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc] at htE htF ht ⊢
    omega


/-- The complete single-program Corollary 3 bound, with the cited almost-linear
flow algorithm remaining its sole algorithmic hypothesis. -/
theorem fourCycleAssignment_single {F : RAM.Stmt} {T : Nat→Nat}
    (hF : MinCostFlowSolver F T) (hT : AlmostLinear T) :
    ∃ (prog : RAM.Stmt) (C₀ : Nat),∀ ε : Real,0<ε → ∃ C : Real,∀ g : Graph,
      ∃ (cs : List Cycle) (pos : List Nat) (steps space : Nat),
        cs.Perm (cycles g 4) ∧ RAM.ComputesIn prog (graphInput g) pos steps space ∧
        (∀ X : Nat,g.length^4≤X^3 →
          (steps : Real)≤C₀*((cycles g 4).length+g.length+1+
            (min (numV g*numV g) X : Nat) : Real)+C*((cycles g 4).length : Real)^(1+ε) ∧
          (space : Real)≤C₀*(labelBound g+(cycles g 4).length+g.length+1+
            (min (numV g*numV g) X : Nat) : Real)+C*((cycles g 4).length : Real)^(1+ε)) ∧
        pos.length=cs.length ∧ (∀ p∈pos,p<4) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 4 (cost (List.zipWith selected cs pos)) := by
  obtain ⟨prog,C₀,h⟩ := fourCycleAssignment_single_explicit hF
  refine ⟨prog,C₀+16*T 5,fun ε hε=>?_⟩
  obtain ⟨Cε,hCε⟩ := hT ε hε
  refine ⟨(16 : Nat)*(Cε*(35 : Real)^(1+ε)),fun g=>?_⟩
  obtain ⟨cs,pos,steps,hp,hc,hs,hl,hlt,hv,ho⟩ := h g
  let A := min (numV g*numV g) (C4.pow43 g.length)
  have htBound := split_bound (s:=steps) (L:=(cycles g 4).length+g.length+1+A)
    (k:=16) (C₀:=C₀) (t:=(cycles g 4).length) (a:=30)
    hε (almostLinear_const hCε) hCε le_rfl (by omega) hs
  have hspaceBound := split_bound
    (s:=C₀*(labelBound g+(cycles g 4).length+g.length+1+A)+16*T (30*(cycles g 4).length+5))
    (L:=labelBound g+(cycles g 4).length+g.length+1+A)
    (k:=16) (C₀:=C₀) (t:=(cycles g 4).length) (a:=30)
    hε (almostLinear_const hCε) hCε le_rfl (by omega) le_rfl
  refine ⟨cs,pos,steps,_,hp,hc,fun X hX=>?_,hl,hlt,hv,ho⟩
  have hmin : (A : Real)≤(min (numV g*numV g) X : Nat) := by
    exact_mod_cast C4.min_pow43_le (a:=numV g*numV g) hX
  have hmono := mul_le_mul_of_nonneg_left hmin
    (Nat.cast_nonneg (C₀+16*T 5) : (0 : Real)≤(C₀+16*T 5 : Nat))
  dsimp only [A] at htBound hspaceBound hmono
  push_cast at htBound hspaceBound hmono ⊢
  exact ⟨by linarith,by linarith⟩

end STACS2027.Runtimes
