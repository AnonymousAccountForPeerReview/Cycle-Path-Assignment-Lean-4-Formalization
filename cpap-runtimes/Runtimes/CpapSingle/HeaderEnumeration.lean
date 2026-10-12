module

public import Runtimes.C4.Main
public import Runtimes.Flow.Single
public import Outerplanar.RAM.BoundedDemo
import Mathlib.Tactic

/-! # The checked four-cycle enumerator with its count before the cycle stream -/

@[expose] public section

namespace STACS2027.Runtimes.CpapSingle

open STACS2027 STACS2027.Algo STACS2027.RAM

/-- Prefix a stream by its payload size, cycle length, and stored exact count. -/
def emitHeader : Stmt := .seq (.const 800 2) (.seq (.add 801 C4.gT C4.gT)
  (.seq (.add 801 801 801) (.seq (.add 801 801 800) (.seq (.write 801)
    (.seq (.const 800 4) (.seq (.write 800) (.write C4.gT)))))))
def headerEnumerator : Stmt := .seq R0.r0 (.seq C4.c4Sub (.seq emitHeader C4.emit))

theorem headerEnumerator_spec (g : Graph) {S : Nat} (hSp : C4.c4Space g≤S) :
    HTB S headerEnumerator (·=initial (graphInput g))
      (fun c=>c.out=(4*(C4.enumOutS g).length+2)::4::(C4.enumOutS g).length::(C4.enumOutS g).flatten)
      ((C4.CF+9)*(g.length+1+(cycles g 4).length+
        min (numV g*numV g) (C4.pow43 g.length))) := by
  intro c hc
  have h0S : R0.endR0 g≤S := by
    have := R1.layout_eqs g (R0.endR0 g)
    unfold C4.c4Space at hSp
    omega
  obtain ⟨c₁,t₁,he₁,h0,ht₁⟩ := R0.r0_spec g h0S c hc
  have hfin := h0.fin
  obtain ⟨c₂,t₂,he₂,⟨hE,ho₂,_,_,hE₂⟩,ht₂⟩ := C4.c4Sub_spec g c₁ (S:=S)
    (by rw [hfin];exact hSp) c₁ ⟨h0,rfl⟩
  let cH := run emitHeader c₂
  have eh : ExecB S emitHeader c₂ 8 cH :=
    Exec.toExecB_of_memFree rfl (Flow.exec_loopFree (by decide) c₂
      (by simp [emitHeader,RAM.cost]))
  have hmH : cH.mem=c₂.mem := by simp [cH,emitHeader,run]
  have hEH : C4.EnumPost g cH := hE.transfer (by
    intro r hr _
    have hn : r≠800 ∧ r≠801 := by omega
    simp [cH,emitHeader,run,hn.1,hn.2]) hmH
  have houtH : cH.out=c₂.out++[4*(C4.enumOutS g).length+2,4,(C4.enumOutS g).length] := by
    simp [cH,emitHeader,run,hE.t];omega
  have hfreeH : cH.reg rFREE=c₂.reg rFREE := by simp [cH,emitHeader,run]
  obtain ⟨c₃,t₃,he₃,⟨ho₃,_⟩,ht₃⟩ := C4.emit_spec g cH (S:=S) (by
    rw [hfreeH]
    rw [hfin] at hE₂
    unfold C4.c4Space at hSp
    omega) cH ⟨hEH,rfl⟩
  refine ⟨c₃,t₁+(t₂+(8+t₃)),.seq he₁ (.seq he₂ (.seq eh he₃)),?_,?_⟩
  · change c₃.out=_
    rw [ho₃,houtH,ho₂,h0.out]
    simp
  · simp only [R0.C0,C4.CSub,C4.CF] at ht₁ ht₂ ⊢
    have : 0≤min (numV g*numV g) (C4.pow43 g.length) := Nat.zero_le _
    nlinarith

end STACS2027.Runtimes.CpapSingle
