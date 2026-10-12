module

public import ApproximationHardness.Embed.DefaultCycle
import Lean.Elab.Tactic.Omega

/-! # Pure finite-table bounds for real forest vertices -/

@[expose] public section

namespace STACS2027.Embed.ForestData

theorem distinguished_mem_of_degree {F : ForestData} {v : Nat}
    (h : (F.dartsAt v).length=3) : F.zOf v∈F.dartsAt v := by
  unfold zOf
  rw [ite_eq_left h]
  cases he : ((F.dartsAt v).filter (fun d=>!decide (F.IsTree d))).getLast? with
  | some d => exact List.mem_of_mem_filter (List.mem_of_getLast? he)
  | none =>
    have hne : F.dartsAt v≠[] := by intro hn;simp [hn] at h
    simp only [List.getLastD_eq_getLast?,List.getLast?_eq_some_getLast hne,Option.getD_some]
    exact List.getLast_mem hne

theorem real_parts_bound {F : ForestData} (hF : F.Valid) {v : Nat}
    (hv : v<2*F.E) : (F.parts v).length≤2 := by
  by_cases hver : F.IsVertex v
  · rw [parts_vertex hver,List.length_map]
    by_cases hr : F.IsRoot v
    · rw [ite_eq_left hr]
      by_cases hd : (F.dartsAt v).length=3
      · rw [List.length_erase_of_mem (distinguished_mem_of_degree hd),hd]
      · have := hF.deg v
        have := List.length_erase_le (a:=F.zOf v) (l:=F.dartsAt v)
        omega
    · rw [ite_eq_right hr]
      have hp : F.par v∈F.dartsAt v := mem_dartsAt.mpr ⟨hF.par_lt v hver hr,hF.par_rep v hver hr⟩
      rw [List.length_erase_of_mem hp]
      have := hF.deg v
      omega
  · have ht : ¬F.IsTop v := by intro h;have := h.1;omega
    simp [parts,hver,ht]

theorem real_child_bound {F : ForestData} (hF : F.Valid) {v w : Nat}
    (hv : v<2*F.E) (hw : Item.node w∈F.parts v) : w<2*F.E ∧ F.par w<2*F.E := by
  by_cases hver : F.IsVertex v
  · rw [parts_vertex hver] at hw
    obtain ⟨d,hd,hi⟩ := List.mem_map.mp hw
    have hdm := List.mem_of_mem_erase hd
    have hdl := (mem_dartsAt.mp hdm).1
    unfold item at hi
    split at hi
    · rename_i hdown
      cases hi
      have hc := down_child hF hdl hdown
      exact ⟨hc.1.1,hF.par_lt _ hc.1 hc.2.1⟩
    · cases hi
  · have ht : ¬F.IsTop v := by intro h;have := h.1;omega
    simp [parts,hver,ht] at hw

end STACS2027.Embed.ForestData
