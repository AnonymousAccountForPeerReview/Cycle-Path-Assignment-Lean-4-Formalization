module

public import NPHardness.PlanarSourceRotationTableDescriptors
public import NPHardness.PlanarSourcePackedLayout

/-! Static page tags in every compiled block coincide with the registered
comb side test. The input bits affect signs, never the geometric page. -/

@[expose] public section
namespace STACS2027.PlanarSource.RotationTable
open Complexity Complexity.SAT Complexity.Planar Comb Grid
open Complexity.StackTableauEmitter
open STACS2027.PlanarSource.Packed

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem cellTemplates_page {n : Nat} (W j idx : NumExpr n) (odd : Bool)
    (bp bn : Test n) (w : SAT.Word) (env : Env n) :
    ∀ t ∈ Packed.cellTemplates W j idx odd bp bn, t.top = sideOf (t.eval w env) := by
  cases odd <;>
    simp [Packed.cellTemplates,Template.eval,sideOf,cellT,orT,crossT,
      addN,NumExpr.eval]

theorem startTemplates_page {n : Nat} (W j : NumExpr n)
    (w : SAT.Word) (env : Env n) :
    ∀ t ∈ startTemplates W j, t.top = sideOf (t.eval w env) := by
  simp [startTemplates,Template.eval,sideOf,addN,NumExpr.eval]

theorem endTemplates_page {n : Nat} (W j : NumExpr n)
    (w : SAT.Word) (env : Env n) :
    ∀ t ∈ endTemplates W j, t.top = sideOf (t.eval w env) := by
  simp [endTemplates,Template.eval,sideOf,addN,NumExpr.eval]

theorem rainbowTemplates_page {n : Nat} (W j v : NumExpr n) (odd : Bool)
    (w : SAT.Word) (env : Env n) (hv : v.eval env < W.eval env) :
    ∀ t ∈ rainbowTemplates W j v odd, t.top = sideOf (t.eval w env) := by
  intro t ht
  have hm : t.eval w env ∈ (rainbowTemplates W j v odd).map (fun t => t.eval w env) :=
    List.mem_map.mpr ⟨t,ht,rfl⟩
  rw [rainbowTemplates_eval] at hm
  cases odd
  · simp only [Bool.false_eq_true,ite_false] at hm
    have hs := (rbEven_facts hv hm).2.2.2
    have hh : t.top = true := by
      simp only [rainbowTemplates,Bool.false_eq_true,ite_false,List.mem_cons,List.not_mem_nil,
        or_false] at ht
      rcases ht with rfl | rfl <;> rfl
    exact hh.trans hs.symm
  · simp only [ite_true] at hm
    have hs := (rbOdd_facts hv hm).2.2.2
    have hh : t.top = false := by
      simp only [rainbowTemplates,ite_true,List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl <;> rfl
    exact hh.trans hs.symm

/-- A source clause equality turns the static page theorem into the exact
`Comb.isTop` premise used by descriptor correctness. -/
theorem template_source_page {n : Nat} {f : CNF} (t : Template n)
    (w : SAT.Word) (env : Env n) {j : Nat} (hj : j < f.length)
    (hc : f[j] = t.eval w env) (ht : t.top = sideOf (t.eval w env)) :
    t.top = isTop f j := by rw [isTop_eq hj,hc]; exact ht

end STACS2027.PlanarSource.RotationTable
