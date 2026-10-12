module

public import Runtimes.BoundedCost.OuterRepresentation
public import Runtimes.BoundedCost.InnerCompilerBridge
import Mathlib.Tactic

/-! The complete inner scan preserves the outer compression state and its
read-only clause and digit arrays. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3 Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem outerGeometry_special_frame {S nodes clauses depth : ℕ} {layout : CompilerLayout}
    {special : CNF} (hgeo : OuterGeometry S layout nodes clauses depth special.length)
    (hcodes : (TwoSat.codes special).length ≤ 2 * special.length) :
    ∀ i < (TwoSat.codes special).length,
      InnerMemoryFrame layout nodes clauses depth (layout.special + i) := by
  intro i hi
  apply innerGeometry_readOnlyGap hgeo.inner
  have hlabels := hgeo.inner.labelsSnapshot
  have hbase := hgeo.inner.activeForcedSnapshot
  have hseed := hgeo.seedSpecial
  have hspecial := hgeo.specialDigits
  have hdigits := hgeo.outerInner
  omega

theorem outerGeometry_digits_frame {S nodes clauses depth : ℕ} {layout : CompilerLayout}
    {special : CNF} {digits : List ℕ}
    (hgeo : OuterGeometry S layout nodes clauses depth special.length)
    (hlen : digits.length = special.length) :
    ∀ i < digits.length,
      InnerMemoryFrame layout nodes clauses depth (layout.outerDigits + i) := by
  intro i hi
  apply innerGeometry_readOnlyGap hgeo.inner
  have hlabels := hgeo.inner.labelsSnapshot
  have hbase := hgeo.inner.activeForcedSnapshot
  have hseed := hgeo.seedSpecial
  have hspecial := hgeo.specialDigits
  have hdigits := hgeo.outerInner
  omega

theorem outerBasic_after_inner {F : Stmt} {S time nodes budget depth processed deleted : ℕ}
    {layout : CompilerLayout} {original special : CNF} {τ : Assignment}
    {rows : List (Bool × Clause)} {oldOutput digits innerDigits forcedBits : List ℕ}
    {answer : Option Assignment} {c₀ c : Config}
    (hgeo : OuterGeometry S layout nodes original.length depth special.length)
    (hspecial : (TwoSat.codes special).length ≤ 2 * special.length)
    (hb : OuterBasic F layout nodes original τ rows special budget depth processed oldOutput digits c₀)
    (he : ExecB S (Compiler.innerScan F) c₀ time c)
    (hi : InnerRep F layout nodes original τ depth budget deleted (maskWords rows) forcedBits
      oldOutput c₀.mem answer innerDigits c) :
    OuterBasic F layout nodes original τ rows special budget depth processed oldOutput digits c := by
  obtain ⟨hg, _, _, _, _, _, hspecialArray, hob, hol, _, hdigits, hlen, hcount, hp, halive⟩ := hb
  obtain ⟨⟨hpath, _, hbase, _, _, _, hradix, _⟩, _, hframe⟩ := hi
  obtain ⟨_, hcodes, href, hzero, hout, _, _, _⟩ := hpath
  have hprotected (r : ℕ) (hr : r ∈ Compiler.innerProtectedRegisters) :
      c.reg (callerRegister r) = c₀.reg (callerRegister r) :=
    he.reg_frame (Compiler.not_mem_innerScan_protected F hr)
  refine ⟨Compiler.globals_actualInner_frame hg he, hcodes, href, hzero, hout, hbase,
    ?_, (hprotected rOB (by simp [Compiler.innerProtectedRegisters])).trans hob,
    (hprotected rOL (by simp [Compiler.innerProtectedRegisters])).trans hol,
    ?_, ?_, hlen,
    (hprotected seedSpecialCount (by simp [Compiler.innerProtectedRegisters])).trans hcount,
    (hprotected Compiler.processed (by simp [Compiler.innerProtectedRegisters])).trans hp,
    (hprotected Compiler.alive (by simp [Compiler.innerProtectedRegisters])).trans halive⟩
  · intro i hi
    exact (hframe _ (outerGeometry_special_frame hgeo hspecial i hi)).trans (hspecialArray i hi)
  · simpa only [innerCallerRegister_radix] using hradix
  · intro i hi
    exact (hframe _ (outerGeometry_digits_frame hgeo hlen i hi)).trans (hdigits i hi)

theorem outerRep_after_inner {F : Stmt} {S time nodes budget depth processed deleted : ℕ}
    {layout : CompilerLayout} {original special : CNF} {τ : Assignment}
    {rows : List (Bool × Clause)} {oldOutput digits innerDigits forcedBits : List ℕ}
    {answer : Option Assignment} {c₀ c : Config}
    (hgeo : OuterGeometry S layout nodes original.length depth special.length)
    (hspecial : (TwoSat.codes special).length ≤ 2 * special.length)
    (hb : OuterBasic F layout nodes original τ rows special budget depth processed oldOutput digits c₀)
    (he : ExecB S (Compiler.innerScan F) c₀ time c)
    (hi : InnerRep F layout nodes original τ depth budget deleted (maskWords rows) forcedBits
      oldOutput c₀.mem answer innerDigits c) :
    OuterRep F layout nodes original τ rows special budget depth processed oldOutput answer digits c :=
  ⟨outerBasic_after_inner hgeo hspecial hb he hi, hi.2.1⟩

end STACS2027.Runtimes.BoundedCost
