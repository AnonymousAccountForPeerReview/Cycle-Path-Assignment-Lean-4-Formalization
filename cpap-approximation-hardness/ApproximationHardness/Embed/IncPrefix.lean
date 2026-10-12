module

public import ApproximationHardness.Embed.FirstOccurrences
public import ApproximationHardness.RAM.Orient.Spec
import Lean.Elab.Tactic.Omega

/-! # Incidence representatives at a formula input prefix -/

@[expose] public section

namespace STACS2027.Embed

open Complexity.SAT Complexity.Planar.Comb

/-- The literal read at a clause/literal prefix is the indexed incidence occurrence. -/
theorem varAt_prefix {f pre suf : CNF} {cl : Clause} {lpre lsuf : List Literal} {l : Literal}
    (hf : pre++cl::suf=f) (hc : lpre++l::lsuf=cl) :
    varAt f (pre.flatten.length+lpre.length) = l.var := by
  have he := RAM.flatten_prefix hf lpre hc
  have hg := (RAM.getElem_prefix he).1
  unfold varAt
  rw [show pre.flatten.length+lpre.length=(pre.flatten++lpre).length by simp]
  rw [List.getD_eq_getElem?_getD,hg]
  rfl

theorem incRep_odd_prefix {f pre suf : CNF} {cl : Clause} {lpre lsuf : List Literal} {l : Literal}
    (hf : pre++cl::suf=f) (hc : lpre++l::lsuf=cl) :
    incRep f (2*(pre.flatten.length+lpre.length)+1) = 2*pre.flatten.length+1 := by
  rw [incRep_odd,RAM.oj_prefix hf (by rw [←hc];simp),RAM.off_prefix hf]

theorem incRep_even_prefix {f pre suf : CNF} {cl : Clause} {lpre lsuf : List Literal} {l : Literal}
    (hf : pre++cl::suf=f) (hc : lpre++l::lsuf=cl) :
    firstCode ((pre.flatten++lpre)++[l]) l.var-1 =
      incRep f (2*(pre.flatten.length+lpre.length)) := by
  have he := RAM.flatten_prefix hf lpre hc
  have hp : ((pre.flatten++lpre)++[l]) <+: f.flatten := by
    rw [←he]
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using
      List.prefix_append ((pre.flatten++lpre)++[l]) (lsuf++suf.flatten)
  have hs := firstCode_prefix hp (firstCode_positive (pre.flatten++lpre) l)
  have hi : pre.flatten.length+lpre.length < f.flatten.length := by
    rw [←he]; simp
  rw [←hs,←varAt_prefix hf hc,firstCode_firstOcc f hi,incRep_even]
  omega

end STACS2027.Embed
