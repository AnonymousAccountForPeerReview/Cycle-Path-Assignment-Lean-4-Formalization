module

public import ApproximationHardness.Embed.SM

/-! # Decoding the solver's stored Boolean instructions -/

@[expose] public section

namespace STACS2027.Embed

def SMem.evalBit (m : SMem) (gid : Nat → Nat) (o : Nat → Bool) (v : Nat) : Bool :=
  if m.inf v = 1 then !(o (m.ia v)) else
  if m.inf v = 2 then o (m.ia v) else
  if m.inf v = 3 then o (gid v) else
  if m.inf v = 4 then !(o (gid v)) else false

theorem SMem.evalBit_zero (m : SMem) (gid : Nat → Nat) (o : Nat → Bool) (v : Nat)
    (h : m.inf v = 0) : m.evalBit gid o v = false := by simp [evalBit, h]

theorem SMem.evalBit_target (m : SMem) (gid : Nat → Nat) (o : Nat → Bool) (v d : Nat)
    (code : Bool) (h : m.inf v = if code then 1 else 2) (hi : m.ia v = d) :
    m.evalBit gid o v = if code then !(o d) else o d := by
  cases code <;> simp_all [evalBit]

theorem SMem.evalBit_fork (m : SMem) (gid : Nat → Nat) (o : Nat → Bool) (v : Nat)
    (code : Bool) (h : m.inf v = if code then 3 else 4) :
    m.evalBit gid o v = if code then o (gid v) else !(o (gid v)) := by
  cases code <;> simp_all [evalBit]

end STACS2027.Embed
