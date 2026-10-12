module

public import Outerplanar.RAM.Bounded
public import Outerplanar.RAM.BoundedHT
public import Outerplanar.RAM.BoundedLib
public import Outerplanar.RAM.BoundedDemo

/-!
# The space-bounded RAM framework

* `Bounded.lean`: bounded runs `ExecB S` (every `load`/`store` address below `S`),
  `ComputesIn s input output time space`, independence of the memory at and above the bound
  (`ExecB.congr`, `ComputesIn.of_eqBelow`), `memFree` and `Exec.toExecB_of_memFree`;
* `BoundedHT.lean`: the triples `HTB S s P Q b`, the twins of the rules of `HT.lean` and
  `Frame.lean`, the address obligations `AddrOK S s c` of loop-free code, the bridges
  `HTB.toHT`, `HTB.of_HT`, `HTB.of_HT_addrOK`, `HTB.mono_S`, `HTB.computesIn`;
* `BoundedLib.lean`: the twins of the instruction and macro specifications of `Lib.lean`, the
  `AddrOK` simp lemmas of the macros, the tactics `addr_ok` and `addr_simp`;
* `BoundedDemo.lean`: a complete program with its `ComputesIn` theorem
  (`EchoDemo.echo_computesIn`); the phases R0–R3 are ported in place (`R0.r0_spec`, `R1.r1_spec`,
  `R2.r2_spec`, `R3.r3_spec`).

See `GUIDE-SPACE.md` for porting a phase.
-/

@[expose] public section
