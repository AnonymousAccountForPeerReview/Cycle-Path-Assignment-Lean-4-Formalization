module

public import ApproximationHardness.Embed.SolverNodeRAM
import Lean.Elab.Tactic.Omega

/-! Temporary-register frames and loop-free bounded execution facts. -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

/-- A write to the reserved scratch interval preserves the represented state. -/
theorem Rep.temp {L : Layout} {c : Config} {s : SMS} (hr : Rep L c s)
    (r v : Nat) (hlo : 20 ≤ r) (hhi : r < 50) : Rep L (c.setReg r v) s := by
  apply hr.frame
  · intro i hi; simp [show i ≠ r by omega]
  · intro i hi; simp [show i ≠ r by omega]
  · rfl

/-- A scratch-register write preserves the read-only formula tables. -/
theorem Tables.temp {L : Layout} {c : Config} {S : Sol} {post : List Nat} {vertices darts : Nat}
    (ht : Tables L c S post vertices darts) (r v : Nat) (hlo : 20 ≤ r) :
    Tables L (c.setReg r v) S post vertices darts := by
  apply ht.frame
  · simp [show 4 ≠ r by omega]
  · simp [show 5 ≠ r by omega]
  · exact TableMemEq.refl L c.mem

/-- A load into the reserved scratch interval preserves the represented scalar state. -/
theorem Rep.loadTemp {L : Layout} {c : Config} {s : SMS} (hr : Rep L c s)
    (r block index : Nat) (hlo : 20 ≤ r) (hhi : r < 40) :
    Rep L (run (loadCell r block index) c) s := by
  apply hr.frame
  · intro i hi; exact loadCell_frame c r block index i ⟨by omega, by omega⟩
  · intro i hi; exact loadCell_frame c r block index i ⟨by omega, by omega⟩
  · simp [loadCell, run, seqs]

/-- A scratch load preserves every formula table. -/
theorem Tables.loadTemp {L : Layout} {c : Config} {S : Sol} {post : List Nat} {vertices darts : Nat}
    (ht : Tables L c S post vertices darts) (r block index : Nat) (hlo : 20 ≤ r) :
    Tables L (run (loadCell r block index) c) S post vertices darts := by
  apply ht.frame
  · exact loadCell_frame c r block index 4 ⟨by omega, by decide⟩
  · exact loadCell_frame c r block index 5 ⟨by omega, by decide⟩
  · simp [loadCell, run, seqs]; exact TableMemEq.refl L c.mem

/-- A loop-free bounded execution certifies its deterministic run and actual address safety. -/
theorem boundedRun_addr {bound : Nat} {p : Stmt} {c d : Config} {t : Nat}
    (he : ExecB bound p c t d) : LoopFree p → d = run p c ∧ AddrOK bound p c := by
  induction he with
  | skip c => intro _; exact ⟨rfl, trivial⟩
  | const r v c => intro _; exact ⟨rfl, trivial⟩
  | add r a b c => intro _; exact ⟨rfl, trivial⟩
  | sub r a b c => intro _; exact ⟨rfl, trivial⟩
  | load r a c h => intro _; exact ⟨rfl, h⟩
  | store a r c h => intro _; exact ⟨rfl, h⟩
  | write r c => intro _; exact ⟨rfl, trivial⟩
  | seq h₁ h₂ ih₁ ih₂ =>
    intro hlp
    obtain ⟨hr₁, ha₁⟩ := ih₁ hlp.1
    obtain ⟨hr₂, ha₂⟩ := ih₂ hlp.2
    subst_vars
    exact ⟨rfl, ⟨ha₁, ha₂⟩⟩
  | ifzTrue hz he ih =>
    intro hlp
    obtain ⟨hr, ha⟩ := ih hlp.1
    refine ⟨?_, ?_⟩
    · simpa [run, hz] using hr
    · exact ⟨fun _ => ha, fun hn => False.elim (hn hz)⟩
  | ifzFalse hn he ih =>
    intro hlp
    obtain ⟨hr, ha⟩ := ih hlp.2
    refine ⟨?_, ?_⟩
    · simpa [run, hn] using hr
    · exact ⟨fun hz => False.elim (hn hz), fun _ => ha⟩
  | loopDone hz => intro hlp; exact False.elim hlp
  | loopNext hn he he' ih ih' => intro hlp; exact False.elim hlp

end STACS2027.Embed.RAMSolver
