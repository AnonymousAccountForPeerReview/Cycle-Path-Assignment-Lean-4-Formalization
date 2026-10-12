module

public import ApproximationHardness.Embed.SolverForkRAM
import Mathlib.Tactic.NormNum

/-! # Ordering the two fork operands in constant-time RAM code -/

@[expose] public section

set_option maxHeartbeats 1500000

namespace STACS2027.Embed.RAMSolver

open RAM

def orderForkProgram : Stmt := seqs [.sub 30 29 25,
  .ifz 30 (seqs [.add 21 24 0, .add 24 28 0, .add 28 21 0,
    .add 21 25 0, .add 25 29 0, .add 29 21 0, .const 31 4]) (.const 31 3)]

theorem itemResultInto_reg_frame (c : Config) (typ value head low i : Nat)
    (hh : i ≠ head) (hl : i ≠ low) (ha : i ≠ 40) :
    (run (itemResultInto typ value head low) c).reg i = c.reg i := by
  by_cases ht : c.reg typ = 0 <;>
    simp [itemResultInto, loadCell, storeCell, run, seqs, ht, hh, hl, ha]

theorem orderForkProgram_raw (c : Config) (hz : c.reg 0 = 0) :
    let d := run orderForkProgram c
    d.reg 24 = (if c.reg 25 < c.reg 29 then c.reg 24 else c.reg 28) ∧
      d.reg 25 = (if c.reg 25 < c.reg 29 then c.reg 25 else c.reg 29) ∧
      d.reg 28 = (if c.reg 25 < c.reg 29 then c.reg 28 else c.reg 24) ∧
      d.reg 29 = (if c.reg 25 < c.reg 29 then c.reg 29 else c.reg 25) ∧
      d.reg 31 = (if c.reg 25 < c.reg 29 then 3 else 4) ∧
      (∀ i, i ≠ 21 → i ≠ 24 → i ≠ 25 → i ≠ 28 → i ≠ 29 → i ≠ 30 → i ≠ 31 → d.reg i = c.reg i) ∧
      d.mem = c.mem ∧ d.out = c.out := by
  by_cases hlt : c.reg 25 < c.reg 29
  · have hn : c.reg 29 - c.reg 25 ≠ 0 := by omega
    simp [orderForkProgram, run, seqs, hn, hlt, hz]
    intro i h₁ h₂ h₃ h₄ h₅ h₆ h₇
    simp [h₆, h₇]
  · have hn : c.reg 29 - c.reg 25 = 0 := by omega
    simp [orderForkProgram, run, seqs, hn, hlt, hz]
    intro i h₁ h₂ h₃ h₄ h₅ h₆ h₇
    simp [h₁, h₂, h₃, h₄, h₅, h₆, h₇]

theorem orderForkProgram_rep {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertices darts : Nat} (hr : Rep L c s) (ht : Tables L c S post vertices darts) :
    Rep L (run orderForkProgram c) s ∧ Tables L (run orderForkProgram c) S post vertices darts := by
  obtain ⟨_, _, _, _, _, hf, hm, _⟩ := orderForkProgram_raw c hr.bases.1
  refine ⟨hr.frame (by intro i hi; apply hf <;> omega)
    (by intro i hi; apply hf <;> omega) hm, ?_⟩
  exact ht.frame (hf 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hm]; exact TableMemEq.refl _ _)

theorem orderForkProgram_exec (bound : Nat) (c : Config) :
    ∃ t, ExecB bound orderForkProgram c t (run orderForkProgram c) ∧ t ≤ 30 := by
  have hl : LoopFree orderForkProgram := by simp [orderForkProgram, LoopFree, seqs]
  have ha : AddrOK bound orderForkProgram c := by simp [orderForkProgram, AddrOK, seqs]
  have hs : size orderForkProgram ≤ 30 := by norm_num [orderForkProgram, size, seqs]
  exact ⟨_, execB_run _ hl c ha, (cost_le_size _ _).trans hs⟩

theorem run_forkNodeProgram (c : Config) : run forkNodeProgram c = run forkResultProgram
    (run orderForkProgram (run (itemResultInto 26 27 28 29) (run (itemResultInto 22 23 24 25) c))) := by
  simp only [forkNodeProgram, orderForkProgram, run_seqs_cons, run_seqs_nil]

theorem forkResultProgram_addrOK {L : Layout} {c : Config} {s : SMS} {v : Nat}
    (hr : Rep L c s) (hv : v < L.width) (hnode : c.reg 20 = v) :
    AddrOK L.limit forkResultProgram c := by
  have hbase := hr.bases.2.2.2.2
  have h₆ : c.reg 56 + c.reg 20 < L.limit := by rw [hbase 6 (by decide), hnode]; exact L.cell_lt (by decide) hv
  have h₇ : c.reg 57 + c.reg 20 < L.limit := by rw [hbase 7 (by decide), hnode]; exact L.cell_lt (by decide) hv
  have h₁₀ : c.reg 60 + c.reg 20 < L.limit := by rw [hbase 10 (by decide), hnode]; exact L.cell_lt (by decide) hv
  have h₁₅ : c.reg 65 + c.reg 20 < L.limit := by rw [hbase 15 (by decide), hnode]; exact L.cell_lt (by decide) hv
  simp [forkResultProgram, storeNodeResult, beginForkProgram, loadCell, storeCell,
    AddrOK, run, seqs, h₆, h₇, h₁₀, h₁₅]

end STACS2027.Embed.RAMSolver
