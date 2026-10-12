module

public import Outerplanar.RAM.EarRecon
import Mathlib.Tactic

/-!
# The ear-elimination machine: the main theorem

`earProg_spec : EarSpec earProg CE` with `CE = 700`: on the local graph of `EarIn N L` (edges
smaller end first, ends below `N`, `N ≥ 3`) with an outerplanar Hamiltonian cycle through all of
`0, …, N - 1`, `earProg` stores `Ear.earHam N L` at the fresh array `gHAM` within
`700 (N + |L| + 1)` steps, touching only the addresses below `F + 700 (N + |L| + 1)` (`F` the
initial `rFREE`; the layout ends at `bEND F N |L| ≤ F + 21 (N + |L| + 1)`, `bEND_le`), allocating
fresh memory only and writing no output. The time: initialization and peeling
`70 N + 120 |L| + 75` (`init_spec`), the elimination loop `Φ + 6 ≤ 560 N + 48 |L| + 6`
(`mainLoop_spec`, `phi_init_le`), the reconstruction `63 N + 21` (`recon_spec`).

The hypothesis is used twice: the peeling, which takes linear time on every input, then orients
every edge (`Ear.peel_orient`), and the elimination's adjacency queries are answered by that
orientation (`Ear.query_static`, through the ghost invariants `Ear.Inv`, `Ear.Static` of
`Ear.inv_static_init`).

`earProg_wregs`: the program writes only `rT`, `rFREE`, `gHAM` and scratch registers;
`earProg_writes`: it has no `write` instruction.
-/

@[expose] public section

namespace STACS2027.RAM.EarR

open STACS2027 STACS2027.Ear

variable {S : ℕ}

/-- The reconstruction from the final state `Sf` of the elimination loop. -/
theorem recon_spec (N : ℕ) (L : List Edge) (F : ℕ) (m₀ : ℕ → ℕ) (Sf : State) (hN : 0 < N)
    (hG : Good N Sf) (hS : bEND F N L.length ≤ S) :
    HTB S recon (LRep N L F m₀ Sf)
      (RRep N L F m₀ Sf (Sf.log.foldl reinsert (succ0Of Sf N))
        (walk (Sf.log.foldl reinsert (succ0Of Sf N)) N ((triPre Sf N).getD 0 0)))
      (4 + ((N * (20 + 4) + 3) + (6 + ((N * (27 + 4) + 3) + (2 + (N * (4 + 4) + 3)))))) := by
  set x := (triPre Sf N).getD 0 0 with hx
  set succF := Sf.log.foldl reinsert (succ0Of Sf N) with hsuccF
  have hxN : x < N := getD_lt (triPre_lt Sf N) hN 0
  have hsucc0 : ∀ y, succ0Of Sf N y < N := fun y => by
    have := fun i => getD_lt (triPre_lt Sf N) hN i
    simp only [succ0Of, Function.update_apply]
    split_ifs <;> first | exact this _ | omega
  have hsuccF : ∀ y, succF y < N := foldl_reinsert_lt hsucc0 hG.log_lt
  have hlog : Sf.log.length ≤ N := by have := hG.log_len; omega
  have h0 : HTB S triInit (LRep N L F m₀ Sf) (fun c => TriInv N L F m₀ Sf 0 c ∧ c.reg gVN = N) 4 :=
    HTB.of_HT rfl (HT.run_le (by decide) (by decide) fun c hR => by
      refine ⟨⟨((LRep.indep N L F m₀ Sf).mono (by decide)).run (by decide) (by decide) (by decide)
        hR, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp +decide [triInit, triPre, hR.glob.vn])
  have h1 := HTB.forUpC (S := S) (i := rI) (n := gVN) (N := N) (body := triBody)
    (TriInv N L F m₀ Sf) 20 (by decide) (by decide) (by decide)
    (fun j => by indep [TriInv, lRep_iff, glob_iff]) (fun j hj => triBody_spec Sf hS j hj)
  have h2 := (succInit_spec (L := L) (F := F) (m₀ := m₀) Sf hN hS).pre
    (P' := fun c => TriInv N L F m₀ Sf N c ∧ c.reg rI = N ∧ c.reg gVN = N) fun c h => h.1
  have h3 := (HTB.forUpC (S := S) (i := rI) (n := rLC) (N := Sf.log.length) (body := reinsBody)
    (ReInv N L F m₀ Sf x) 27 (by decide) (by decide) (by decide)
    (fun j => by indep [ReInv, rRep_iff, glob_iff])
    (fun j hj => reinsBody_spec Sf hG x hS j hj)).pre
    (P' := fun c => RRep N L F m₀ Sf (succ0Of Sf N) [] c ∧ c.reg rX = x)
    fun c ⟨hR, hX⟩ => ⟨⟨by simpa using hR, hX⟩, hR.lc⟩
  have h4 : HTB S (mov rC rX) (fun c => ReInv N L F m₀ Sf x Sf.log.length c ∧
      c.reg rI = Sf.log.length ∧ c.reg rLC = Sf.log.length)
      (fun c => WInv N L F m₀ Sf succF x 0 c ∧ c.reg gVN = N) 2 :=
    HTB.of_HT rfl (HT.run_le (by decide) (by decide) fun c ⟨⟨hR, hX⟩, _, _⟩ => by
      rw [List.take_length] at hR
      rw [run_mov (by decide)]
      have hR' := (RRep.indep N L F m₀ Sf succF []).setReg (d := rC) (by decide) (c.reg rX)
        ((RRep.indep N L F m₀ Sf succF []).setReg (d := rT) (by decide) 0 hR)
      refine ⟨⟨by simpa using hR', ?_⟩, ?_⟩
      · simp +decide [hX]
      · simp +decide [hR.glob.vn])
  have h5 := HTB.forUpC (S := S) (i := rI) (n := gVN) (N := N) (body := walkBody)
    (WInv N L F m₀ Sf succF x) 4 (by decide) (by decide) (by decide)
    (fun j => by indep [WInv, rRep_iff, glob_iff])
    (fun j hj => walkBody_spec Sf succF hsuccF x hxN hS j hj)
  have h := h0.seq (h1.seq (h2.seq (h3.seq (h4.seq h5))))
  refine (h.post fun c hc => ?_).weaken ?_
  · obtain ⟨⟨hR, _⟩, _, _⟩ := hc
    rwa [List.take_of_length_le (by simp)] at hR
  · have := Nat.mul_le_mul_right (27 + 4) hlog
    omega

/-- The constant of the running time and of the space. -/
def CE : ℕ := 700

/-- The peeling's result is an orientation of `L` (under the hypothesis). -/
theorem outOK_of_peel {N : ℕ} {L : List Edge} {F : ℕ} {m : ℕ → ℕ}
    (hL : ∀ e ∈ L, e.1 < e.2 ∧ e.2 < N) (hnd : L.Nodup) {ham0 : List ℕ}
    (h0 : OuterplanarHam L ham0) (hv : ∀ v, v < N → v ∈ ham0) {p : PState}
    (hP : PInv N (initAdj L) p) (hs : p.stack = []) (h1 : Tab m (bO1 F N) N p.o1)
    (h2 : Tab m (bO2 F N) N p.o2) : OutOK N L F m := by
  intro a b ha hb hab
  rw [peel_orient hL hnd h0 hv hP hs ha hb hab, OutAdj, h1.get ha, h2.get ha, h1.get hb,
    h2.get hb, or_assoc]

/-- The program writes no output. -/
theorem earProg_writes : writes earProg = false := by
  have h1 : writes initProg = false := by decide
  have h2 : writes mainLoop = false := by decide
  have h3 : writes recon = false := by decide
  simp only [earProg, writes, h1, h2, h3, Bool.or_self]

/-- **The ear-elimination program** stores `Ear.earHam N L` at a fresh `gHAM` within
`CE * (N + |L| + 1)` steps and below the address `F + CE * (N + |L| + 1)`. -/
theorem earProg_spec : EarSpec earProg CE := by
  intro S N L c₀ hL hnd hN ⟨ham0, h0, hv⟩ hSb
  have hL' : ∀ e ∈ L, e.1 < N ∧ e.2 < N := fun e he => ⟨by have := hL e he; omega, (hL e he).2⟩
  set F := c₀.reg rFREE with hF
  have hend := bEND_le F N L.length
  have hS : bEND F N L.length ≤ S := by simp only [CE] at hSb; omega
  set Sf := loop (4 * N + 1) (init N L) with hSf
  have hGS : Good N Sf := good_loop (by omega) _ (good_init hL')
  have h1 := init_spec N L c₀ hL hnd hS
  have hphi := phi_init_le hL'
  have h23 : HTB S (.seq mainLoop recon)
      (fun c => LRep N L F c.mem (init N L) c ∧ SameOn (· < F) c₀.mem c.mem ∧
        ∃ p, PInv N (initAdj L) p ∧ p.stack = [] ∧ Tab c.mem (bO1 F N) N p.o1 ∧
          Tab c.mem (bO2 F N) N p.o2)
      (fun c => Arr c.mem (c.reg gHAM) (Ear.earHam N L) ∧ c.reg gHAM + N ≤ c.reg rFREE ∧
        SameOn (· < F) c₀.mem c.mem ∧ ZeroFrom c.mem (c.reg rFREE) ∧ F ≤ c.reg rFREE ∧
        c.reg rFREE ≤ F + CE * (N + L.length + 1))
      ((5 + (phi N (init N L) + 1)) +
        (4 + ((N * (20 + 4) + 3) + (6 + ((N * (27 + 4) + 3) + (2 + (N * (4 + 4) + 3))))))) := by
    refine HTB.of_forall fun c₁ ⟨hR₁, hlow, p, hP, hs, ho1, ho2⟩ => ?_
    have hO := outOK_of_peel hL hnd h0 hv hP hs ho1 ho2
    have hI0 : ∃ H, Inv N ham0 (init N L) H ∧ Static L (init N L) H :=
      ⟨ham0, inv_static_init hL hnd h0 hv⟩
    have h2 := mainLoop_spec N L F c₁.mem hN hL hI0 hO hS
    have h3 := recon_spec N L F c₁.mem Sf (by omega) hGS hS
    refine ((h2.seq h3).pre fun c hc => by subst hc; exact hR₁).post fun c hR => ?_
    rw [← earHam_eq] at hR
    refine ⟨by rw [hR.glob.ham]; exact hR.mem.hamA, by rw [hR.glob.ham, hR.glob.free]; lomega,
      hlow.trans (hR.mem.same.mono fun a (ha : a < F) => show a < bHD F N by lomega),
      by rw [hR.glob.free]; exact hR.mem.zero, by rw [hR.glob.free]; lomega,
      by rw [hR.glob.free]; simp only [CE]; omega⟩
  have h := (h1.seq h23).frame (F := fun c => c.out = c₀.out)
    fun c c' hfr ho => (hfr.out earProg_writes).trans ho
  refine h.mono (fun c ⟨hE, hc⟩ => ⟨⟨hE, hc⟩, by rw [hc]⟩)
    (fun c ⟨⟨hA, hH, hsame, hz, hle, hge⟩, ho⟩ => ⟨hA, hH, ho, hsame, hz, hle, hge⟩) ?_
  simp only [CE]
  omega

/-- The registers written by the program: `rT`, `rFREE`, `gHAM` and scratch registers. -/
theorem earProg_wregs : ∀ r ∈ wregs earProg, r = rT ∨ r = rFREE ∨ r = gHAM ∨ rS ≤ r := by
  have h1 : ∀ r ∈ wregs initProg, r = rT ∨ r = rFREE ∨ r = gHAM ∨ rS ≤ r := by
    have ha : ∀ r ∈ wregs allocs1, r = rT ∨ r = rFREE ∨ r = gHAM ∨ rS ≤ r := by decide
    have hb : ∀ r ∈ wregs allocs2, r = rT ∨ r = rFREE ∨ r = gHAM ∨ rS ≤ r := by decide
    have hc : ∀ r ∈ wregs (forUp rI gLN edgeBody), r = rT ∨ r = rFREE ∨ r = gHAM ∨ rS ≤ r := by
      decide
    have hd : ∀ r ∈ wregs (forUp rI gVN stkBody), r = rT ∨ r = rFREE ∨ r = gHAM ∨ rS ≤ r := by
      decide
    have he : ∀ r ∈ wregs peelProg, r = rT ∨ r = rFREE ∨ r = gHAM ∨ rS ≤ r := by decide
    intro r hr
    simp only [initProg, wregs_seq, List.mem_append] at hr
    rcases hr with ((hr | hr) | hr | hr) | hr
    exacts [ha r hr, hb r hr, hc r hr, hd r hr, he r hr]
  have h2 : ∀ r ∈ wregs mainLoop, r = rT ∨ r = rFREE ∨ r = gHAM ∨ rS ≤ r := by decide
  have h3 : ∀ r ∈ wregs recon, r = rT ∨ r = rFREE ∨ r = gHAM ∨ rS ≤ r := by decide
  intro r hr
  simp only [earProg, wregs_seq, List.mem_append] at hr
  rcases hr with hr | hr | hr
  exacts [h1 r hr, h2 r hr, h3 r hr]


end STACS2027.RAM.EarR
