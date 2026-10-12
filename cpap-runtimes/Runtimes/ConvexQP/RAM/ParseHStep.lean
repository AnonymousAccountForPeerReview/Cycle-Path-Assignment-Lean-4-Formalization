module

public import Runtimes.ConvexQP.RAM.ParseHLoop
import Mathlib.Tactic

/-!
# Lemma 16 on the RAM, the parser: the phase `stepH`

`stepH_spec`: from the front end's `FrontPost g k (bD g k)` (`Sort/Front.lean`), the phase
`stepH` allocates `MARK` (at `bMK g k`, zero again at the end) and `H` (at `bH g k`, address in
`qBH`), and fills `H` with `hc g k a b (k − 2)`, in `O(N² k)` steps (`N = kt`), accessing only
addresses below any `S ≥ bEnd g k`. For a duplicate-free `g`, this is `HMem (instOf g k)`
(`hMem_of_HM`, by `Hflat_instOf`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Parse

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ConvexQP STACS2027.Runtimes.ZeroCost

variable {S : ℕ}

/-! ### Allocation and the registers of column `0` -/

/-- After the allocation of `MARK`. -/
def HA0 (g : Graph) (k : ℕ) (c : Config) : Prop :=
  GA g k c ∧ c.reg gEID = bEI g k ∧ c.reg hMK = bMK g k ∧ c.reg rFREE = bH g k ∧
    Tab c.mem (bEI g k) (nN g k) (eidOf g k) ∧ ZeroFrom c.mem (bMK g k) ∧ c.out = []

/-- After the allocation of `H`. -/
def HA1 (g : Graph) (k : ℕ) (c : Config) : Prop :=
  GA g k c ∧ c.reg gEID = bEI g k ∧ c.reg hMK = bMK g k ∧ c.reg qBH = bH g k ∧
    c.reg rFREE = bEnd g k ∧ Tab c.mem (bEI g k) (nN g k) (eidOf g k) ∧
    ZeroFrom c.mem (bMK g k) ∧ c.out = []

/-- The state after the front end, with an empty output. -/
def FP (g : Graph) (k : ℕ) (c : Config) : Prop := Sort.FrontPost g k (bD g k) c ∧ c.out = []

theorem hAlloc_spec (g : Graph) (k : ℕ) :
    HTB S hAlloc (FP g k) (HA1 g k) (3 + ((5 * (2 * nN g k) + 4) + 3)) := HTB.of_HT rfl <| by
  have a1 : HT (alloc hMK ZeroCost.gNE) (FP g k) (HA0 g k) 3 := by
    refine HT.run_le (by decide) (by decide) fun c ⟨hP, hout⟩ => ?_
    refine ⟨(show RegIndep [rT, hMK, rFREE] (GA g k) by indep [gA_iff]).run_of_sub (by decide)
      (by decide) hP.ga, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp +decide only [run_alloc (show ZeroCost.gNE ≠ rT by decide)
      (show hMK ≠ ZeroCost.gNE by decide), setReg_reg, setReg_mem, setReg_out, ↓reduceIte,
      hP.reid, hP.rfree, hP.rne, hout]
    all_goals first | rfl | exact hP.meid | exact hP.mzero
  have a2 := HT.mul (d := hSz) (a := gKT) (b := gNV) (k := hS) (x := nN g k) (y := 2 * nN g k)
    (P := HA0 g k) (by decide) (by indep [HA0, gA_iff]) (fun c h => h.1.rkt) (fun c h => h.1.rnv)
  have a3 : HT (alloc qBH hSz) (fun c => HA0 g k c ∧ c.reg hSz = nN g k * (2 * nN g k))
      (HA1 g k) 3 := by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨hga, he, hm, hf, ht, hz, ho⟩, hs⟩ => ?_
    refine ⟨(show RegIndep [rT, qBH, rFREE] (GA g k) by indep [gA_iff]).run_of_sub (by decide)
      (by decide) hga, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp +decide only [run_alloc (show hSz ≠ rT by decide) (show qBH ≠ hSz by decide),
      setReg_reg, setReg_mem, setReg_out, ↓reduceIte, he, hm, hf, hs, ho]
    · rfl
    · exact ht
    · exact hz
  exact a1.seq (a2.seq a3)

theorem hRegs_spec (g : Graph) (k : ℕ) : HTB S hRegs (HA1 g k) (OInv g k 0) 5 :=
    HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨hga, he, hm, hb, hf, ht, hz, ho⟩ => ?_
  have hL := hlayout g k
  have hreg : ∀ r, r ∉ wregs hRegs → (run hRegs c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) hr c
  have hmem : (run hRegs c).mem = c.mem := run_mem_of_stores (by decide) rfl c
  have hout : (run hRegs c).out = c.out := run_out_of_writes (by decide) rfl c
  refine ⟨⟨by rw [hreg gK (by decide), hga.rk], by rw [hreg gT (by decide), hga.rt],
    by rw [hreg gKT (by decide), hga.rkt], by rw [hreg gNV (by decide), hga.rnv],
    by rw [hreg gEID (by decide), he], by rw [hreg hMK (by decide), hm],
    by rw [hreg qBH (by decide), hb], by rw [hreg rFREE (by decide), hf], ?_⟩, ?_, ?_,
    by rw [hout, ho]⟩
  · simp +decide [hRegs, run_subc (show gK ≠ rT by decide), hga.rk]
  · rw [hmem]
    refine ⟨ht, hz.tab (le_refl _) _, fun a ha b hb' => ?_, hz.mono (by omega)⟩
    have h1 := hz (bH g k + a * (2 * nN g k) + 2 * b) (by omega)
    have h2 := hz (bH g k + a * (2 * nN g k) + 2 * b + 1) (by omega)
    refine ⟨h1, ?_⟩
    rw [h2]
    simp [hv]
  · refine ⟨?_, ?_, ?_⟩ <;> simp +decide [hRegs, run_subc (show gK ≠ rT by decide)]

/-- The cost of `stepH`. -/
def Th (g : Graph) (k : ℕ) : ℕ :=
  3 + ((5 * (2 * nN g k) + 4) + 3) + (5 + (nN g k * (Tout g k + 4) + 3))

/-- **The phase `stepH`**: `H` in memory, `MARK` zero again, below any `S ≥ bEnd g k`. -/
theorem stepH_spec (g : Graph) (k : ℕ) (hSp : bEnd g k ≤ S) :
    HTB S stepH (FP g k) (OInv g k (nN g k)) (Th g k) := by
  have h3 := (outerLoop_spec g k hSp).pre (fun c (h : OInv g k 0 c) => ⟨h, h.1.rkt⟩)
  exact ((hAlloc_spec g k).seq ((hRegs_spec g k).seq h3)).post fun c h => h.1

/-! ### `H` of the instance -/

theorem hv_full {g : Graph} {k a b : ℕ} (hb : b < nN g k) :
    hv g k (nN g k) 0 a b = hc g k a b (k - 2) := by
  simp [hv, hb]

/-- **`H` in memory**: after `stepH`, for a duplicate-free graph, `HMem (instOf g k)` at `bH g k`. -/
theorem hMem_of_HM {g : Graph} (hg : g.Nodup) {k : ℕ} {f : ℕ → ℕ} {m : ℕ → ℕ}
    (h : HM g k (hv g k (nN g k) 0) f m) : HMem (instOf g k) m (bH g k) := by
  have hN : (instOf g k).t * (instOf g k).k = nN g k := by simp [Nat.mul_comm]
  intro a ha j hj
  rw [hN] at ha hj
  have ha' : a < (cycles g k).length * k := by rw [Nat.mul_comm]; exact ha
  have hj' : j < (cycles g k).length * k := by rw [Nat.mul_comm]; exact hj
  obtain ⟨h0, h1⟩ := h.mh a ha j hj
  rw [hv_full hj] at h1
  rw [hN, Hflat_instOf hg ha' hj']
  unfold Arith.SMem
  rw [show bH g k + a * (2 * nN g k) + j * 2 = bH g k + a * (2 * nN g k) + 2 * j by ring, h0, h1]
  simp [Arith.sgnBit]

end STACS2027.Runtimes.QPRam.Parse
