module

public import Runtimes.ConvexQP.RAM.ParseH
import Mathlib.Tactic

/-!
# Lemma 16 on the RAM, the parser: the overlap matrix `H` (blocks, loops)

The specifications of the loop-free blocks of `stepH` (`markBody_spec`, `cntBody_spec`,
`advA_spec`, `advB_spec`, `innerInit_spec`), the walks (`markWalk_spec`, `cntWalk_spec`) and the
two loops over the flat indices (`innerLoop_spec`, `outerBody_spec`, `outerLoop_spec`), as
`HTB S` triples for every bound `S ≥ bEnd g k` (`hSp`; the accesses are to `EID`, `MARK` and `H`,
`hfits`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Parse

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ConvexQP STACS2027.Runtimes.ZeroCost

variable {S : ℕ}

/-! ### The walks -/

theorem markBody_spec (g : Graph) (k b : ℕ) (F : ℕ → ℕ → ℕ) (f : ℕ → ℕ) (v s : ℕ)
    (hSp : bEnd g k ≤ S) (hb : b < nN g k) (hs : s < k - 2) :
    HTB S markBody (fun c => WInv g k b F f v s c ∧ c.reg hS = s ∧ c.reg hK2 = k - 2)
      (fun c => WInv g k b F f v (s + 1) c ∧ c.reg hS = s ∧ c.reg hK2 = k - 2) 11 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hM, hBR, ho, hv, hp⟩, hs', hk2⟩ => ?_
  have hk : 0 < k := by omega
  have hb' : b < (cycles g k).length * k := by rw [Nat.mul_comm]; exact hb
  have hq : occ k b s < nN g k := occ_lt hb' s
  have he : eidOf g k (occ k b s) < nE g k := eidOf_lt hq
  have hrd : c.mem (bEI g k + occ k b s) = eidOf g k (occ k b s) := hM.meid.get hq
  refine ⟨by
    have hf := hfits g k hSp
    have hq' : b / k * k + opos k (b % k) s < nN g k := hq
    have hrd' : c.mem (bEI g k + (b / k * k + opos k (b % k) s)) = eidOf g k (occ k b s) := hrd
    addr_ok [markBody, nextP, hG.reid, hG.rmk, hBR.2.1, hp, hrd'], ?_⟩
  have hreg : ∀ r, r ∉ wregs markBody → (run markBody c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) hr c
  have hmem : (run markBody c).mem = upd c.mem (bMK g k + eidOf g k (occ k b s)) v := by
    simp +decide only [markBody, run_seq', run_add, run_ld, run_st (show hV ≠ rT by decide),
      run_nextP, setReg_mem, setMem_mem_upd, setReg_reg, ↓reduceIte, hG.reid, hG.rmk, hBR.2.1,
      hp, hv]
    rw [show b / k * k + opos k (b % k) s = occ k b s from rfl, hrd]
  have hpp : (run markBody c).reg hP = opos k (b % k) (s + 1) := by
    simp +decide only [markBody, run_seq', run_add, run_ld, run_st (show hV ≠ rT by decide),
      run_nextP, setReg_reg, setMem_reg, ↓reduceIte, hp, hG.rk]
    rw [opos_succ hk]
  have hout : (run markBody c).out = c.out := run_out_of_writes (by decide) rfl c
  refine ⟨⟨(HG.regIndep g k).run_of_sub (by decide) (by decide) hG, ?_, ?_, by rw [hout, ho],
    by rw [hreg hV (by decide), hv], hpp⟩, by rw [hreg hS (by decide), hs'],
    by rw [hreg hK2 (by decide), hk2]⟩
  · rw [hmem, mk_succ]; exact hM.mark he v
  · obtain ⟨h1, h2, h3⟩ := hBR
    exact ⟨by rw [hreg hJB (by decide), h1], by rw [hreg hCB (by decide), h2],
      by rw [hreg hCol (by decide), h3]⟩

/-- The cost of a mark walk. -/
def Tmw (k : ℕ) : ℕ := 8 + ((k - 2) * 15 + 3)

/-- **The mark walk**: `MARK[EID[occ b s]] := v` for `s < k − 2`. -/
theorem markWalk_spec (g : Graph) (k b : ℕ) (F : ℕ → ℕ → ℕ) (f : ℕ → ℕ) (v : ℕ)
    (hSp : bEnd g k ≤ S) (hb : b < nN g k) :
    HTB S markWalk (fun c => HG g k c ∧ HM g k F f c.mem ∧ BR k b c ∧ c.out = [] ∧ c.reg hV = v)
      (WInv g k b F f v (k - 2)) (Tmw k) := by
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by simp [nN, h] at hb
  have h0 : HTB S (startP hJB)
      (fun c => HG g k c ∧ HM g k F f c.mem ∧ BR k b c ∧ c.out = [] ∧ c.reg hV = v)
      (fun c => WInv g k b F f v 0 c ∧ c.reg hK2 = k - 2) 8 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨hG, hM, hBR, ho, hv⟩ => ?_
    have hreg : ∀ r, r ∉ wregs (startP hJB) → (run (startP hJB) c).reg r = c.reg r :=
      fun r hr => run_reg_of_not_mem (by decide) hr c
    have hmem : (run (startP hJB) c).mem = c.mem := run_mem_of_stores (by decide) rfl c
    have hout : (run (startP hJB) c).out = c.out := run_out_of_writes (by decide) rfl c
    obtain ⟨h1, h2, h3⟩ := hBR
    refine ⟨⟨(HG.regIndep g k).run_of_sub (by decide) (by decide) hG, by
      rw [hmem, mk_zero]; exact hM, ⟨by rw [hreg hJB (by decide), h1],
      by rw [hreg hCB (by decide), h2], by rw [hreg hCol (by decide), h3]⟩, by rw [hout, ho],
      by rw [hreg hV (by decide), hv], ?_⟩, by rw [hreg hK2 (by decide), hG.rk2]⟩
    simp +decide only [run_startP (show hJB ≠ rT by decide), setReg_reg, ↓reduceIte, hG.rk, h1]
    rw [opos_zero (Nat.mod_lt _ hk)]
  have hl := HTB.forUpC (i := hS) (n := hK2) (N := k - 2) (body := markBody) (WInv g k b F f v)
    11 (by decide) (by decide) (by decide) (fun s => by indep [WInv, hG_iff, BR])
    (fun s hs => markBody_spec g k b F f v s hSp hb hs)
  exact (h0.seq hl).mono (fun _ h => h) (fun c ⟨h, _, _⟩ => h) (by unfold Tmw; omega)

theorem cntBody_spec (g : Graph) (k b a s : ℕ) (hSp : bEnd g k ≤ S) (ha : a < nN g k)
    (hs : s < k - 2) :
    HTB S cntBody (fun c => CInv g k b a s c ∧ c.reg hS = s ∧ c.reg hK2 = k - 2)
      (fun c => CInv g k b a (s + 1) c ∧ c.reg hS = s ∧ c.reg hK2 = k - 2) 12 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hI, hp, hcnt⟩, hs', hk2⟩ => ?_
  obtain ⟨hG, hM, hBR, ho, hJ, hC, hR⟩ := hI
  have hk : 0 < k := by omega
  have ha' : a < (cycles g k).length * k := by rw [Nat.mul_comm]; exact ha
  have hq : occ k a s < nN g k := occ_lt ha' s
  have he : eidOf g k (occ k a s) < nE g k := eidOf_lt hq
  have hrd : c.mem (bEI g k + occ k a s) = eidOf g k (occ k a s) := hM.meid.get hq
  have hmk : c.mem (bMK g k + eidOf g k (occ k a s)) = mark g k b (eidOf g k (occ k a s)) :=
    hM.mmark.get he
  refine ⟨by
    have hf := hfits g k hSp
    have hq' : a / k * k + opos k (a % k) s < nN g k := hq
    have hrd' : c.mem (bEI g k + (a / k * k + opos k (a % k) s)) = eidOf g k (occ k a s) := hrd
    addr_ok [cntBody, nextP, hG.reid, hG.rmk, hC, hp, hrd'], ?_⟩
  have hreg : ∀ r, r ∉ wregs cntBody → (run cntBody c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) hr c
  have hmem : (run cntBody c).mem = c.mem := run_mem_of_stores (by decide) rfl c
  have hout : (run cntBody c).out = c.out := run_out_of_writes (by decide) rfl c
  have hpp : (run cntBody c).reg hP = opos k (a % k) (s + 1) := by
    simp +decide only [cntBody, run_seq', run_add, run_ld, run_nextP, setReg_reg, ↓reduceIte, hp,
      hG.rk]
    rw [opos_succ hk]
  have hcc : (run cntBody c).reg hCnt = hc g k a b (s + 1) := by
    simp +decide only [cntBody, run_seq', run_add, run_ld, run_nextP, setReg_reg, setReg_mem,
      ↓reduceIte, hp, hG.reid, hG.rmk, hC, hcnt]
    rw [show a / k * k + opos k (a % k) s = occ k a s from rfl, hrd, hmk, hc_succ]
  refine ⟨⟨⟨(HG.regIndep g k).run_of_sub (by decide) (by decide) hG, by rw [hmem]; exact hM, ?_,
    by rw [hout, ho], ?_, ?_, ?_⟩, hpp, hcc⟩, by rw [hreg hS (by decide), hs'],
    by rw [hreg hK2 (by decide), hk2]⟩
  · obtain ⟨h1, h2, h3⟩ := hBR
    exact ⟨by rw [hreg hJB (by decide), h1], by rw [hreg hCB (by decide), h2],
      by rw [hreg hCol (by decide), h3]⟩
  · rw [hreg hJA (by decide), hJ]
  · rw [hreg hCA (by decide), hC]
  · rw [hreg hRow (by decide), hR]

/-- The cost of a count walk. -/
def Tcw (k : ℕ) : ℕ := 1 + (8 + ((k - 2) * 16 + 3))

/-- **The count walk** of row `a`: `hCnt = Σ_{s<k−2} MARK[EID[occ a s]]`. -/
theorem cntWalk_spec (g : Graph) (k b a : ℕ) (hSp : bEnd g k ≤ S) (ha : a < nN g k) :
    HTB S cntWalk (IInv g k b a) (CInv g k b a (k - 2)) (Tcw k) := by
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by simp [nN, h] at ha
  have h0 : HTB S (.seq (.const hCnt 0) (startP hJA)) (IInv g k b a)
      (fun c => CInv g k b a 0 c ∧ c.reg hK2 = k - 2) 9 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c hI => ?_
    obtain ⟨hG, hM, hBR, ho, hJ, hC, hR⟩ := hI
    set s := Stmt.seq (.const hCnt 0) (startP hJA)
    have hreg : ∀ r, r ∉ wregs s → (run s c).reg r = c.reg r :=
      fun r hr => run_reg_of_not_mem (by decide) hr c
    have hmem : (run s c).mem = c.mem := run_mem_of_stores (by decide) rfl c
    have hout : (run s c).out = c.out := run_out_of_writes (by decide) rfl c
    obtain ⟨h1, h2, h3⟩ := hBR
    refine ⟨⟨⟨(HG.regIndep g k).run_of_sub (by decide) (by decide) hG, by rw [hmem]; exact hM,
      ⟨by rw [hreg hJB (by decide), h1], by rw [hreg hCB (by decide), h2],
        by rw [hreg hCol (by decide), h3]⟩, by rw [hout, ho], by rw [hreg hJA (by decide), hJ],
      by rw [hreg hCA (by decide), hC], by rw [hreg hRow (by decide), hR]⟩, ?_, ?_⟩,
      by rw [hreg hK2 (by decide), hG.rk2]⟩
    · simp +decide only [s, run_seq', run_const, run_startP (show hJA ≠ rT by decide), setReg_reg,
        ↓reduceIte, hG.rk, hJ]
      rw [opos_zero (Nat.mod_lt _ hk)]
    · simp +decide only [s, run_seq', run_const, run_startP (show hJA ≠ rT by decide), setReg_reg,
        ↓reduceIte, hc_zero]
  have hl := HTB.forUpC (i := hS) (n := hK2) (N := k - 2) (body := cntBody) (CInv g k b a) 12
    (by decide) (by decide) (by decide) (fun s => by indep [CInv, IInv, hG_iff, BR, AR])
    (fun s hs => cntBody_spec g k b a s hSp ha hs)
  exact HTB.assoc ((h0.seq hl).mono (fun _ h => h) (fun c ⟨h, _, _⟩ => h) (by unfold Tcw; omega))

/-! ### The inner loop -/

theorem hv_succ {g : Graph} {k b a : ℕ} {a' b' : ℕ} :
    (if a' = a ∧ b' = b then hc g k a b (k - 2) else hv g k b a a' b') = hv g k b (a + 1) a' b' := by
  unfold hv
  by_cases h : a' = a ∧ b' = b
  · obtain ⟨rfl, rfl⟩ := h; simp
  · simp only [h, ↓reduceIte]
    have e : (b' < b ∨ b' = b ∧ a' < a) ↔ (b' < b ∨ b' = b ∧ a' < a + 1) := by
      constructor
      · rintro (h1 | ⟨h1, h2⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨h1, by omega⟩
      · rintro (h1 | ⟨h1, h2⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨h1, by
            rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h3 | h3
            · exact h3
            · exact absurd ⟨h3, h1⟩ h⟩
    simp only [e]

/-- `H[a][b] := hCnt`, then the registers of `a + 1`. -/
theorem advA_spec (g : Graph) (k b a : ℕ) (hSp : bEnd g k ≤ S) (hb : b < nN g k)
    (ha : a < nN g k) :
    HTB S advA (CInv g k b a (k - 2)) (IInv g k b (a + 1)) 13 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hI, _, hcnt⟩ => ?_
  obtain ⟨hG, hM, hBR, ho, hJ, hC, hR⟩ := hI
  refine ⟨by
    have hf := hfits g k hSp
    have hc := hcell_lt ha hb
    addr_ok [advA, hR, hBR.2.2], ?_⟩
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by simp [nN, h] at ha
  have hreg : ∀ r, r ∉ wregs advA → (run advA c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) hr c
  have hout : (run advA c).out = c.out := run_out_of_writes (by decide) rfl c
  obtain ⟨hidx1, hidx2⟩ := idx_succ (a := a) hk
  have hmem : (run advA c).mem =
      upd c.mem (bH g k + a * (2 * nN g k) + 2 * b + 1) (hc g k a b (k - 2)) := by
    simp +decide only [advA, run_seq', run_add, run_store, run_inc (show hJA ≠ rT by decide),
      run_ifEq (show hJA ≠ rT by decide) (show gK ≠ rT by decide), run_const, run_skip,
      setReg_mem, setMem_mem_upd, setReg_reg, setMem_reg, ↓reduceIte, config_ite_mem, hR, hBR.2.2,
      hcnt, ite_self]
    congr 1
  have hrow : (run advA c).reg hRow = bH g k + (a + 1) * (2 * nN g k) := by
    simp +decide only [advA, run_seq', run_add, run_store, run_inc (show hJA ≠ rT by decide),
      run_ifEq (show hJA ≠ rT by decide) (show gK ≠ rT by decide), run_const, run_skip,
      setReg_reg, setMem_reg, ↓reduceIte, config_ite_reg, hR, hG.rnv, ite_self]
    ring
  have hja : (run advA c).reg hJA = (a + 1) % k ∧ (run advA c).reg hCA = (a + 1) / k * k := by
    by_cases hj : a % k + 1 = k
    · obtain ⟨e1, e2⟩ := hidx1 hj
      simp +decide only [advA, run_seq', run_add, run_store, run_inc (show hJA ≠ rT by decide),
        run_ifEq (show hJA ≠ rT by decide) (show gK ≠ rT by decide), run_const,
        setReg_reg, setMem_reg, ↓reduceIte, hJ, hG.rk, hj, hC, e1, e2]
    · obtain ⟨e1, e2⟩ := hidx2 hj
      simp +decide only [advA, run_seq', run_add, run_store, run_inc (show hJA ≠ rT by decide),
        run_ifEq (show hJA ≠ rT by decide) (show gK ≠ rT by decide), run_skip,
        setReg_reg, setMem_reg, ↓reduceIte, hJ, hG.rk, hj, hC, e1, e2]
  refine ⟨(HG.regIndep g k).run_of_sub (by decide) (by decide) hG, ?_, ?_, by rw [hout, ho],
    hja.1, hja.2, hrow⟩
  · rw [hmem]
    exact (hM.hset ha hb _).congrH fun a' _ b' _ => hv_succ
  · obtain ⟨h1, h2, h3⟩ := hBR
    exact ⟨by rw [hreg hJB (by decide), h1], by rw [hreg hCB (by decide), h2],
      by rw [hreg hCol (by decide), h3]⟩

/-- The cost of one row of the inner loop. -/
def Tin (k : ℕ) : ℕ := Tcw k + 13

/-- **The inner loop**: every row `a` of column `b`. -/
theorem innerLoop_spec (g : Graph) (k b : ℕ) (hSp : bEnd g k ≤ S) (hb : b < nN g k) :
    HTB S (forUp hA gKT innerBody) (fun c => IInv g k b 0 c ∧ c.reg gKT = nN g k)
      (fun c => IInv g k b (nN g k) c ∧ c.reg hA = nN g k ∧ c.reg gKT = nN g k)
      (nN g k * (Tin k + 4) + 3) :=
  HTB.forUpC (i := hA) (n := gKT) (N := nN g k) (body := innerBody) (IInv g k b) (Tin k)
    (by decide) (by decide) (by decide) (fun a => by indep [IInv, hG_iff, BR, AR])
    (fun a ha => ((cntWalk_spec g k b a hSp ha).seq (advA_spec g k b a hSp hb ha)).frameReg
      (F := fun c => c.reg hA = a ∧ c.reg gKT = nN g k) (by indep))

/-! ### The outer loop -/

theorem hv_last {g : Graph} {k b a' b' : ℕ} (ha' : a' < nN g k) :
    hv g k b (nN g k) a' b' = hv g k (b + 1) 0 a' b' := by
  unfold hv
  have e : (b' < b ∨ b' = b ∧ a' < nN g k) ↔ (b' < b + 1 ∨ b' = b + 1 ∧ a' < 0) := by omega
  simp only [e]

/-- The registers of `b + 1`, after unmarking. -/
theorem advB_spec (g : Graph) (k b : ℕ) (hb : b < nN g k) :
    HTB S advB (fun c => WInv g k b (hv g k b (nN g k)) (mark g k b) 0 (k - 2) c)
      (OInv g k (b + 1)) 12 := HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨hG, hM, hBR, ho, _, _⟩ => ?_
  obtain ⟨hJ, hC, hL⟩ := hBR
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by simp [nN, h] at hb
  have hmem : (run advB c).mem = c.mem := run_mem_of_stores (by decide) rfl c
  have hout : (run advB c).out = c.out := run_out_of_writes (by decide) rfl c
  obtain ⟨hidx1, hidx2⟩ := idx_succ (a := b) hk
  have hcol : (run advB c).reg hCol = 2 * (b + 1) + 1 := by
    simp +decide only [advB, run_seq', run_addc (show hCol ≠ rT by decide),
      run_inc (show hJB ≠ rT by decide),
      run_ifEq (show hJB ≠ rT by decide) (show gK ≠ rT by decide), run_const, run_add, run_skip,
      setReg_reg, ↓reduceIte, config_ite_reg, hL, ite_self]
    ring
  have hjb : (run advB c).reg hJB = (b + 1) % k ∧ (run advB c).reg hCB = (b + 1) / k * k := by
    by_cases hj : b % k + 1 = k
    · obtain ⟨e1, e2⟩ := hidx1 hj
      simp +decide only [advB, run_seq', run_addc (show hCol ≠ rT by decide),
        run_inc (show hJB ≠ rT by decide),
        run_ifEq (show hJB ≠ rT by decide) (show gK ≠ rT by decide), run_const, run_add,
        setReg_reg, ↓reduceIte, hJ, hG.rk, hj, hC, e1, e2]
    · obtain ⟨e1, e2⟩ := hidx2 hj
      simp +decide only [advB, run_seq', run_addc (show hCol ≠ rT by decide),
        run_inc (show hJB ≠ rT by decide),
        run_ifEq (show hJB ≠ rT by decide) (show gK ≠ rT by decide), run_skip,
        setReg_reg, ↓reduceIte, hJ, hG.rk, hj, hC, e1, e2]
  refine ⟨(HG.regIndep g k).run_of_sub (by decide) (by decide) hG, ?_, ⟨hjb.1, hjb.2, hcol⟩,
    by rw [hout, ho]⟩
  rw [hmem]
  exact (hM.congrM (mk_unmark b)).congrH fun a' ha' b' _ => hv_last ha'

/-- The registers of row `0`. -/
theorem innerInit_spec (g : Graph) (k b : ℕ) :
    HTB S innerInit (fun c => WInv g k b (hv g k b 0) (fun _ => 0) 1 (k - 2) c) (IInv g k b 0) 4 :=
    HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨hG, hM, hBR, ho, _, _⟩ => ?_
  have hreg : ∀ r, r ∉ wregs innerInit → (run innerInit c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) hr c
  have hmem : (run innerInit c).mem = c.mem := run_mem_of_stores (by decide) rfl c
  have hout : (run innerInit c).out = c.out := run_out_of_writes (by decide) rfl c
  obtain ⟨h1, h2, h3⟩ := hBR
  refine ⟨(HG.regIndep g k).run_of_sub (by decide) (by decide) hG, by rw [hmem]; exact hM,
    ⟨by rw [hreg hJB (by decide), h1], by rw [hreg hCB (by decide), h2],
      by rw [hreg hCol (by decide), h3]⟩, by rw [hout, ho], ?_, ?_, ?_⟩
  · simp +decide [innerInit, run_mov (show qBH ≠ rT by decide)]
  · simp +decide [innerInit, run_mov (show qBH ≠ rT by decide)]
  · simp +decide [innerInit, run_mov (show qBH ≠ rT by decide), hG.rbh]

/-- The cost of one column of the outer loop. -/
def Tout (g : Graph) (k : ℕ) : ℕ :=
  1 + (Tmw k + (4 + ((nN g k * (Tin k + 4) + 3) + (1 + (Tmw k + 12)))))

/-- **One column `b`**: mark option `b`, count every row against it, unmark. -/
theorem outerBody_spec (g : Graph) (k b : ℕ) (hSp : bEnd g k ≤ S) (hb : b < nN g k) :
    HTB S outerBody (OInv g k b) (OInv g k (b + 1)) (Tout g k) := by
  have s1 : HTB S (.const hV 1) (OInv g k b)
      (fun c => HG g k c ∧ HM g k (hv g k b 0) (fun _ => 0) c.mem ∧ BR k b c ∧ c.out = [] ∧
        c.reg hV = 1) 1 := HTB.of_HT rfl <|
    HT.run_le (by decide) (by decide) fun c ⟨hG, hM, hBR, ho⟩ =>
      ⟨(HG.regIndep g k).setReg (by decide) _ hG, hM,
        (show Indep [hV] (BR k b) by indep [BR]).setReg (by decide) _ hBR, ho, by simp⟩
  have s5 : HTB S (.const hV 0)
      (fun c => IInv g k b (nN g k) c ∧ c.reg hA = nN g k ∧ c.reg gKT = nN g k)
      (fun c => HG g k c ∧ HM g k (hv g k b (nN g k)) (mark g k b) c.mem ∧ BR k b c ∧
        c.out = [] ∧ c.reg hV = 0) 1 := HTB.of_HT rfl <|
    HT.run_le (by decide) (by decide) fun c ⟨⟨hG, hM, hBR, ho, _⟩, _⟩ =>
      ⟨(HG.regIndep g k).setReg (by decide) _ hG, hM,
        (show Indep [hV] (BR k b) by indep [BR]).setReg (by decide) _ hBR, ho, by simp⟩
  have s2 := markWalk_spec g k b (hv g k b 0) (fun _ => 0) 1 hSp hb
  have s3 := innerInit_spec (S := S) g k b
  have s4 := (innerLoop_spec g k b hSp hb).pre (fun c (h : IInv g k b 0 c) => ⟨h, h.1.rkt⟩)
  have s6 := markWalk_spec g k b (hv g k b (nN g k)) (mark g k b) 0 hSp hb
  have s7 := advB_spec (S := S) g k b hb
  exact s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq s7)))))

/-- **The outer loop**: every column `b`. -/
theorem outerLoop_spec (g : Graph) (k : ℕ) (hSp : bEnd g k ≤ S) :
    HTB S (forUp hB gKT outerBody) (fun c => OInv g k 0 c ∧ c.reg gKT = nN g k)
      (fun c => OInv g k (nN g k) c ∧ c.reg hB = nN g k ∧ c.reg gKT = nN g k)
      (nN g k * (Tout g k + 4) + 3) :=
  HTB.forUpC (i := hB) (n := gKT) (N := nN g k) (body := outerBody) (OInv g k) (Tout g k)
    (by decide) (by decide) (by decide) (fun b => by indep [OInv, hG_iff, BR])
    (fun b hb => (outerBody_spec g k b hSp hb).frameReg
      (F := fun c => c.reg hB = b ∧ c.reg gKT = nN g k) (by indep))

end STACS2027.Runtimes.QPRam.Parse
