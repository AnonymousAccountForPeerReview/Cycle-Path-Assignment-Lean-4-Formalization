module

public import Outerplanar.RAM.EarInit
import Mathlib.Tactic

/-!
# The ear-elimination machine: popping, the loop test, the scan of a list

* `pop_run`: popping `v` from the stack (`LRep` of the state with the rest of the stack, the
  popped vertex in `rV`, its dead flag in `rA`), its addresses `pop_addrOK`;
* `mcond_run`: the loop test `stack ≠ [] ∧ 3 < cnt` into `rT`;
* `scan_core`, `scan_spec`: the scan of the whole list `adj v` (a `while` loop over the nodes,
  `21 |adj v| + 7` steps) leaves the first two alive entries in `rU`, `rW` (`0` if missing),
  as `Ear.step` chooses them.

The triples are `HTB S` triples, for any bound `S ≥ bEND F N |L|` of the layout.
-/

@[expose] public section

namespace STACS2027.RAM.EarR

open STACS2027 STACS2027.Ear

variable {N : ℕ} {L : List Edge} {F : ℕ} {m₀ : ℕ → ℕ} {S : ℕ}

/-! ### Pop and the loop test -/

theorem pop_addrOK {s : State} {c : Config} (hR : LRep N L F m₀ s c) (hne : s.stack ≠ [])
    {v : ℕ} (hrv : c.mem (bSTK F N + (s.stack.length - 1)) = v) (hv : v < N)
    (hS : bEND F N L.length ≤ S) : AddrOK S pop c := by
  have hs := hR.mem.stkS
  have hl : 0 < s.stack.length := List.length_pos_of_ne_nil hne
  have hsp := hR.sp
  ear_addr [pop, hR.glob.stk, hR.glob.dead, hsp, hrv]

theorem pop_run {s : State} {v : ℕ} {rest : List ℕ} {c : Config} (hs : s.stack = v :: rest)
    (hR : LRep N L F m₀ s c) (hv : v < N) :
    LRep N L F m₀ { s with stack := rest } (run pop c) ∧ (run pop c).reg rV = v ∧
      ((run pop c).reg rA = 0 ↔ s.dead v = false) := by
  have hstk := hR.mem.stk
  rw [hs, List.reverse_cons] at hstk
  have hsp : c.reg rSP = rest.length + 1 := by rw [hR.sp, hs, List.length_cons]
  have hrv : c.mem (bSTK F N + rest.length) = v := by
    have := hstk.get (i := rest.length) (by simp)
    rw [this, List.getElem_append_right (by simp)]
    simp
  have hfr : ∀ r, r ∉ wregs pop → (run pop c).reg r = c.reg r := fun r hr =>
    run_reg_of_not_mem (by decide) hr c
  have hmem : (run pop c).mem = c.mem := run_mem_of_stores (by decide) (by decide) c
  have hV : (run pop c).reg rV = v := by
    simp +decide [pop, run_dec, hsp, hR.glob.stk, hrv]
  have hA : (run pop c).reg rA = if s.dead v = true then 1 else 0 := by
    simp +decide only [pop, run_seq', run_dec (show rSP ≠ rT by decide), run_ld, setReg_reg,
      ↓reduceIte, setReg_mem, hsp, Nat.add_sub_cancel, hR.glob.stk, hrv, hR.glob.dead,
      hR.mem.dead.get hv]
  refine ⟨⟨(Glob.regIndep _ _ _).run_of_sub (by decide) (by decide) hR.glob, ?_,
    (hfr rCNT (by decide)).trans hR.cnt, (hfr rLC (by decide)).trans hR.lc,
    by rw [hfr rNP (by decide)]; exact hR.np1, ?_, ?_⟩, hV, ?_⟩
  · simp +decide [pop, run_dec, hsp]
  · rw [hfr rNP (by decide)]; exact hR.npb
  · rw [hmem, hfr rNP (by decide)]; exact hR.mem.pop hs
  · rw [hA]; cases s.dead v <;> simp

theorem mcond_run {s : State} {c : Config} (hR : LRep N L F m₀ s c) :
    LRep N L F m₀ s (run mcond c) ∧ ((run mcond c).reg rT = 0 ↔ ¬ Running s) := by
  refine ⟨((LRep.indep N L F m₀ s).mono (by decide)).run (by decide) (by decide) (by decide) hR, ?_⟩
  simp +decide only [mcond, run_seq', run_const, run_sub, run_ifz', setReg_reg, ↓reduceIte,
    hR.sp, hR.cnt, Running, ne_eq]
  by_cases h : s.stack = []
  · simp [h]
  · have h' : s.stack.length ≠ 0 := fun e => h (List.length_eq_zero_iff.mp e)
    simp only [h', h, ↓reduceIte, not_false_eq_true, true_and, not_lt, run_skip, setReg_reg]
    omega

/-! ### The scan of a list -/

/-- The alive entries of a list. -/
def alive (dead : ℕ → Bool) (l : List ℕ) : List ℕ := l.filter fun x => dead x = false

theorem scanUpd_K (c : Config) : (run scanUpd c).reg rK = c.reg rK + 1 := by
  simp +decide only [scanUpd, run_seq', run_ifz', run_mov (show rX ≠ rT by decide),
    run_subc (show rK ≠ rT by decide), run_inc (show rK ≠ rT by decide), run_skip, setReg_reg,
    ↓reduceIte]
  split_ifs <;> simp +decide

theorem scanUpd_U (c : Config) :
    (run scanUpd c).reg rU = if c.reg rK = 0 then c.reg rX else c.reg rU := by
  simp +decide only [scanUpd, run_seq', run_ifz', run_mov (show rX ≠ rT by decide),
    run_subc (show rK ≠ rT by decide), run_inc (show rK ≠ rT by decide), run_skip, setReg_reg,
    ↓reduceIte]
  split_ifs <;> simp +decide

theorem scanUpd_W (c : Config) :
    (run scanUpd c).reg rW = if c.reg rK = 1 then c.reg rX else c.reg rW := by
  simp +decide only [scanUpd, run_seq', run_ifz', run_mov (show rX ≠ rT by decide),
    run_subc (show rK ≠ rT by decide), run_inc (show rK ≠ rT by decide), run_skip, setReg_reg,
    ↓reduceIte]
  split_ifs <;> simp +decide <;> omega

theorem scanUpd_reg (c : Config) {r : ℕ} (hr : r ∉ [rU, rW, rQ, rT, rK]) :
    (run scanUpd c).reg r = c.reg r := by
  have h : ∀ r ∈ wregs scanUpd, r ∈ [rU, rW, rQ, rT, rK] := by decide
  exact run_reg_of_not_mem (by decide) (fun h' => hr (h r h')) c

/-- The invariant of the scan after `j` entries of `l`. -/
def ScanInv (m : ℕ → ℕ) (Vb Xb D np : ℕ) (l : List ℕ) (dead : ℕ → Bool) (j : ℕ) (c : Config) :
    Prop :=
  c.mem = m ∧ c.reg rVAL = Vb ∧ c.reg rNXT = Xb ∧ c.reg rDEAD = D ∧ c.reg rZERO = 0 ∧
    j ≤ l.length ∧ LL m Vb Xb np (c.reg rP) (l.drop j) ∧ c.reg rT = c.reg rP ∧
    c.reg rK = (alive dead (l.take j)).length ∧ c.reg rU = (alive dead (l.take j)).getD 0 0 ∧
    c.reg rW = (alive dead (l.take j)).getD 1 0

theorem alive_take_succ (dead : ℕ → Bool) (l : List ℕ) (j : ℕ) (hj : j < l.length) :
    alive dead (l.take (j + 1)) =
      alive dead (l.take j) ++ (if dead l[j] = false then [l[j]] else []) := by
  rw [alive, filter_take_succ l _ j hj, alive]
  simp

theorem scanStep (m : ℕ → ℕ) {Vb Xb D np N : ℕ} {l : List ℕ} {dead : ℕ → Bool}
    (hd : Tab m D N (fun x => if dead x = true then 1 else 0)) (hlt : ∀ x ∈ l, x < N)
    (hVS : Vb + np ≤ S) (hXS : Xb + np ≤ S) (hDS : D + N ≤ S) (j : ℕ) :
    HTB S (.seq scanBody scanCond) (fun c => ScanInv m Vb Xb D np l dead j c ∧ c.reg rT ≠ 0)
      (ScanInv m Vb Xb D np l dead (j + 1)) 20 := by
  refine HTB.run_le (by decide) (by decide)
    fun c ⟨⟨hm, hV, hX, hD, hz, hj, hll, hT, hK, hU, hW⟩, hT0⟩ => ?_
  have hP0 : c.reg rP ≠ 0 := by rw [← hT]; exact hT0
  have hjl : j < l.length := by
    by_contra h
    rw [List.drop_eq_nil_of_le (by omega)] at hll
    exact hP0 hll
  rw [List.drop_eq_getElem_cons hjl] at hll
  obtain ⟨_, hpn, hval, hnext⟩ := hll
  have hx := hlt l[j] (List.getElem_mem hjl)
  have hdx : m (D + l[j]) = if dead l[j] = true then 1 else 0 := hd.get hx
  refine ⟨by addr_ok [scanBody, scanUpd, scanCond, hm, hV, hX, hD, hval], ?_⟩
  have hsucc := alive_take_succ dead l j hjl
  have hfr : ∀ r, r ∉ wregs (.seq scanBody scanCond) →
      (run (.seq scanBody scanCond) c).reg r = c.reg r := fun r hr => run_reg_of_not_mem (by decide) hr c
  have hmem : (run (.seq scanBody scanCond) c).mem = c.mem := run_mem_of_stores (by decide) (by decide) c
  obtain ⟨c₂, hc₂⟩ : ∃ c₂, c₂ = run (.seq (ld rX rVAL rP) (ld rQ rDEAD rX)) c := ⟨_, rfl⟩
  have hX2 : c₂.reg rX = l[j] := by rw [hc₂]; simp +decide [hm, hV, hval]
  have hQ2 : c₂.reg rQ = if dead l[j] = true then 1 else 0 := by
    rw [hc₂]; simp +decide [hm, hV, hval, hD, hdx]
  have hr2 : ∀ r, r ≠ rX → r ≠ rQ → c₂.reg r = c.reg r := fun r h1 h2 => by
    rw [hc₂]; simp [h1, h2]
  have hm2 : c₂.mem = m := by rw [hc₂]; simp [hm]
  obtain ⟨c₃, hc₃⟩ : ∃ c₃, c₃ = run (.ifz rQ scanUpd .skip) c₂ := ⟨_, rfl⟩
  have hc₃' : c₃ = if dead l[j] = false then run scanUpd c₂ else c₂ := by
    rw [hc₃, run_ifz', hQ2]; cases dead l[j] <;> simp
  have hr3 : ∀ r, r ∉ [rU, rW, rQ, rT, rK] → r ≠ rX → c₃.reg r = c.reg r := fun r h1 h2 => by
    have h3 : r ≠ rQ := by simp at h1; omega
    rw [hc₃']; split_ifs
    · rw [scanUpd_reg _ h1, hr2 r h2 h3]
    · exact hr2 r h2 h3
  have hm3 : c₃.mem = m := by
    rw [hc₃', ← hm2]; split_ifs
    · exact run_mem_of_stores (by decide) (by decide) c₂
    · rfl
  have hK3 : c₃.reg rK = c.reg rK + (if dead l[j] = false then 1 else 0) := by
    rw [hc₃']; cases dead l[j] <;> simp [scanUpd_K, hr2 rK (by decide) (by decide)]
  have hU3 : c₃.reg rU = if dead l[j] = false ∧ c.reg rK = 0 then l[j] else c.reg rU := by
    rw [hc₃']
    cases dead l[j] <;> simp [scanUpd_U, hr2 rK (by decide) (by decide), hX2,
      hr2 rU (by decide) (by decide)]
  have hW3 : c₃.reg rW = if dead l[j] = false ∧ c.reg rK = 1 then l[j] else c.reg rW := by
    rw [hc₃']
    cases dead l[j] <;> simp [scanUpd_W, hr2 rK (by decide) (by decide), hX2,
      hr2 rW (by decide) (by decide)]
  have hrun : run (.seq scanBody scanCond) c = run scanCond (run (ld rP rNXT rP) c₃) := by
    rw [hc₃, hc₂]; rfl
  have hP1 : (run (.seq scanBody scanCond) c).reg rP = m (Xb + c.reg rP) := by
    rw [hrun]
    simp +decide [scanCond, hm3, hr3 rNXT (by decide) (by decide), hr3 rP (by decide) (by decide), hX]
  have hT1 : (run (.seq scanBody scanCond) c).reg rT = (run (.seq scanBody scanCond) c).reg rP := by
    rw [hrun]
    simp +decide [scanCond, hr3 rZERO (by decide) (by decide), hz]
  have hK1 : (run (.seq scanBody scanCond) c).reg rK =
      c.reg rK + (if dead l[j] = false then 1 else 0) := by
    rw [hrun]; simp +decide [scanCond, hK3]
  have hU1 : (run (.seq scanBody scanCond) c).reg rU =
      if dead l[j] = false ∧ c.reg rK = 0 then l[j] else c.reg rU := by
    rw [hrun]; simp +decide [scanCond, hU3]
  have hW1 : (run (.seq scanBody scanCond) c).reg rW =
      if dead l[j] = false ∧ c.reg rK = 1 then l[j] else c.reg rW := by
    rw [hrun]; simp +decide [scanCond, hW3]
  have hK' : (alive dead (List.take j l)).length = c.reg rK := hK.symm
  refine ⟨hmem.trans hm, (hfr rVAL (by decide)).trans hV, (hfr rNXT (by decide)).trans hX,
    (hfr rDEAD (by decide)).trans hD, (hfr rZERO (by decide)).trans hz, by omega, ?_, hT1, ?_, ?_, ?_⟩
  · rw [hP1]; exact hnext
  · rw [hK1, hsucc]
    cases hdl : dead l[j] <;> simp [hK]
  · rw [hU1, hsucc]
    cases hdl : dead l[j]
    · simp only [true_and, ↓reduceIte, getD_snoc, hK']
      by_cases hk0 : c.reg rK = 0
      · simp [hk0]
      · simp [hk0, hU, Nat.pos_of_ne_zero hk0]
    · simp [hU]
  · rw [hW1, hsucc]
    cases hdl : dead l[j]
    · simp only [true_and, ↓reduceIte, getD_snoc, hK']
      by_cases hk0 : c.reg rK = 0
      · have h0 : alive dead (List.take j l) = [] := List.length_eq_zero_iff.mp (by omega)
        simp [hk0, hW, h0]
      · by_cases hk1 : c.reg rK = 1
        · simp [hk1]
        · have h2 : 1 < c.reg rK := by omega
          simp [hk1, hW, h2]
    · simp [hW]

/-- **The scan** of the whole list `l` (from the head of `v`): the first two alive entries. -/
theorem scan_core {m : ℕ → ℕ} {H Vb Xb D N np v : ℕ} {l : List ℕ} {dead : ℕ → Bool}
    (hl : LL m Vb Xb np (m (H + v)) l) (hd : Tab m D N (fun x => if dead x = true then 1 else 0))
    (hlt : ∀ x ∈ l, x < N) (hHS : H + v < S) (hVS : Vb + np ≤ S) (hXS : Xb + np ≤ S)
    (hDS : D + N ≤ S) :
    HTB S scan (fun c => c.mem = m ∧ c.reg rHD = H ∧ c.reg rVAL = Vb ∧ c.reg rNXT = Xb ∧
        c.reg rDEAD = D ∧ c.reg rV = v ∧ c.reg rZERO = 0)
      (fun c => c.reg rU = (alive dead l).getD 0 0 ∧ c.reg rW = (alive dead l).getD 1 0)
      (21 * l.length + 7) := by
  have hinit : HTB S scanInit (fun c => c.mem = m ∧ c.reg rHD = H ∧ c.reg rVAL = Vb ∧
      c.reg rNXT = Xb ∧ c.reg rDEAD = D ∧ c.reg rV = v ∧ c.reg rZERO = 0)
      (fun c => c.mem = m ∧ c.reg rVAL = Vb ∧ c.reg rNXT = Xb ∧ c.reg rDEAD = D ∧
        c.reg rZERO = 0 ∧ c.reg rP = m (H + v) ∧ c.reg rK = 0 ∧ c.reg rU = 0 ∧ c.reg rW = 0) 5 :=
    HTB.run_le (by decide) (by decide) fun c ⟨hm, hH, hV, hX, hD, hv, hz⟩ =>
      ⟨by addr_ok [scanInit, hH, hv], by simp +decide [scanInit, hm, hH, hV, hX, hD, hv, hz]⟩
  have hcond : HTB S scanCond (fun c => c.mem = m ∧ c.reg rVAL = Vb ∧ c.reg rNXT = Xb ∧
      c.reg rDEAD = D ∧ c.reg rZERO = 0 ∧ c.reg rP = m (H + v) ∧ c.reg rK = 0 ∧ c.reg rU = 0 ∧
      c.reg rW = 0) (ScanInv m Vb Xb D np l dead 0) 1 :=
    HTB.run_le (by decide) (by decide) fun c ⟨hm, hV, hX, hD, hz, hP, hK, hU, hW⟩ => by
      refine ⟨trivial, ?_⟩
      simp +decide only [ScanInv, scanCond, run_add, setReg_reg, setReg_mem, ↓reduceIte, hm, hV, hX,
        hD, hz, hP, hK, hU, hW, List.drop_zero, List.take_zero, Nat.add_zero, Nat.zero_le]
      exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, hl, trivial, by simp [alive],
        by simp [alive], by simp [alive]⟩
  have hloop := HTB.whileG (cond := scanCond) (body := scanBody) (ScanInv m Vb Xb D np l dead)
    (fun j => 21 * (l.length - j)) 0 hcond fun j c ⟨hI, hT0⟩ => by
      have hjl : j < l.length := by
        obtain ⟨_, _, _, _, _, hj, hll, hT, _⟩ := hI
        by_contra h
        rw [List.drop_eq_nil_of_le (by omega)] at hll
        exact hT0 (by rw [hT]; exact hll)
      exact HTB.toG (scanStep m hd hlt hVS hXS hDS j) (by omega) c ⟨hI, hT0⟩
  refine (hinit.seq hloop).mono (fun _ h => h) ?_ (by omega)
  rintro c ⟨j, ⟨_, _, _, _, _, hj, hll, hT, _, hU, hW⟩, hT0⟩
  have hjl : j = l.length := by
    rw [hT] at hT0
    rw [hT0] at hll
    have := hll.eq_zero_iff.mp rfl
    rw [List.drop_eq_nil_iff] at this
    omega
  subst hjl
  rw [List.take_length] at hU hW
  exact ⟨hU, hW⟩

/-- The scan on the machine state: `rU`, `rW` are the neighbours chosen by `Ear.step`. -/
theorem scan_spec {s : State} {v : ℕ} (hv : v < N) (hlt : ∀ x ∈ s.adj v, x < N)
    (hS : bEND F N L.length ≤ S) :
    HTB S scan (fun c => LRep N L F m₀ s c ∧ c.reg rV = v)
      (fun c => (LRep N L F m₀ s c ∧ c.reg rV = v) ∧ c.reg rU = (nbOf s v).getD 0 0 ∧
        c.reg rW = (nbOf s v).getD 1 0) (21 * (s.adj v).length + 7) := by
  have hF : Indep (wregs scan) (fun c => LRep N L F m₀ s c ∧ c.reg rV = v) :=
    ((LRep.indep N L F m₀ s).mono (by decide)).and (Indep.reg (r := rV) (by decide) (· = v))
  refine HTB.of_forall fun c₀ ⟨hR, hv₀⟩ => ?_
  have hnp := hR.mem.npS
  have hcore := scan_core (S := S) (m := c₀.mem) (H := bHD F N) (Vb := bVAL F N)
    (Xb := bNXT F N L.length) (D := bDEAD F N) (np := c₀.reg rNP) (v := v) (dead := s.dead)
    (hR.mem.adj v hv) hR.mem.dead hlt (by lomega) (by lomega) (by lomega) (by lomega)
  have := (hcore.frameIndep (by decide) (by decide) hF).pre (P' := fun c => c = c₀)
    fun c hc => by
      subst hc
      exact ⟨⟨rfl, hR.glob.hd, hR.glob.val, hR.glob.nxt, hR.glob.dead, hv₀, hR.glob.zero⟩, hR, hv₀⟩
  exact this.post fun c ⟨⟨hU, hW⟩, hF⟩ => ⟨hF, hU, hW⟩

end STACS2027.RAM.EarR
