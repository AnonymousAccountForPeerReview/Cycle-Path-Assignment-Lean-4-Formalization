module

public import ApproximationHardness.RAM.Decode.Paths
import Lean.Elab.Tactic.Omega

/-!
# The decoding program computes `decodeAssign`
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

/-- The step count of the decoding program. -/
def decCost (k : Nat) (f : CNF) (ps : List (List Edge)) : Nat :=
  passACost f + size scanPre + ((ps.map fun _ => size skipPath + 1).sum + 1) + size (tabPre k) +
    ((f.length + variableBound f) * ((4 + (gadgetWidth k * (size fillCell + 1) + 1) + 1) + 1) + 1) + size procPre +
    ((ps.map fun p => pathCost p + 1).sum + 1) + size outPre + (variableBound f * (size outBodyD + 1) + 1)

/-- The space of the decoding program: the input, the block and offset tables of the
`X = (m + n) w` vertices, and the three port counters of every variable. -/
def decSpace (k : Nat) (f : CNF) (ps : List (List Edge)) : Nat :=
  (decInput f ps).length + 2 * ((f.length + variableBound f) * gadgetWidth k) + 3 * variableBound f

/-- The vertices of the paths are below `S = (m + n) w`. -/
def PathsBelow (k : Nat) (f : CNF) (ps : List (List Edge)) : Prop :=
  ∀ p ∈ ps, ∀ e ∈ p, e.1 < (f.length + variableBound f) * gadgetWidth k ∧
    e.2 < (f.length + variableBound f) * gadgetWidth k

theorem decInput_getD_left (f : CNF) (ps : List (List Edge)) {i : Nat} (hi : i < (ramInput f).length) :
    (decInput f ps).getD i 0 = (ramInput f).getD i 0 := by
  simp only [decInput, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem decInput_getD_right (f : CNF) (ps : List (List Edge)) (i : Nat) :
    (decInput f ps).getD ((ramInput f).length + i) 0 = (pathsCode ps).getD i 0 := by
  simp only [decInput, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

/-! ### The output loop -/

/-- The invariant of the output loop after `j` variables. -/
def OutInvD (k : Nat) (ps : List (List Edge)) (Wb : Nat) (c0 : Config) (j : Nat) (c : Config) : Prop :=
  c.out = (List.range j).map (fun v => if decodeAssign k ps v then 1 else 0) ∧ c.reg DR.vi = j ∧ c.mem = c0.mem ∧
    c.reg DR.Wb = Wb ∧ c.reg Reg.one = 1 ∧ c.reg Reg.zero = 0

/-- One output step; it reads the counters `Wb + 3v + i` of the variable `v < n`. -/
theorem outBodyD_step (k : Nat) (ps : List (List Edge)) (Wb n : Nat) (c0 : Config)
    (hW : ∀ v i, v < n → i < 3 → c0.mem (Wb + 3 * v + i) = clauseLoad k ps v i) {SP : Nat} (hSP : Wb + 3 * n ≤ SP) :
    ∀ j c, j < n → OutInvD k ps Wb c0 j c → c.reg DR.v = n - j →
      ∃ t c', ExecB SP outBodyD c t c' ∧ t ≤ size outBodyD ∧ OutInvD k ps Wb c0 (j + 1) c' ∧
        c'.reg DR.v + 1 = c.reg DR.v := by
  intro j c hj ⟨ho, hvi, hm, hWb, hone, hzero⟩ hv
  obtain ⟨t, he, ht⟩ := exec_loopFree (S := SP) (s := outBodyD) (by simp [outBodyD, seqs, LoopFree]) c
    (by simp +decide [outBodyD, run, hvi, hWb, hone]; omega)
  have w0 := hW j 0 hj (by decide)
  have w1 := hW j 1 hj (by decide)
  have w2 := hW j 2 hj (by decide)
  refine ⟨t, _, he, ht, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp +decide only [outBodyD, run_seqs_cons, run_seqs_nil, run, setReg_reg, setReg_mem, setReg_out, emit_out,
      emit_reg, reg_ite, out_ite]
    simp +decide [hvi, hWb, hm, hone, hzero]
    rw [show j + j + j + Wb + 1 + 1 = Wb + 3 * j + 2 by omega, show j + j + j + Wb + 1 = Wb + 3 * j + 1 by omega,
      show j + j + j + Wb = Wb + 3 * j + 0 by omega, w0, w1, w2, ho, List.range_succ, List.map_append]
    unfold decodeAssign
    by_cases h : clauseLoad k ps j 1 + clauseLoad k ps j 2 ≤ clauseLoad k ps j 0
    · simp [h, show clauseLoad k ps j 1 + clauseLoad k ps j 2 - clauseLoad k ps j 0 = 0 by omega]
    · simp [h, show clauseLoad k ps j 1 + clauseLoad k ps j 2 - clauseLoad k ps j 0 ≠ 0 by omega]
  all_goals (simp +decide [outBodyD, run, hvi, hone, hm, hWb, hzero]; try omega)

theorem tabMem_at (w E : Nat) (M : Nat → Nat) (X x : Nat) (hx : x < X) :
    tabMem w E M X (E + x + x) = x / w ∧ tabMem w E M X (E + x + x + 1) = x % w := by
  unfold tabMem tabVal
  constructor
  · rw [ite_eq_left (by omega), show E + x + x - E = x + x by omega, ite_eq_left (by omega), show (x + x) / 2 = x by omega]
  · rw [ite_eq_left (by omega), show E + x + x + 1 - E = x + x + 1 by omega, ite_eq_right (by omega),
      show (x + x + 1) / 2 = x by omega]

theorem tabMem_out (w E : Nat) (M : Nat → Nat) (X a : Nat) (ha : a < E ∨ E + 2 * X ≤ a) :
    tabMem w E M X a = M a := by
  unfold tabMem; rw [ite_eq_right (by omega)]

theorem decInput_length (f : CNF) (ps : List (List Edge)) :
    (decInput f ps).length = (ramInput f).length + 1 + (ps.flatMap pathCode).length := by
  simp [decInput, pathsCode]; omega

theorem decInput_paths (f : CNF) (ps : List (List Edge)) (i : Nat) :
    (decInput f ps).getD ((ramInput f).length + 1 + i) 0 = (ps.flatMap pathCode).getD i 0 := by
  rw [show (ramInput f).length + 1 + i = (ramInput f).length + (i + 1) by omega, decInput_getD_right]
  simp [pathsCode]

/-- The decoding program computes `decOutput k f ps` within `decCost k f ps` steps and the space
`decSpace k f ps`. -/
theorem dec_computes (k : Nat) (f : CNF) (hf : ∀ c ∈ f, c.length ≤ 3) (ps : List (List Edge))
    (hb : PathsBelow k f ps) :
    ∃ t, ComputesIn (decProgram k) (decInput f ps) (decOutput k f ps) t (decSpace k f ps) ∧ t ≤ decCost k f ps := by
  have hw : 0 < gadgetWidth k := by have := gadgetWidth_ge k; omega
  have hL := decInput_length f ps
  have hLS : (decInput f ps).length ≤ decSpace k f ps := by unfold decSpace; omega
  -- the first pass
  have hc0 : HoldsInput f (initial (decInput f ps)) := fun i hi => decInput_getD_left f ps hi
  obtain ⟨t1, e1, ht1⟩ := sat_passAq f hf (S := decSpace k f ps) (by omega) _ ⟨hc0, rfl, rfl, rfl⟩
  have spec1 := passAqModel_spec f _ hc0 rfl rfl rfl
  dsimp only at spec1
  obtain ⟨a1m, a1o, a1one, a1zero, a1n, a1N, -, a1p⟩ := spec1
  generalize hc1 : passAqModel (initial (decInput f ps)) = c1 at e1 a1m a1o a1one a1zero a1n a1N a1p
  have hM : ∀ i, c1.mem i = (decInput f ps).getD i 0 := fun i => by rw [a1m]; rfl
  have hnps : (decInput f ps).getD (ramInput f).length 0 = ps.length := by
    have := decInput_getD_right f ps 0
    rw [Nat.add_zero] at this
    rw [this]; simp [pathsCode]
  have hm0 : (decInput f ps).getD 0 0 = f.length := by
    rw [decInput_getD_left f ps (by simp [ramInput])]; simp [ramInput]
  -- the number of paths
  obtain ⟨t2, e2, ht2⟩ := exec_loopFree (S := decSpace k f ps) (s := scanPre) (by simp [scanPre, seqs, LoopFree]) c1
    (by simp +decide [scanPre, run, a1p]; omega)
  generalize hc2 : run scanPre c1 = c2 at e2
  have a2np : c2.reg DR.np = ps.length := by
    rw [← hc2]; simp +decide [scanPre, run, a1p, hM]; simpa using hnps
  have a2p : c2.reg Reg.p = (ramInput f).length + 1 := by
    rw [← hc2]; simp +decide [scanPre, run, a1p, a1one]
  have a2m : c2.mem = c1.mem := by rw [← hc2]; exact run_mem_frame _ _ (by decide)
  have a2o : c2.out = c1.out := by rw [← hc2]; exact run_out_frame _ _ (by decide)
  have a2fr : ∀ r, r ≠ DR.np → r ≠ Reg.p → c2.reg r = c1.reg r := by
    intro r h1 h2; rw [← hc2]; exact run_reg_frame _ _ _ (by simp [scanPre, regsW, h1, h2])
  have hAt2 : At c2 (ps.flatMap pathCode) := by
    intro i _
    rw [a2m, hM, a2p, decInput_paths]
  -- skipping the paths
  obtain ⟨t3, c3, e3, ht3, hI3⟩ := exec_listPass pathCode ps (cnt := DR.np) (body := skipPath)
    (SkipInv ((ramInput f).length + 1) c2) (fun _ => size skipPath) (skip_step _ c2 ps (S := decSpace k f ps)
      (by omega)) c2
    ⟨by simp [a2p], rfl, rfl, by rw [a2fr _ (by decide) (by decide)]; exact a1one, fun _ _ _ _ _ => rfl⟩ a2np hAt2
  have ht3' : t3 ≤ (ps.map fun _ => size skipPath + 1).sum + 1 := ht3
  obtain ⟨a3p, a3m, a3o, a3one, a3fr⟩ := hI3
  have a3zero : c3.reg Reg.zero = 0 := by
    rw [a3fr _ (by decide) (by decide) (by decide) (by decide), a2fr _ (by decide) (by decide), a1zero]
  have a3n : c3.reg Reg.n = variableBound f := by
    rw [a3fr _ (by decide) (by decide) (by decide) (by decide), a2fr _ (by decide) (by decide), a1n]
  have a3N : c3.reg Reg.N = (ramInput f).length := by
    rw [a3fr _ (by decide) (by decide) (by decide) (by decide), a2fr _ (by decide) (by decide), a1N]
  have a3p' : c3.reg Reg.p = (decInput f ps).length := by rw [a3p, hL]
  have hM3 : ∀ i, c3.mem i = (decInput f ps).getD i 0 := fun i => by rw [a3m, a2m, hM]
  -- the tables
  obtain ⟨t4, e4, ht4⟩ := exec_loopFree (S := decSpace k f ps) (s := tabPre k) (by simp [tabPre, seqs, LoopFree]) c3
    (by simp +decide [tabPre, run]; omega)
  generalize hc4 : run (tabPre k) c3 = c4 at e4
  have a4E : c4.reg DR.E = (decInput f ps).length := by
    rw [← hc4]; simp +decide [tabPre, run, a3p', a3zero]
  have a4w : c4.reg DR.w = gadgetWidth k := by rw [← hc4]; simp +decide [tabPre, run]
  have a4nb : c4.reg DR.nb = f.length + variableBound f := by
    rw [← hc4]; simp +decide [tabPre, run, hM3, a3n]; simpa using hm0
  have a4x : c4.reg DR.x = 0 := by rw [← hc4]; simp +decide [tabPre, run]
  have a4bi : c4.reg DR.bi = 0 := by rw [← hc4]; simp +decide [tabPre, run]
  have a4m : c4.mem = c3.mem := by rw [← hc4]; exact run_mem_frame _ _ rfl
  have a4o : c4.out = c3.out := by rw [← hc4]; exact run_out_frame _ _ rfl
  have a4fr : ∀ r, r ≠ DR.E → r ≠ DR.w → r ≠ DR.addr → r ≠ DR.nb → r ≠ DR.x → r ≠ DR.bi → c4.reg r = c3.reg r := by
    intro r h1 h2 h3 h4 h5 h6; rw [← hc4]; exact run_reg_frame _ _ _ (by simp [tabPre, regsW, h1, h2, h3, h4, h5, h6])
  have a4one : c4.reg Reg.one = 1 := by
    rw [a4fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a3one]
  have a4zero : c4.reg Reg.zero = 0 := by
    rw [a4fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a3zero]
  obtain ⟨t5, c5, e5, ht5, hI5⟩ := exec_countLoop (a := DR.nb) (body := fillBlock) (f.length + variableBound f)
    (FillInv (gadgetWidth k) (decInput f ps).length c4.mem c4) (4 + (gadgetWidth k * (size fillCell + 1) + 1) + 1)
    (fun j c hj hI hc => fillBlock_exec _ _ _ c4 hw a4w a4E a4one a4zero (S := decSpace k f ps)
      (X := (f.length + variableBound f) * gadgetWidth k) (by unfold decSpace; omega) j
      (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj) c hI (by omega)) c4
    ⟨by rw [a4x, Nat.zero_mul], a4bi, by rw [Nat.zero_mul, tabMem_zero], rfl, fun _ _ => rfl⟩ a4nb
  have hSP : (decInput f ps).length + (f.length + variableBound f) * gadgetWidth k +
      (f.length + variableBound f) * gadgetWidth k + 3 * variableBound f = decSpace k f ps := by
    unfold decSpace; omega
  generalize hS : (f.length + variableBound f) * gadgetWidth k = S at hI5 hSP
  have a5x : c5.reg DR.x = S := by rw [hI5.x, hS]
  have a5m : c5.mem = tabMem (gadgetWidth k) (decInput f ps).length c4.mem S := by rw [hI5.mem, hS]
  have a5fr : ∀ r, FillFixed r → c5.reg r = c4.reg r := hI5.fixed
  have a5o : c5.out = [] := by rw [hI5.out, a4o, a3o, a2o, a1o]
  -- preparing the paths
  obtain ⟨t6, e6, ht6⟩ := exec_loopFree (S := decSpace k f ps) (s := procPre) (by simp [procPre, seqs, LoopFree]) c5
    (by
      have hN5' : c5.reg Reg.N = (ramInput f).length := by
        rw [a5fr _ (by decide), a4fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a3N]
      have hzero5' : c5.reg Reg.zero = 0 := by rw [a5fr _ (by decide), a4zero]
      simp +decide [procPre, run, hN5', hzero5']; omega)
  generalize hc6 : run procPre c5 = c6 at e6
  have hE5 : c5.reg DR.E = (decInput f ps).length := by rw [a5fr _ (by decide), a4E]
  have hN5 : c5.reg Reg.N = (ramInput f).length := by
    rw [a5fr _ (by decide), a4fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a3N]
  have hzero5 : c5.reg Reg.zero = 0 := by rw [a5fr _ (by decide), a4zero]
  have hone5 : c5.reg Reg.one = 1 := by rw [a5fr _ (by decide), a4one]
  have hn5 : c5.reg Reg.n = variableBound f := by
    rw [a5fr _ (by decide), a4fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a3n]
  have hnps5 : c5.mem (ramInput f).length = ps.length := by
    rw [a5m, tabMem_out _ _ _ _ _ (Or.inl (by omega)), a4m, hM3, hnps]
  have a6Wb : c6.reg DR.Wb = (decInput f ps).length + S + S := by
    rw [← hc6]; simp +decide [procPre, run, hE5, a5x]
  have a6p : c6.reg Reg.p = (ramInput f).length + 1 := by
    rw [← hc6]; simp +decide [procPre, run, hN5, hzero5, hone5]
  have a6np : c6.reg DR.np = ps.length := by
    rw [← hc6]; simp +decide [procPre, run, hN5, hzero5, hnps5]
  have a6m : c6.mem = c5.mem := by rw [← hc6]; exact run_mem_frame _ _ (by decide)
  have a6o : c6.out = [] := by rw [← hc6, run_out_frame _ _ (by decide), a5o]
  have a6fr : ∀ r, r ≠ DR.Wb → r ≠ Reg.p → r ≠ DR.np → c6.reg r = c5.reg r := by
    intro r h1 h2 h3; rw [← hc6]; exact run_reg_frame _ _ _ (by simp [procPre, regsW, h1, h2, h3])
  have a6E : c6.reg DR.E = (decInput f ps).length := by rw [a6fr _ (by decide) (by decide) (by decide), hE5]
  have a6one : c6.reg Reg.one = 1 := by rw [a6fr _ (by decide) (by decide) (by decide), hone5]
  have a6zero : c6.reg Reg.zero = 0 := by rw [a6fr _ (by decide) (by decide) (by decide), hzero5]
  have a6n : c6.reg Reg.n = variableBound f := by rw [a6fr _ (by decide) (by decide) (by decide), hn5]
  -- the paths
  generalize hM' : tabMem (gadgetWidth k) (decInput f ps).length c4.mem S = M' at a5m
  have hAt6 : At c6 (ps.flatMap pathCode) := by
    intro i hi
    have hlt : (ramInput f).length + 1 + i < (decInput f ps).length := by omega
    rw [a6m, a5m, a6p, ← hM', tabMem_out _ _ _ _ _ (Or.inl hlt), a4m, hM3, decInput_paths]
  let I7 : List (List Edge) → Config → Prop := fun pre c =>
    c.mem = wMem k M' ((decInput f ps).length + S + S) (variableBound f) pre ∧
      c.reg Reg.p = (ramInput f).length + 1 + (pre.flatMap pathCode).length ∧ c.out = [] ∧
      ∀ r, PathFixed r → c.reg r = c6.reg r
  have hstep7 : ∀ pre x suf c, pre ++ x :: suf = ps → I7 pre c → c.reg DR.np = suf.length + 1 →
      At c (pathCode x ++ suf.flatMap pathCode) →
      ∃ t c', ExecB (decSpace k f ps) pathBody c t c' ∧ t ≤ pathCost x ∧ I7 (pre ++ [x]) c' ∧
        c'.reg DR.np = suf.length ∧ At c' (suf.flatMap pathCode) := by
    intro pre x suf c hxs ⟨hm, hp, ho, hfr⟩ hnp hAt
    have hE : c.reg DR.E = (decInput f ps).length := by rw [hfr _ (by decide), a6E]
    have hlen : (pre.flatMap pathCode).length + (pathCode x ++ suf.flatMap pathCode).length =
        (ps.flatMap pathCode).length := by
      rw [← hxs]; simp [List.flatMap_append]
    obtain ⟨t, c', he, ht, hm', hp', hnp', hAt', ho', hfr'⟩ :=
      pathBody_step k S M' ((decInput f ps).length + S + S) (variableBound f) c pre x (suf.flatMap pathCode) hAt
        (by rw [hfr _ (by decide), a6one]) (by rw [hfr _ (by decide), a6zero])
        (fun y hy => by rw [hE, ← hM']; exact tabMem_at _ _ _ _ _ hy)
        (fun e he => by
          have hx : x ∈ ps := by rw [← hxs]; simp
          have := hb x hx e he
          rw [hS] at this; exact this)
        (by rw [hfr _ (by decide), a6Wb]) (by rw [hfr _ (by decide), a6n]) (by rw [hE]; exact Nat.le_refl _) hm
        (by rw [hp]; omega) (SP := decSpace k f ps) (by omega)
    refine ⟨t, c', he, ht, ⟨hm', ?_, by rw [ho', ho], fun r hr => by rw [hfr' r hr, hfr r hr]⟩, by omega, hAt'⟩
    rw [hp', hp]; simp [List.flatMap_append]; omega
  obtain ⟨t7, c7, e7, ht7, hI7⟩ := exec_listPass pathCode ps (cnt := DR.np) (body := pathBody) I7 pathCost hstep7 c6
    ⟨by funext a; simp [a6m, a5m, wMem, clauseLoad], by simp [a6p], a6o, fun _ _ => rfl⟩ a6np hAt6
  obtain ⟨a7m, -, a7o, a7fr⟩ := hI7
  -- the output
  obtain ⟨t8, e8, ht8⟩ := exec_loopFree (S := decSpace k f ps) (s := outPre) (by simp [outPre, seqs, LoopFree]) c7
    (AddrOK.of_memFree rfl)
  generalize hc8 : run outPre c7 = c8 at e8
  have a8v : c8.reg DR.v = variableBound f := by
    rw [← hc8]; simp +decide [outPre, run, a7fr _ (by decide : PathFixed Reg.n), a6n, a7fr _ (by decide : PathFixed Reg.zero), a6zero]
  have a8vi : c8.reg DR.vi = 0 := by rw [← hc8]; simp +decide [outPre, run]
  have a8m : c8.mem = c7.mem := by rw [← hc8]; exact run_mem_frame _ _ (by decide)
  have a8o : c8.out = [] := by rw [← hc8, run_out_frame _ _ (by decide), a7o]
  have a8fr : ∀ r, r ≠ DR.v → r ≠ DR.vi → c8.reg r = c7.reg r := by
    intro r h1 h2; rw [← hc8]; exact run_reg_frame _ _ _ (by simp [outPre, regsW, h1, h2])
  have hW : ∀ v i, v < variableBound f → i < 3 →
      c8.mem ((decInput f ps).length + S + S + 3 * v + i) = clauseLoad k ps v i := by
    intro v i hv hi
    rw [a8m, a7m]
    unfold wMem
    rw [ite_eq_left (by omega), ← hM', tabMem_out _ _ _ _ _ (Or.inr (by omega)), a4m, hM3,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none, Nat.zero_add,
      show (decInput f ps).length + S + S + 3 * v + i - ((decInput f ps).length + S + S) = 3 * v + i by omega,
      show (3 * v + i) / 3 = v by omega, show (3 * v + i) % 3 = i by omega]
  obtain ⟨t9, c9, e9, ht9, hI9⟩ := exec_countLoop (a := DR.v) (body := outBodyD) (variableBound f)
    (OutInvD k ps ((decInput f ps).length + S + S) c8) (size outBodyD)
    (outBodyD_step k ps _ _ c8 hW (SP := decSpace k f ps) (by omega)) c8
    ⟨by simp [a8o], a8vi, rfl, by rw [a8fr _ (by decide) (by decide), a7fr _ (by decide), a6Wb],
      by rw [a8fr _ (by decide) (by decide), a7fr _ (by decide), a6one],
      by rw [a8fr _ (by decide) (by decide), a7fr _ (by decide), a6zero]⟩ a8v
  refine ⟨t1 + (t2 + (t3 + (t4 + (t5 + (t6 + (t7 + (t8 + t9))))))), ⟨c9, ?_, hI9.1⟩, ?_⟩
  · exact ExecB.seq e1 (ExecB.seq e2 (ExecB.seq e3 (ExecB.seq e4 (ExecB.seq e5 (ExecB.seq e6 (ExecB.seq e7
      (ExecB.seq e8 e9)))))))
  · unfold decCost; omega

end STACS2027.RAM
