module

public import ApproximationHardness.RAM.Decode.Tables
import Lean.Elab.Tactic.Omega

/-!
# The decoding program: reading an edge
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

/-- The block and offset tables are valid for the vertices below `S`. -/
def TablesAt (w E S : Nat) (c : Config) : Prop :=
  ∀ x, x < S → c.mem (E + x + x) = x / w ∧ c.mem (E + x + x + 1) = x % w

/-- The registers `readEdge` writes. -/
abbrev EdgeScratch (r : Nat) : Prop :=
  r ≠ DR.cnt ∧ r ≠ DR.ex ∧ r ≠ DR.ey ∧ r ≠ Reg.p ∧ r ≠ DR.addr ∧ r ≠ DR.bx ∧ r ≠ DR.bY

theorem readEdge_run (w E S : Nat) (c : Config) (e : Edge) (rest : List Nat) (hAt : At c (edgeCode e ++ rest))
    (hone : c.reg Reg.one = 1) (hE : c.reg DR.E = E) (hT : TablesAt w E S c) (h1 : e.1 < S) (h2 : e.2 < S) :
    let d := run (seqs readEdge) c
    d.reg DR.ex = e.1 ∧ d.reg DR.ey = e.2 ∧ d.reg DR.bx = e.1 / w ∧ d.reg DR.bY = e.2 / w ∧
      d.reg Reg.p = c.reg Reg.p + 2 ∧ d.reg DR.cnt = c.reg DR.cnt - 1 ∧ d.mem = c.mem ∧ d.out = c.out ∧
      At d rest ∧ ∀ r, EdgeScratch r → d.reg r = c.reg r := by
  have g0 := hAt.getD (i := 0) (by simp [edgeCode])
  have g1 := hAt.getD (i := 1) (by simp [edgeCode])
  simp only [edgeCode, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at g0 g1
  have t1 := (hT e.1 h1).1
  have t2 := (hT e.2 h2).1
  intro d
  have hmem : d.mem = c.mem := run_mem_frame _ _ (by decide)
  have hp : d.reg Reg.p = c.reg Reg.p + 2 := by
    simp +decide [d, readEdge, blkOf, run, hone]; try omega
  refine ⟨?_, ?_, ?_, ?_, hp, ?_, hmem, run_out_frame _ _ (by decide), ?_, ?_⟩
  · simp +decide [d, readEdge, blkOf, run, hone, g0]
  · simp +decide [d, readEdge, blkOf, run, hone, g1]
  · simp +decide [d, readEdge, blkOf, run, hone, g0, g1, hE, t1]
  · simp +decide [d, readEdge, blkOf, run, hone, g0, g1, hE, t2]
  · simp +decide [d, readEdge, blkOf, run, hone]
  · exact hAt.drop hmem (by rw [hp]; simp [edgeCode])
  · intro r ⟨a1, a2, a3, a4, a5, a6, a7⟩
    exact run_reg_frame _ _ _ (by simp [readEdge, blkOf, regsW, a1, a2, a3, a4, a5, a6, a7])

/-- `readEdge` reads the two cells of the edge at `p` and the block cells `E + 2x` of its ends. -/
theorem readEdge_addrOK {SP : Nat} (E X : Nat) (c : Config) (e : Edge) (rest : List Nat)
    (hAt : At c (edgeCode e ++ rest)) (hone : c.reg Reg.one = 1) (hE : c.reg DR.E = E) (h1 : e.1 < X)
    (h2 : e.2 < X) (hp : c.reg Reg.p + 2 ≤ SP) (hS : E + X + X ≤ SP) : AddrOK SP (seqs readEdge) c := by
  have g0 := hAt.getD (i := 0) (by simp [edgeCode])
  have g1 := hAt.getD (i := 1) (by simp [edgeCode])
  simp only [edgeCode, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at g0 g1
  simp +decide [readEdge, blkOf, run, hone, hE, g0, g1]
  omega

/-! ### The flag pass -/

theorem flagIfNe_run (c : Config) (r : Nat) (hr : r ≠ DR.t ∧ r ≠ DR.t2 ∧ r ≠ DR.flag) :
    (run (seqs (flagIfNe r)) c).reg DR.flag = if c.reg r ≠ c.reg DR.b0 then 1 else c.reg DR.flag := by
  obtain ⟨a1, a2, a3⟩ := hr
  simp +decide [flagIfNe, run, a1]
  by_cases h : c.reg r = c.reg DR.b0 <;> simp [h] <;> omega

theorem flagEdge_run (w E S : Nat) (c : Config) (e : Edge) (rest : List Nat) (hAt : At c (edgeCode e ++ rest))
    (hone : c.reg Reg.one = 1) (hE : c.reg DR.E = E) (hT : TablesAt w E S c) (h1 : e.1 < S) (h2 : e.2 < S) :
    let d := run flagEdge c
    (d.reg DR.flag = if e.1 / w ≠ c.reg DR.b0 ∨ e.2 / w ≠ c.reg DR.b0 then 1 else c.reg DR.flag) ∧
      d.reg Reg.p = c.reg Reg.p + 2 ∧ d.reg DR.cnt = c.reg DR.cnt - 1 ∧ d.mem = c.mem ∧ d.out = c.out ∧
      At d rest ∧ ∀ r, EdgeScratch r → r ≠ DR.t → r ≠ DR.t2 → r ≠ DR.flag → d.reg r = c.reg r := by
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10⟩ := readEdge_run w E S c e rest hAt hone hE hT h1 h2
  generalize hd : run (seqs readEdge) c = d1 at x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
  have hrun : run flagEdge c = run (seqs (flagIfNe DR.bY)) (run (seqs (flagIfNe DR.bx)) d1) := by
    rw [← hd]; simp only [flagEdge, run_seqs_app]
  intro d
  have hfrA : ∀ r, r ≠ DR.t → r ≠ DR.t2 → r ≠ DR.flag → (run (seqs (flagIfNe DR.bx)) d1).reg r = d1.reg r :=
    fun r a b d' => run_reg_frame _ _ _ (by simp [flagIfNe, regsW, a, b, d'])
  have hfrB : ∀ r, r ≠ DR.t → r ≠ DR.t2 → r ≠ DR.flag →
      (run (seqs (flagIfNe DR.bY)) (run (seqs (flagIfNe DR.bx)) d1)).reg r = d1.reg r :=
    fun r a b d' => (run_reg_frame _ _ _ (by simp [flagIfNe, regsW, a, b, d'])).trans (hfrA r a b d')
  have hmA : (run (seqs (flagIfNe DR.bx)) d1).mem = d1.mem := run_mem_frame _ _ (by decide)
  have hmB : (run (seqs (flagIfNe DR.bY)) (run (seqs (flagIfNe DR.bx)) d1)).mem = d1.mem :=
    (run_mem_frame _ _ (by decide)).trans hmA
  have hb0 : d1.reg DR.b0 = c.reg DR.b0 := x10 _ (by decide)
  have hfl : d1.reg DR.flag = c.reg DR.flag := x10 _ (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (run flagEdge c).reg DR.flag = _
    rw [hrun, flagIfNe_run _ _ (by decide), flagIfNe_run _ _ (by decide)]
    rw [hfrA _ (by decide) (by decide) (by decide), hfrA _ (by decide) (by decide) (by decide), x3, x4, hb0, hfl]
    by_cases ha : e.1 / w = c.reg DR.b0 <;> by_cases hb : e.2 / w = c.reg DR.b0 <;> simp [ha, hb]
  · show (run flagEdge c).reg Reg.p = _
    rw [hrun, hfrB _ (by decide) (by decide) (by decide), x5]
  · show (run flagEdge c).reg DR.cnt = _
    rw [hrun, hfrB _ (by decide) (by decide) (by decide), x6]
  · show (run flagEdge c).mem = _
    rw [hrun, hmB, x7]
  · show (run flagEdge c).out = _
    rw [hrun, run_out_frame _ _ (by decide), run_out_frame _ _ (by decide), x8]
  · show At (run flagEdge c) rest
    rw [hrun]
    exact At.of_mem x9 (hfrB _ (by decide) (by decide) (by decide)) (fun i _ => by rw [hmB])
  · intro r hr a b d'
    show (run flagEdge c).reg r = _
    rw [hrun, hfrB r a b d', x10 r hr]

theorem flagEdge_addrOK {SP : Nat} (E X : Nat) (c : Config) (e : Edge) (rest : List Nat)
    (hAt : At c (edgeCode e ++ rest)) (hone : c.reg Reg.one = 1) (hE : c.reg DR.E = E) (h1 : e.1 < X)
    (h2 : e.2 < X) (hp : c.reg Reg.p + 2 ≤ SP) (hS : E + X + X ≤ SP) : AddrOK SP flagEdge c :=
  AddrOK.append_memFree (AddrOK.append_memFree (readEdge_addrOK E X c e rest hAt hone hE h1 h2 hp hS) rfl) rfl

/-! ### Counting the port edges -/

theorem portInc_mem (c : Config) (i a b : Nat) (hone : c.reg Reg.one = 1) :
    (run (portInc i a b) c).mem = if c.reg DR.ox = a ∧ c.reg DR.oy = b then
      (fun x => if x = c.reg DR.Wb + 3 * c.reg DR.bx + i then c.mem x + 1 else c.mem x) else c.mem := by
  simp only [portInc, run_seqs_cons, run_seqs_nil, run]
  by_cases ha : c.reg DR.ox = a <;> by_cases hb : c.reg DR.oy = b
  · simp +decide [ha, hb, hone]
    have haddr : c.reg DR.bx + c.reg DR.bx + c.reg DR.bx + c.reg DR.Wb + i = c.reg DR.Wb + 3 * c.reg DR.bx + i := by
      omega
    rw [haddr]
    funext x
    by_cases hx : x = c.reg DR.Wb + 3 * c.reg DR.bx + i <;> simp [hx]
  all_goals (simp +decide [ha, hb, hone]; all_goals (intros; omega))

theorem portInc_frame (c : Config) (i a b r : Nat) (h : r ≠ DR.z1 ∧ r ≠ DR.z2 ∧ r ≠ DR.z3 ∧ r ≠ DR.addr) :
    (run (portInc i a b) c).reg r = c.reg r :=
  run_reg_frame _ _ _ (by simp [portInc, regsW, h.1, h.2.1, h.2.2.1, h.2.2.2])

theorem portEdgeG_iff (k v i : Nat) (hi : i < 3) (e : Edge) :
    e = portEdgeG k v i ↔ e.1 / gadgetWidth k = v ∧ e.2 / gadgetWidth k = v ∧
      e.1 % gadgetWidth k = (variablePortEdge i).1 ∧ e.2 % gadgetWidth k = (variablePortEdge i).2 := by
  have hw := gadgetWidth_ge k
  have hlt := variablePortEdge_lt i
  have hord : (variablePortEdge i).1 < (variablePortEdge i).2 := by
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl <;> decide
  have hpe : portEdgeG k v i = (v * gadgetWidth k + (variablePortEdge i).1, v * gadgetWidth k + (variablePortEdge i).2) := by
    rw [portEdgeG_eq]; unfold blockVertex edge
    rw [Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)]
  rw [hpe]
  obtain ⟨x, y⟩ := e
  simp only [Prod.mk.injEq]
  have hw0 : 0 < gadgetWidth k := by omega
  constructor
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw0, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw0, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  · rintro ⟨h1, h2, h3, h4⟩
    constructor
    · rw [← h1, ← h3, Nat.mul_comm]; exact (Nat.div_add_mod x _).symm
    · rw [← h2, ← h4, Nat.mul_comm]; exact (Nat.div_add_mod y _).symm

theorem portInc_mem' (c : Config) (i a b x : Nat) (hone : c.reg Reg.one = 1) :
    (run (portInc i a b) c).mem x = c.mem x +
      (if c.reg DR.ox = a ∧ c.reg DR.oy = b ∧ x = c.reg DR.Wb + 3 * c.reg DR.bx + i then 1 else 0) := by
  rw [portInc_mem c i a b hone]
  by_cases h : c.reg DR.ox = a ∧ c.reg DR.oy = b
  · rw [ite_eq_left h]
    by_cases hx : x = c.reg DR.Wb + 3 * c.reg DR.bx + i
    · simp [hx, h]
    · simp [hx]
  · rw [ite_eq_right h]
    have : ¬ (c.reg DR.ox = a ∧ c.reg DR.oy = b ∧ x = c.reg DR.Wb + 3 * c.reg DR.bx + i) :=
      fun h' => h ⟨h'.1, h'.2.1⟩
    simp [this]

theorem offOf_run (c : Config) (r d : Nat) (hr : r ≠ DR.addr) (_hd : d ≠ DR.addr) (hone : c.reg Reg.one = 1) :
    (run (seqs (offOf r d)) c).reg d = c.mem (c.reg DR.E + c.reg r + c.reg r + 1) := by
  simp +decide [offOf, run, hr, hone]

theorem offOf_frame (c : Config) (r d q : Nat) (h1 : q ≠ DR.addr) (h2 : q ≠ d) :
    (run (seqs (offOf r d)) c).reg q = c.reg q := run_reg_frame _ _ _ (by simp [offOf, regsW, h1, h2])

theorem variablePortEdge_cases {i : Nat} (hi : i < 3) :
    variablePortEdge i = if i = 0 then (2, 6) else if i = 1 then (4, 5) else (0, 3) := by
  have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl | rfl <;> decide

/-- The registers the count pass leaves alone. -/
abbrev CountFixed (r : Nat) : Prop := EdgeScratch r ∧ r ≠ DR.t ∧ r ≠ DR.t2 ∧ r ≠ DR.ox ∧ r ≠ DR.oy ∧
  r ≠ DR.z1 ∧ r ≠ DR.z2 ∧ r ≠ DR.z3

theorem countEdge_run (k S : Nat) (c : Config) (e : Edge) (rest : List Nat) (hAt : At c (edgeCode e ++ rest))
    (hone : c.reg Reg.one = 1) (hT : TablesAt (gadgetWidth k) (c.reg DR.E) S c) (h1 : e.1 < S) (h2 : e.2 < S)
    (_hWb : c.reg DR.E + S + S ≤ c.reg DR.Wb) :
    let d := run countEdge c
    (d.mem = fun a => c.mem a + (if c.reg DR.Wb ≤ a ∧ a < c.reg DR.Wb + 3 * c.reg Reg.n ∧
        e = portEdgeG k ((a - c.reg DR.Wb) / 3) ((a - c.reg DR.Wb) % 3) then 1 else 0)) ∧
      d.reg Reg.p = c.reg Reg.p + 2 ∧ d.reg DR.cnt = c.reg DR.cnt - 1 ∧ d.out = c.out ∧
      ∀ r, CountFixed r → d.reg r = c.reg r := by
  have hw := gadgetWidth_ge k
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, -, x10⟩ := readEdge_run (gadgetWidth k) (c.reg DR.E) S c e rest hAt hone rfl hT h1 h2
  generalize hd1 : run (seqs readEdge) c = d1 at x1 x2 x3 x4 x5 x6 x7 x8 x10
  let tail : Stmt := Stmt.ifz DR.t (Stmt.seq (Stmt.sub DR.t2 Reg.n DR.bx) (Stmt.ifz DR.t2 Stmt.skip
      (seqs (offOf DR.ex DR.ox ++ offOf DR.ey DR.oy ++ [portInc 0 2 6, portInc 1 4 5, portInc 2 0 3])))) Stmt.skip
  have hrun : run countEdge c = run tail (run (seqs [Stmt.sub DR.t DR.bx DR.bY, Stmt.sub DR.t2 DR.bY DR.bx,
      Stmt.add DR.t DR.t DR.t2]) d1) := by
    rw [← hd1]; simp only [countEdge, run_seqs_app]; rfl
  let d2 := run (seqs [Stmt.sub DR.t DR.bx DR.bY, Stmt.sub DR.t2 DR.bY DR.bx, Stmt.add DR.t DR.t DR.t2]) d1
  have d2t : d2.reg DR.t = (e.1 / gadgetWidth k - e.2 / gadgetWidth k) + (e.2 / gadgetWidth k - e.1 / gadgetWidth k) := by
    simp +decide [d2, run, x3, x4]
  have d2fr : ∀ r, r ≠ DR.t → r ≠ DR.t2 → d2.reg r = d1.reg r := by intro r a b; simp [d2, run, a, b]
  have d2m : d2.mem = c.mem := by rw [← x7]; rfl
  have d2o : d2.out = c.out := by rw [← x8]; rfl
  -- the common frame of the tail
  have tailfr : ∀ r, r ≠ DR.t2 → r ≠ DR.addr → r ≠ DR.ox → r ≠ DR.oy → r ≠ DR.z1 → r ≠ DR.z2 → r ≠ DR.z3 →
      (run tail d2).reg r = d2.reg r := by
    intro r a1 a2 a3 a4 a5 a6 a7
    exact run_reg_frame _ _ _ (by simp [tail, offOf, portInc, regsW, a1, a2, a3, a4, a5, a6, a7])
  have tailout : (run tail d2).out = d2.out := run_out_frame _ _ (by simp [tail, offOf, portInc, hasWrite])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · show (run countEdge c).reg Reg.p = _
    rw [hrun, tailfr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      d2fr _ (by decide) (by decide), x5]
  · show (run countEdge c).reg DR.cnt = _
    rw [hrun, tailfr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      d2fr _ (by decide) (by decide), x6]
  · show (run countEdge c).out = _
    rw [hrun, tailout, d2o]
  · intro r ⟨hr, a1, a2, a3, a4, a5, a6, a7⟩
    show (run countEdge c).reg r = _
    rw [hrun, tailfr r a2 hr.2.2.2.2.1 a3 a4 a5 a6 a7, d2fr r a1 a2, x10 r hr]
  -- the memory
  show (run countEdge c).mem = _
  rw [hrun]
  have hWbn : d2.reg DR.Wb = c.reg DR.Wb := by rw [d2fr _ (by decide) (by decide), x10 _ (by decide)]
  have hnn : d2.reg Reg.n = c.reg Reg.n := by rw [d2fr _ (by decide) (by decide), x10 _ (by decide)]
  have hbx : d2.reg DR.bx = e.1 / gadgetWidth k := by rw [d2fr _ (by decide) (by decide), x3]
  have hone2 : d2.reg Reg.one = 1 := by rw [d2fr _ (by decide) (by decide), x10 _ (by decide), hone]
  by_cases hb : e.1 / gadgetWidth k = e.2 / gadgetWidth k
  · have ht0 : d2.reg DR.t = 0 := by rw [d2t, hb]; simp
    let d3 := run (Stmt.sub DR.t2 Reg.n DR.bx) d2
    have hstep1 : run tail d2 = run (Stmt.ifz DR.t2 Stmt.skip
        (seqs (offOf DR.ex DR.ox ++ offOf DR.ey DR.oy ++ [portInc 0 2 6, portInc 1 4 5, portInc 2 0 3]))) d3 := by
      show run (Stmt.ifz DR.t _ Stmt.skip) d2 = _
      rw [run_ifz, ite_eq_left ht0, run_seq]
    rw [hstep1]
    have d3t2 : d3.reg DR.t2 = c.reg Reg.n - e.1 / gadgetWidth k := by
      simp +decide [d3, run]; rw [hnn, hbx]
    have d3m : d3.mem = c.mem := d2m
    have d3fr : ∀ r, r ≠ DR.t2 → d3.reg r = d2.reg r := by intro r a; simp [d3, run, a]
    by_cases hn : e.1 / gadgetWidth k < c.reg Reg.n
    · -- a candidate port edge
      have ht2 : d3.reg DR.t2 ≠ 0 := by rw [d3t2]; omega
      rw [run_ifz, ite_eq_right ht2]
      have hE3 : d3.reg DR.E = c.reg DR.E := by
        rw [d3fr _ (by decide), d2fr _ (by decide) (by decide), x10 _ (by decide)]
      have hex3 : d3.reg DR.ex = e.1 := by rw [d3fr _ (by decide), d2fr _ (by decide) (by decide), x1]
      have hey3 : d3.reg DR.ey = e.2 := by rw [d3fr _ (by decide), d2fr _ (by decide) (by decide), x2]
      have hone3 : d3.reg Reg.one = 1 := by rw [d3fr _ (by decide)]; exact hone2
      rw [run_seqs_app, run_seqs_app]
      generalize hd35 : run (seqs (offOf DR.ex DR.ox)) d3 = d35
      have d35ox : d35.reg DR.ox = e.1 % gadgetWidth k := by
        rw [← hd35, offOf_run _ _ _ (by decide) (by decide) hone3, hE3, hex3, d3m]; exact (hT e.1 h1).2
      have d35fr : ∀ r, r ≠ DR.addr → r ≠ DR.ox → d35.reg r = d3.reg r := fun r a b => hd35 ▸ offOf_frame d3 _ _ r a b
      have d35m : d35.mem = d3.mem := hd35 ▸ run_mem_frame _ _ (by decide)
      generalize hd4 : run (seqs (offOf DR.ey DR.oy)) d35 = d4
      have d4ox : d4.reg DR.ox = e.1 % gadgetWidth k := by
        rw [← hd4, offOf_frame _ _ _ _ (by decide) (by decide), d35ox]
      have d4oy : d4.reg DR.oy = e.2 % gadgetWidth k := by
        rw [← hd4, offOf_run _ _ _ (by decide) (by decide) (by rw [d35fr _ (by decide) (by decide)]; exact hone3),
          d35fr _ (by decide) (by decide), d35fr _ (by decide) (by decide), hE3, hey3, d35m, d3m]
        exact (hT e.2 h2).2
      have d4fr : ∀ r, r ≠ DR.addr → r ≠ DR.ox → r ≠ DR.oy → d4.reg r = d3.reg r := by
        intro r a b d'; rw [← hd4, offOf_frame _ _ _ _ a d', d35fr r a b]
      have d4m : d4.mem = c.mem := by rw [← hd4, run_mem_frame _ _ (by decide), d35m, d3m]
      have d4Wb : d4.reg DR.Wb = c.reg DR.Wb := by
        rw [d4fr _ (by decide) (by decide) (by decide), d3fr _ (by decide), hWbn]
      have d4bx : d4.reg DR.bx = e.1 / gadgetWidth k := by
        rw [d4fr _ (by decide) (by decide) (by decide), d3fr _ (by decide), hbx]
      have d4one : d4.reg Reg.one = 1 := by rw [d4fr _ (by decide) (by decide) (by decide)]; exact hone3
      show (run (seqs [portInc 0 2 6, portInc 1 4 5, portInc 2 0 3]) d4).mem = _
      simp only [run_seqs_cons, run_seqs_nil]
      have pf : ∀ (i a b : Nat) (d : Config) r, r ≠ DR.z1 → r ≠ DR.z2 → r ≠ DR.z3 → r ≠ DR.addr →
          (run (portInc i a b) d).reg r = d.reg r := fun i a b d r h1 h2 h3 h4 => portInc_frame d i a b r ⟨h1, h2, h3, h4⟩
      generalize hq0 : run (portInc 0 2 6) d4 = q0
      have q0r : ∀ r, r ≠ DR.z1 → r ≠ DR.z2 → r ≠ DR.z3 → r ≠ DR.addr → q0.reg r = d4.reg r := hq0 ▸ pf 0 2 6 d4
      generalize hq1 : run (portInc 1 4 5) q0 = q1
      have q1r : ∀ r, r ≠ DR.z1 → r ≠ DR.z2 → r ≠ DR.z3 → r ≠ DR.addr → q1.reg r = d4.reg r :=
        fun r h1 h2 h3 h4 => (hq1 ▸ pf 1 4 5 q0 r h1 h2 h3 h4).trans (q0r r h1 h2 h3 h4)
      funext x
      rw [portInc_mem' q1 2 0 3 x (by rw [q1r _ (by decide) (by decide) (by decide) (by decide)]; exact d4one),
        ← hq1, portInc_mem' q0 1 4 5 x (by rw [q0r _ (by decide) (by decide) (by decide) (by decide)]; exact d4one),
        ← hq0, portInc_mem' d4 0 2 6 x d4one, hq0, hq1]
      rw [q1r _ (by decide) (by decide) (by decide) (by decide), q1r _ (by decide) (by decide) (by decide) (by decide),
        q1r _ (by decide) (by decide) (by decide) (by decide), q1r _ (by decide) (by decide) (by decide) (by decide),
        q0r _ (by decide) (by decide) (by decide) (by decide), q0r _ (by decide) (by decide) (by decide) (by decide),
        q0r _ (by decide) (by decide) (by decide) (by decide), q0r _ (by decide) (by decide) (by decide) (by decide),
        d4ox, d4oy, d4Wb, d4bx, d4m]
      simp only [portEdgeG_iff k _ _ (Nat.mod_lt _ (by omega : 0 < 3)),
        variablePortEdge_cases (Nat.mod_lt _ (by omega : 0 < 3))]
      have hbd := hb
      generalize e.1 % gadgetWidth k = X
      generalize e.2 % gadgetWidth k = Y
      rw [← hbd]
      generalize e.1 / gadgetWidth k = V at hn ⊢
      rcases (by omega : (x - c.reg DR.Wb) % 3 = 0 ∨ (x - c.reg DR.Wb) % 3 = 1 ∨ (x - c.reg DR.Wb) % 3 = 2)
        with h3 | h3 | h3 <;> simp only [h3, ite_true, ite_false, show (1 : Nat) ≠ 0 from by decide,
          show (2 : Nat) ≠ 0 from by decide, show (2 : Nat) ≠ 1 from by decide] <;>
        (split <;> split <;> split <;> split <;> omega)
    · have ht2 : d3.reg DR.t2 = 0 := by rw [d3t2]; omega
      rw [run_ifz, ite_eq_left ht2]
      show d3.mem = _
      rw [d3m]
      funext a
      have : ¬ (c.reg DR.Wb ≤ a ∧ a < c.reg DR.Wb + 3 * c.reg Reg.n ∧
          e = portEdgeG k ((a - c.reg DR.Wb) / 3) ((a - c.reg DR.Wb) % 3)) := by
        rintro ⟨ha1, ha2, he⟩
        have := ((portEdgeG_iff k _ _ (Nat.mod_lt _ (by omega)) e).mp he).1
        omega
      simp [this]
  · have ht0 : d2.reg DR.t ≠ 0 := by rw [d2t]; omega
    show (run (Stmt.ifz DR.t _ Stmt.skip) d2).mem = _
    rw [run_ifz, ite_eq_right ht0]
    show d2.mem = _
    rw [d2m]
    funext a
    have : ¬ (c.reg DR.Wb ≤ a ∧ a < c.reg DR.Wb + 3 * c.reg Reg.n ∧
        e = portEdgeG k ((a - c.reg DR.Wb) / 3) ((a - c.reg DR.Wb) % 3)) := by
      rintro ⟨_, _, he⟩
      have := (portEdgeG_iff k _ _ (Nat.mod_lt _ (by omega)) e).mp he
      omega
    simp [this]

/-- `portInc i a b` updates the counter cell `Wb + 3 bx + i`. -/
theorem portInc_addrOK {SP : Nat} (d : Config) (i a b : Nat) (hone : d.reg Reg.one = 1)
    (h : d.reg DR.Wb + 3 * d.reg DR.bx + i < SP) : AddrOK SP (portInc i a b) d := by
  simp +decide [portInc, run, hone]; omega

theorem portIncs_addrOK {SP : Nat} (d : Config) (hone : d.reg Reg.one = 1)
    (h : d.reg DR.Wb + 3 * d.reg DR.bx + 2 < SP) :
    AddrOK SP (portInc 0 2 6) d ∧ AddrOK SP (portInc 1 4 5) (run (portInc 0 2 6) d) ∧
      AddrOK SP (portInc 2 0 3) (run (portInc 1 4 5) (run (portInc 0 2 6) d)) := by
  have fr : ∀ i a b (d' : Config), (run (portInc i a b) d').reg Reg.one = d'.reg Reg.one ∧
      (run (portInc i a b) d').reg DR.Wb = d'.reg DR.Wb ∧ (run (portInc i a b) d').reg DR.bx = d'.reg DR.bx :=
    fun i a b d' => ⟨run_reg_frame _ _ _ (by simp +decide [portInc, regsW]),
      run_reg_frame _ _ _ (by simp +decide [portInc, regsW]), run_reg_frame _ _ _ (by simp +decide [portInc, regsW])⟩
  refine ⟨portInc_addrOK d 0 2 6 hone (by omega), portInc_addrOK _ 1 4 5 ?_ ?_, portInc_addrOK _ 2 0 3 ?_ ?_⟩ <;>
    simp only [(fr _ _ _ _).1, (fr _ _ _ _).2.1, (fr _ _ _ _).2.2, hone] <;> omega

/-- The tail of `countEdge` reads the offset cells `E + 2x + 1` of the ends and updates the counter
cells `Wb + 3v + i` of a variable `v < n`. -/
theorem countTail_addrOK {SP : Nat} (d : Config) (hone : d.reg Reg.one = 1)
    (hex : d.reg DR.E + d.reg DR.ex + d.reg DR.ex + 1 < SP) (hey : d.reg DR.E + d.reg DR.ey + d.reg DR.ey + 1 < SP)
    (hW : d.reg DR.Wb + 3 * d.reg Reg.n ≤ SP) :
    AddrOK SP (seqs [Stmt.sub DR.t DR.bx DR.bY, Stmt.sub DR.t2 DR.bY DR.bx, Stmt.add DR.t DR.t DR.t2,
      Stmt.ifz DR.t (Stmt.seq (Stmt.sub DR.t2 Reg.n DR.bx) (Stmt.ifz DR.t2 Stmt.skip
      (seqs (offOf DR.ex DR.ox ++ offOf DR.ey DR.oy ++ [portInc 0 2 6, portInc 1 4 5, portInc 2 0 3])))) Stmt.skip]) d := by
  simp only [addrOK_seqs_append, addrOK_seqs_cons, addrOK_seqs_nil, addrOK_sub, addrOK_add, addrOK_ifz, addrOK_seq,
    addrOK_skip, true_and, and_true, implies_true]
  intro _ ht2
  refine ⟨?_, portIncs_addrOK _ ?_ ?_⟩
  · simp +decide [offOf, run, hone]; omega
  · simp +decide [offOf, run, hone]
  · simp +decide [offOf, run, hone] at ht2 ⊢; omega

theorem countEdge_addrOK {SP : Nat} (k X : Nat) (c : Config) (e : Edge) (rest : List Nat)
    (hAt : At c (edgeCode e ++ rest)) (hone : c.reg Reg.one = 1)
    (hT : TablesAt (gadgetWidth k) (c.reg DR.E) X c) (h1 : e.1 < X) (h2 : e.2 < X) (hp : c.reg Reg.p + 2 ≤ SP)
    (hS : c.reg DR.E + X + X ≤ SP) (hW : c.reg DR.Wb + 3 * c.reg Reg.n ≤ SP) : AddrOK SP countEdge c := by
  obtain ⟨x1, x2, -, -, -, -, -, -, -, x10⟩ := readEdge_run (gadgetWidth k) (c.reg DR.E) X c e rest hAt hone rfl hT h1 h2
  rw [show countEdge = seqs (readEdge ++ _) from rfl, addrOK_seqs_append]
  refine ⟨readEdge_addrOK (c.reg DR.E) X c e rest hAt hone rfl h1 h2 hp hS, countTail_addrOK _ ?_ ?_ ?_ ?_⟩
  · rw [x10 _ (by decide), hone]
  · rw [x1, x10 _ (by decide)]; omega
  · rw [x2, x10 _ (by decide)]; omega
  · rw [x10 _ (by decide), x10 _ (by decide)]; exact hW

end STACS2027.RAM
