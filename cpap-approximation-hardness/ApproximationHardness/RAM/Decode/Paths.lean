module

public import ApproximationHardness.RAM.Decode.Edges
import Lean.Elab.Tactic.Omega

/-!
# The decoding program: one path
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

/-- The counters after the paths `L`, on top of the memory `M`. -/
def wMem (k : Nat) (M : Nat → Nat) (Wb n : Nat) (L : List (List Edge)) (a : Nat) : Nat :=
  M a + (if Wb ≤ a ∧ a < Wb + 3 * n then clauseLoad k L ((a - Wb) / 3) ((a - Wb) % 3) else 0)

/-- The counters after the paths `L` and the edges `es` of the current path. -/
def wMemE (k : Nat) (M : Nat → Nat) (Wb n : Nat) (L : List (List Edge)) (es : List Edge) (a : Nat) : Nat :=
  wMem k M Wb n L a + (if Wb ≤ a ∧ a < Wb + 3 * n then es.count (portEdgeG k ((a - Wb) / 3) ((a - Wb) % 3)) else 0)

theorem wMem_below (k : Nat) (M : Nat → Nat) (Wb n : Nat) (L : List (List Edge)) {a : Nat} (ha : a < Wb) :
    wMem k M Wb n L a = M a := by simp [wMem]; omega

theorem wMemE_below (k : Nat) (M : Nat → Nat) (Wb n : Nat) (L : List (List Edge)) (es : List Edge) {a : Nat}
    (ha : a < Wb) : wMemE k M Wb n L es a = M a := by
  simp [wMemE, wMem_below k M Wb n L ha]; omega

theorem wMemE_nil (k : Nat) (M : Nat → Nat) (Wb n : Nat) (L : List (List Edge)) :
    wMemE k M Wb n L [] = wMem k M Wb n L := by funext a; simp [wMemE]

theorem wMemE_snoc (k : Nat) (M : Nat → Nat) (Wb n : Nat) (L : List (List Edge)) (es : List Edge) (e : Edge) :
    wMemE k M Wb n L (es ++ [e]) = fun a => wMemE k M Wb n L es a +
      (if Wb ≤ a ∧ a < Wb + 3 * n ∧ e = portEdgeG k ((a - Wb) / 3) ((a - Wb) % 3) then 1 else 0) := by
  funext a
  unfold wMemE
  by_cases h : Wb ≤ a ∧ a < Wb + 3 * n
  · rw [ite_eq_left h, ite_eq_left h, List.count_append, List.count_singleton]
    by_cases he : e = portEdgeG k ((a - Wb) / 3) ((a - Wb) % 3)
    · simp [he, h]; omega
    · have : ¬ (Wb ≤ a ∧ a < Wb + 3 * n ∧ e = portEdgeG k ((a - Wb) / 3) ((a - Wb) % 3)) := fun h' => he h'.2.2
      rw [ite_eq_right this]
      simp [he]
  · have : ¬ (Wb ≤ a ∧ a < Wb + 3 * n ∧ e = portEdgeG k ((a - Wb) / 3) ((a - Wb) % 3)) :=
      fun h' => h ⟨h'.1, h'.2.1⟩
    simp [h, this]

theorem clauseLoad_snoc (k : Nat) (L : List (List Edge)) (p : List Edge) (v i : Nat) :
    clauseLoad k (L ++ [p]) v i = clauseLoad k L v i + loadTerm k v i p := by
  simp [clauseLoad_eq, List.map_append]

/-! ### Which paths count -/

/-- Some edge of `p` has an endpoint outside the block `b0`. -/
def flagOf (w b0 : Nat) (p : List Edge) : Bool := p.any fun e => e.1 / w != b0 || e.2 / w != b0

theorem loadTerm_flag (k v i : Nat) (p : List Edge) (b0 : Nat) (hb0 : ∀ e ∈ p.head?, e.1 / gadgetWidth k = b0) :
    loadTerm k v i p = if flagOf (gadgetWidth k) b0 p then p.count (portEdgeG k v i) else 0 := by
  unfold loadTerm
  cases hf : flagOf (gadgetWidth k) b0 p
  · -- every vertex is in the block `b0`
    have hall : ∀ e ∈ p, e.1 / gadgetWidth k = b0 ∧ e.2 / gadgetWidth k = b0 := by
      intro e he
      have := List.any_eq_false.mp hf e he
      simpa using this
    by_cases hv : v = b0
    · subst hv
      have : outsideBlock k v p = false := by
        unfold outsideBlock
        apply List.any_eq_false.mpr
        intro e he
        obtain ⟨h1, h2⟩ := hall e he
        simp [blockOf, h1, h2]
      simp [this]
    · have : p.count (portEdgeG k v i) = 0 := by
        apply List.count_eq_zero_of_not_mem
        intro hE
        have := (hall _ hE).1
        rw [show (portEdgeG k v i).1 / gadgetWidth k = blockOf k (portEdgeG k v i).1 from rfl,
          (portEdgeG_blocks k v i).1] at this
        exact hv this
      simp [this]
  · -- two blocks: the path leaves every block
    obtain ⟨e, he, hne⟩ := List.any_eq_true.mp hf
    have : outsideBlock k v p = true := by
      unfold outsideBlock
      apply List.any_eq_true.mpr
      by_cases hv : v = b0
      · subst hv
        refine ⟨e, he, ?_⟩
        simp [blockOf] at hne ⊢
        omega
      · cases hp : p with
        | nil => simp [hp] at he
        | cons e0 rest =>
          have h0 := hb0 e0 (by simp [hp])
          refine ⟨e0, by simp, ?_⟩
          simp [blockOf, h0]
          exact Or.inl (fun h => hv h.symm)
    simp [this]

/-! ### One path -/

theorem flagOf_snoc (w b0 : Nat) (es : List Edge) (e : Edge) :
    flagOf w b0 (es ++ [e]) = (flagOf w b0 es || (e.1 / w != b0 || e.2 / w != b0)) := by
  simp [flagOf, List.any_append]

theorem edgeCodes_length (es : List Edge) : (es.flatMap edgeCode).length = 2 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [edgeCode] at ih ⊢; omega

theorem sum_map_const_succ {α : Type} (xs : List α) (b : Nat) : (xs.map fun _ => b + 1).sum = xs.length * (b + 1) := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul]; omega

/-- The registers one path leaves alone. -/
abbrev PathFixed (r : Nat) : Prop := CountFixed r ∧ r ≠ DR.np ∧ r ≠ DR.len ∧ r ≠ DR.ps ∧ r ≠ DR.flag ∧ r ≠ DR.b0

def pathCost (p : List Edge) : Nat :=
  size pathPre + ((p.length * (size flagEdge + 1)) + 1) + 1 + (3 + (p.length * (size countEdge + 1) + 1))

theorem pathBody_step (k S : Nat) (M : Nat → Nat) (Wb n : Nat) (c : Config) (L : List (List Edge)) (p : List Edge)
    (rest : List Nat) (hAt : At c (pathCode p ++ rest)) (hone : c.reg Reg.one = 1) (hzero : c.reg Reg.zero = 0)
    (hTM : ∀ x, x < S → M (c.reg DR.E + x + x) = x / gadgetWidth k ∧ M (c.reg DR.E + x + x + 1) = x % gadgetWidth k)
    (hverts : ∀ e ∈ p, e.1 < S ∧ e.2 < S) (hWbr : c.reg DR.Wb = Wb) (hnr : c.reg Reg.n = n)
    (hWb : c.reg DR.E + S + S ≤ Wb) (hm : c.mem = wMem k M Wb n L)
    (hin : c.reg Reg.p + (pathCode p ++ rest).length ≤ Wb) {SP : Nat} (hSP : Wb + 3 * n ≤ SP) :
    ∃ t c', ExecB SP pathBody c t c' ∧ t ≤ pathCost p ∧ c'.mem = wMem k M Wb n (L ++ [p]) ∧
      c'.reg Reg.p = c.reg Reg.p + (pathCode p).length ∧ c'.reg DR.np = c.reg DR.np - 1 ∧ At c' rest ∧
      c'.out = c.out ∧ ∀ r, PathFixed r → c'.reg r = c.reg r := by
  have hw := gadgetWidth_ge k
  have hE0 := hWb
  -- tables in every memory agreeing with `M` below `Wb`
  have tabOf : ∀ d : Config, d.reg DR.E = c.reg DR.E → (∀ a, a < Wb → d.mem a = M a) →
      TablesAt (gadgetWidth k) (d.reg DR.E) S d := by
    intro d hE hd x hx
    rw [hE, hd _ (by omega), hd _ (by omega)]
    exact hTM x hx
  have cM : ∀ a, a < Wb → c.mem a = M a := fun a ha => by rw [hm, wMem_below _ _ _ _ _ ha]
  -- the prefix
  have g0 : c.mem (c.reg Reg.p) = p.length := by have := hAt.head; simpa [pathCode] using this
  have hpl : (pathCode p ++ rest).length = 1 + 2 * p.length + rest.length := by
    simp [pathCode_length]; try omega
  have hA1 : AddrOK SP pathPre c := by
    cases p with
    | nil => simp +decide [pathPre, blkOf, run, hone, g0]; omega
    | cons e0 ps' =>
      have g1 := hAt.getD (i := 1) (by simp [pathCode, edgeCode])
      simp [pathCode, edgeCode] at g1
      have hv := (hverts e0 (by simp)).1
      simp only [List.length_cons] at hpl g0
      simp +decide [pathPre, blkOf, run, hone, g0, g1]; omega
  obtain ⟨t1, e1, ht1⟩ := exec_loopFree (S := SP) (s := pathPre) (by simp [pathPre, blkOf, seqs, LoopFree]) c hA1
  generalize hc1 : run pathPre c = c1 at e1
  have c1np : c1.reg DR.np = c.reg DR.np - 1 := by rw [← hc1]; simp +decide [pathPre, blkOf, run, hone]
  have c1len : c1.reg DR.len = p.length := by rw [← hc1]; simp +decide [pathPre, blkOf, run, hone, g0]
  have c1p : c1.reg Reg.p = c.reg Reg.p + 1 := by rw [← hc1]; simp +decide [pathPre, blkOf, run, hone]
  have c1ps : c1.reg DR.ps = c.reg Reg.p + 1 := by rw [← hc1]; simp +decide [pathPre, blkOf, run, hone, hzero]
  have c1flag : c1.reg DR.flag = 0 := by rw [← hc1]; simp +decide [pathPre, blkOf, run]
  have c1cnt : c1.reg DR.cnt = p.length := by rw [← hc1]; simp +decide [pathPre, blkOf, run, hone, g0, hzero]
  have c1m : c1.mem = c.mem := by rw [← hc1]; exact run_mem_frame _ _ (by decide)
  have c1o : c1.out = c.out := by rw [← hc1]; exact run_out_frame _ _ (by decide)
  have c1fr : ∀ r, r ≠ DR.np → r ≠ DR.len → r ≠ Reg.p → r ≠ DR.ps → r ≠ DR.flag → r ≠ DR.ex → r ≠ DR.addr →
      r ≠ DR.b0 → r ≠ DR.cnt → c1.reg r = c.reg r := by
    intro r a1 a2 a3 a4 a5 a6 a7 a8 a9
    rw [← hc1]; exact run_reg_frame _ _ _ (by simp [pathPre, blkOf, regsW, a1, a2, a3, a4, a5, a6, a7, a8, a9])
  have c1b0 : ∀ e ∈ p.head?, e.1 / gadgetWidth k = c1.reg DR.b0 := by
    intro e he
    cases p with
    | nil => simp at he
    | cons e0 ps' =>
      simp at he; subst he
      have g1 := hAt.getD (i := 1) (by simp [pathCode, edgeCode])
      simp [pathCode, edgeCode] at g1
      have hv := (hverts e0 (by simp)).1
      rw [← hc1]
      simp +decide [pathPre, blkOf, run, hone, g0, g1]
      rw [cM _ (by omega)]
      exact ((hTM e0.1 hv).1).symm
  have c1E : c1.reg DR.E = c.reg DR.E := c1fr _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have c1one : c1.reg Reg.one = 1 := by
    rw [c1fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hone
  have hAt1 : At c1 (p.flatMap edgeCode ++ rest) := by
    have : At c (pathCode p ++ rest) := hAt
    simp only [pathCode, List.cons_append] at this
    exact this.tail c1m c1p
  -- the flag pass
  let FI : List Edge → Config → Prop := fun pre d =>
    d.reg DR.flag = (if flagOf (gadgetWidth k) (c1.reg DR.b0) pre then 1 else 0) ∧
    d.reg Reg.p = c.reg Reg.p + 1 + 2 * pre.length ∧ d.mem = c.mem ∧ d.out = c.out ∧
    ∀ r, EdgeScratch r → r ≠ DR.t → r ≠ DR.t2 → r ≠ DR.flag → d.reg r = c1.reg r
  have fstep : ∀ pre x suf d, pre ++ x :: suf = p → FI pre d → d.reg DR.cnt = suf.length + 1 →
      At d (edgeCode x ++ suf.flatMap edgeCode) →
      ∃ t d', ExecB SP flagEdge d t d' ∧ t ≤ size flagEdge ∧ FI (pre ++ [x]) d' ∧ d'.reg DR.cnt = suf.length ∧
        At d' (suf.flatMap edgeCode) := by
    intro pre x suf d hpre ⟨df, dp, dm, dout, dfr⟩ dcnt dAt
    have hx : x ∈ p := by rw [← hpre]; simp
    have dE : d.reg DR.E = c.reg DR.E := by
      rw [dfr _ (by decide) (by decide) (by decide) (by decide), c1E]
    have done' : d.reg Reg.one = 1 := by rw [dfr _ (by decide) (by decide) (by decide) (by decide)]; exact c1one
    have dT := tabOf d dE (fun a ha => by rw [dm]; exact cM a ha)
    obtain ⟨y1, y2, y3, y4, y5, y6, y7⟩ := flagEdge_run (gadgetWidth k) (c.reg DR.E) S d x _
      dAt done' dE (dE ▸ dT) (hverts x hx).1 (hverts x hx).2
    have hlp : pre.length + 1 ≤ p.length := by rw [← hpre]; simp
    obtain ⟨t, he, ht⟩ := exec_loopFree (S := SP) (s := flagEdge) (by simp [flagEdge, readEdge, blkOf, flagIfNe, seqs, LoopFree,
      ]) d (flagEdge_addrOK (c.reg DR.E) S d x _ dAt done' dE (hverts x hx).1 (hverts x hx).2
        (by rw [dp]; omega) (by omega))
    have hb0d : d.reg DR.b0 = c1.reg DR.b0 := dfr _ (by decide) (by decide) (by decide) (by decide)
    refine ⟨t, _, he, ht, ⟨?_, ?_, by rw [y4, dm], by rw [y5, dout], fun r hr a b d' => by rw [y7 r hr a b d', dfr r hr a b d']⟩,
      by rw [y3, dcnt]; rfl, y6⟩
    · rw [y1, df, hb0d, flagOf_snoc]
      cases flagOf (gadgetWidth k) (c1.reg DR.b0) pre <;>
        by_cases h1 : x.1 / gadgetWidth k = c1.reg DR.b0 <;> by_cases h2 : x.2 / gadgetWidth k = c1.reg DR.b0 <;>
        simp [h1, h2]
    · rw [y2, dp]; simp; omega
  obtain ⟨tF, d2, eF, htF, hFI⟩ := exec_listPass edgeCode p FI (fun _ => size flagEdge) fstep c1
    ⟨by rw [c1flag]; rfl, by rw [c1p]; simp, by rw [c1m], by rw [c1o], fun _ _ _ _ _ => rfl⟩ c1cnt
    hAt1.append_left
  obtain ⟨d2f, d2p, d2m, d2o, d2fr⟩ := hFI
  have d2fr' : ∀ r, PathFixed r → d2.reg r = c.reg r := by
    intro r ⟨⟨⟨a1, a2, a3, a4, a5, a6, a7⟩, a8, a9, a10, a11, a12, a13, a14⟩, b1, b2, b3, b4, b5⟩
    rw [d2fr r ⟨a1, a2, a3, a4, a5, a6, a7⟩ a8 a9 b4, c1fr r b1 b2 a4 b3 b4 a2 a5 b5 a1]
  have hpend : c.reg Reg.p + 1 + 2 * p.length = c.reg Reg.p + (pathCode p).length := by
    rw [pathCode_length]; omega
  have hAtEnd : ∀ d : Config, d.reg Reg.p = c.reg Reg.p + (pathCode p).length →
      (∀ a, a < Wb → d.mem a = M a) → At d rest := by
    intro d hdp hdm
    apply At.advance hAt hdp
    intro a ha
    rw [hdm _ (by omega), cM _ (by omega)]
  by_cases hflag : flagOf (gadgetWidth k) (c1.reg DR.b0) p = true
  · -- the path counts: the count pass
    have hf1 : d2.reg DR.flag ≠ 0 := by rw [d2f, ite_eq_left hflag]; decide
    let rs := seqs [Stmt.add Reg.p DR.ps Reg.zero, Stmt.add DR.cnt DR.len Reg.zero]
    obtain ⟨t3, e3, ht3⟩ := exec_loopFree (S := SP) (s := rs) (by simp [rs, seqs, LoopFree]) d2 (AddrOK.of_memFree rfl)
    generalize hc3 : run rs d2 = d3 at e3
    have d3p : d3.reg Reg.p = c.reg Reg.p + 1 := by
      rw [← hc3]; simp +decide [rs, run]
      rw [d2fr _ (by decide) (by decide) (by decide) (by decide), c1ps,
        d2fr _ (by decide) (by decide) (by decide) (by decide),
        c1fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hzero]
    have d3cnt : d3.reg DR.cnt = p.length := by
      rw [← hc3]; simp +decide [rs, run]
      rw [d2fr _ (by decide) (by decide) (by decide) (by decide), c1len,
        d2fr _ (by decide) (by decide) (by decide) (by decide),
        c1fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hzero, Nat.add_zero]
    have d3m : d3.mem = c.mem := by rw [← hc3, run_mem_frame _ _ (by decide), d2m]
    have d3o : d3.out = c.out := by rw [← hc3, run_out_frame _ _ (by decide), d2o]
    have d3fr : ∀ r, r ≠ Reg.p → r ≠ DR.cnt → d3.reg r = d2.reg r := by
      intro r a b; rw [← hc3]; simp [rs, run, a, b]
    have d3At : At d3 (p.flatMap edgeCode) := by
      have : At c (pathCode p ++ rest) := hAt
      simp only [pathCode, List.cons_append] at this
      exact (this.tail d3m d3p).append_left
    have pfx : ∀ r, PathFixed r → d3.reg r = c.reg r := fun r hr => by
      rw [d3fr r hr.1.1.2.2.2.1 hr.1.1.1, d2fr' r hr]
    -- the count pass proper
    let CI : List Edge → Config → Prop := fun pre d =>
      d.mem = wMemE k M Wb n L pre ∧ d.reg Reg.p = c.reg Reg.p + 1 + 2 * pre.length ∧ d.out = c.out ∧
      ∀ r, CountFixed r → d.reg r = d3.reg r
    have cstep : ∀ pre x suf d, pre ++ x :: suf = p → CI pre d → d.reg DR.cnt = suf.length + 1 →
        At d (edgeCode x ++ suf.flatMap edgeCode) →
        ∃ t d', ExecB SP countEdge d t d' ∧ t ≤ size countEdge ∧ CI (pre ++ [x]) d' ∧ d'.reg DR.cnt = suf.length ∧
          At d' (suf.flatMap edgeCode) := by
      intro pre x suf d hpre ⟨dm, dp, dout, dfr⟩ dcnt dAt
      have hx : x ∈ p := by rw [← hpre]; simp
      have dE : d.reg DR.E = c.reg DR.E := by
        rw [dfr _ (by decide), d3fr _ (by decide) (by decide), d2fr _ (by decide) (by decide) (by decide) (by decide),
          c1E]
      have done' : d.reg Reg.one = 1 := by
        rw [dfr _ (by decide), d3fr _ (by decide) (by decide), d2fr _ (by decide) (by decide) (by decide) (by decide),
          c1one]
      have dWb : d.reg DR.Wb = Wb := by
        rw [dfr _ (by decide), pfx _ (by decide), hWbr]
      have dn : d.reg Reg.n = n := by
        rw [dfr _ (by decide), pfx _ (by decide), hnr]
      have dT := tabOf d dE (fun a ha => by rw [dm, wMemE_below _ _ _ _ _ _ ha])
      obtain ⟨z1, z2, z3, z4, z5⟩ := countEdge_run k S d x _ dAt done' dT (hverts x hx).1 (hverts x hx).2
        (by rw [dE, dWb]; exact hWb)
      have hlp : pre.length + 1 ≤ p.length := by rw [← hpre]; simp
      obtain ⟨t, he, ht⟩ := exec_loopFree (S := SP) (s := countEdge) (by simp [countEdge, readEdge, blkOf, offOf, portInc,
        seqs, LoopFree]) d (countEdge_addrOK k S d x _ dAt done' dT (hverts x hx).1 (hverts x hx).2
          (by rw [dp]; omega) (by rw [dE]; omega) (by rw [dWb, dn]; exact hSP))
      refine ⟨t, _, he, ht, ⟨?_, ?_, by rw [z4, dout], fun r hr => by rw [z5 r hr, dfr r hr]⟩, by rw [z3, dcnt]; rfl, ?_⟩
      · rw [z1, wMemE_snoc, dm, dWb, dn]
      · rw [z2, dp]; simp; omega
      · apply At.advance dAt (by rw [z2]; simp [edgeCode])
        intro a ha
        have hlen : p.length = pre.length + 1 + suf.length := by rw [← hpre]; simp; omega
        have : a < Wb := by
          rw [dp] at ha; simp only [List.length_append, edgeCodes_length, edgeCode, List.length_cons,
            List.length_nil] at ha
          rw [hpl] at hin; omega
        rw [z1]; simp only; rw [ite_eq_right (by omega)]; rfl
    obtain ⟨tC, d4, eC, htC, hCI⟩ := exec_listPass edgeCode p CI (fun _ => size countEdge) cstep d3
      ⟨by rw [d3m, hm, wMemE_nil], by rw [d3p]; simp, d3o, fun _ _ => rfl⟩ d3cnt d3At
    obtain ⟨d4m, d4p, d4o, d4fr⟩ := hCI
    have hpe : d4.reg Reg.p = c.reg Reg.p + (pathCode p).length := by rw [d4p, hpend]
    refine ⟨t1 + (tF + (t3 + tC + 1)), d4, ExecB.seq e1 (ExecB.seq eF (ExecB.ifzFalse hf1 (ExecB.seq e3 eC))), ?_, ?_,
      hpe, ?_, ?_, by rw [d4o], ?_⟩
    · rw [sum_map_const_succ] at htF htC
      have : size rs = 3 := by simp [rs, size, seqs]
      unfold pathCost; omega
    · rw [d4m]
      funext a
      unfold wMemE wMem
      by_cases h : Wb ≤ a ∧ a < Wb + 3 * n
      · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, clauseLoad_snoc, loadTerm_flag k _ _ p _ c1b0, ite_eq_left hflag]
        omega
      · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]
    · rw [d4fr _ (by decide), d3fr _ (by decide) (by decide), d2fr _ (by decide) (by decide) (by decide) (by decide),
        c1np]
    · exact hAtEnd d4 hpe (fun a ha => by rw [d4m, wMemE_below _ _ _ _ _ _ ha])
    · intro r hr
      rw [d4fr r hr.1, pfx r hr]
  · -- the path does not count
    have hf0 : d2.reg DR.flag = 0 := by rw [d2f, ite_eq_right hflag]
    have hpe : d2.reg Reg.p = c.reg Reg.p + (pathCode p).length := by rw [d2p, hpend]
    refine ⟨t1 + (tF + (1 + 1)), d2, ExecB.seq e1 (ExecB.seq eF (ExecB.ifzTrue hf0 (ExecB.skip d2))), ?_, ?_, hpe,
      ?_, ?_, by rw [d2o], d2fr'⟩
    · rw [sum_map_const_succ] at htF
      unfold pathCost; omega
    · rw [d2m, hm]
      funext a
      unfold wMem
      by_cases h : Wb ≤ a ∧ a < Wb + 3 * n
      · rw [ite_eq_left h, ite_eq_left h, clauseLoad_snoc, loadTerm_flag k _ _ p _ c1b0, ite_eq_right hflag, Nat.add_zero]
      · rw [ite_eq_right h, ite_eq_right h]
    · rw [d2fr _ (by decide) (by decide) (by decide) (by decide), c1np]
    · exact hAtEnd d2 hpe (fun a ha => by rw [d2m]; exact cM a ha)

end STACS2027.RAM
