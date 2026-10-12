module

public import Runtimes.BoundedCost.CoreReuse
public import Runtimes.ZeroCostEdges
public import Runtimes.Flow.OffsetCall
public import Runtimes.BoundedCost.CallerRegisters
public import Runtimes.BoundedCost.SearchNodeRAM
import Mathlib.Tactic

/-! A deterministic compact core retains every enumerated cycle-edge occurrence.
Its duplicate list entries preserve graph support and the exact cycle order. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.CoreRAM

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

abbrev coreBase : ℕ := 600
abbrev coreAddress : ℕ := 601
abbrev coreTwo : ℕ := 602
abbrev coreFour : ℕ := 603
abbrev coreLength : ℕ := 604
abbrev coreBudget : ℕ := 605
abbrev copyIndex : ℕ := 606
abbrev headerIndex : ℕ := 607

def storeWord (value : ℕ) : Stmt :=
  .seq (.add coreAddress coreBase headerIndex)
    (.seq (.add coreAddress coreAddress coreAddress)
      (.seq (.add coreAddress coreAddress coreAddress)
        (.seq (.add coreAddress coreAddress coreTwo) (.store coreAddress value))))

def header : Stmt := .seq (.const headerIndex 0)
  (.seq (storeWord gKT)
    (.seq (.add headerIndex gKT gKT)
      (.seq (addc headerIndex headerIndex 1)
        (.seq (storeWord gK)
          (.seq (inc headerIndex)
            (.seq (storeWord gT)
              (.seq (.add headerIndex gKT gKT)
                (.seq (.add headerIndex headerIndex gKT)
                  (.seq (addc headerIndex headerIndex 3) (storeWord coreBudget))))))))))

def headerMemory (memory : ℕ → ℕ) (base count k t budget : ℕ) : ℕ → ℕ :=
  upd (upd (upd (upd memory (4 * base + 2) count)
    (4 * (base + 2 * count + 1) + 2) k)
    (4 * (base + 2 * count + 2) + 2) t)
    (4 * (base + 3 * count + 3) + 2) budget

def HeaderGlobals (base count k t budget : ℕ) (c : Config) : Prop :=
  c.reg coreBase = base ∧ c.reg gKT = count ∧ c.reg gK = k ∧ c.reg gT = t ∧
    c.reg coreBudget = budget ∧ c.reg coreTwo = 2

theorem header_spec {S base count k t budget : ℕ} {memory : ℕ → ℕ} {out : List ℕ}
    (hS : 4 * (base + 3 * count + 3) + 2 < S) :
    HTB S header
      (fun c => HeaderGlobals base count k t budget c ∧ c.mem = memory ∧ c.out = out)
      (fun c => HeaderGlobals base count k t budget c ∧
        c.mem = headerMemory memory base count k t budget ∧ c.out = out) 32 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨hb, hn, hk, ht, hbudget, htwo⟩, hm, ho⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · addr_ok [header, storeWord, hb, hn, hk, ht, hbudget, htwo]
  · exact (show RegIndep (wregs header) (HeaderGlobals base count k t budget) by
      indep [HeaderGlobals, header, storeWord, inc, addc]).run (by decide)
      ⟨hb, hn, hk, ht, hbudget, htwo⟩
  · simp +decide only [header, storeWord, headerMemory, run_seq', run_add, run_addc,
      run_inc, run_const, run_store, setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd,
      hb, hn, hk, ht, hbudget, htwo, hm, ↓reduceIte]
    have hbase : base + 0 + (base + 0) + (base + 0 + (base + 0)) + 2 = 4 * base + 2 := by omega
    simp only [Nat.add_zero] at *
    have hhead : base + base + (base + base) + 2 = 4 * base + 2 := by omega
    rw [hhead]
    have haddr (x : ℕ) : base + x + (base + x) + (base + x + (base + x)) + 2 =
        4 * (base + x) + 2 := by omega
    rw [haddr, haddr, haddr,
      show count + count + 1 = 2 * count + 1 by omega,
      show 2 * count + 1 + 1 = 2 * count + 2 by omega,
      show count + count + count + 3 = 3 * count + 3 by omega]
    simp only [Nat.add_assoc]
  · exact (run_out_of_writes (by decide) (by decide) c).trans ho

def readEdge : Stmt := .seq edgeA (.seq nextPos (.seq (ld sY gV sP) minmax))
def readWrites : List ℕ := [sQ, sX, sP, sY, rT]

theorem readEdge_run {g : Graph} {k i j source S : ℕ} {c : Config}
    (hS : source + k * (cycles g k).length ≤ S)
    (hi : i < (cycles g k).length) (hj : j < k)
    (hverts : Arr c.mem source (verts g k)) (hsource : c.reg gV = source)
    (hK : c.reg gK = k) (hJ : c.reg sJ = j) (hB : c.reg sBase = i * k) :
    (run readEdge c).reg sQ = i * k + j ∧
      (run readEdge c).reg sX = ((occs g k).getD (i * k + j) (0, 0)).1 ∧
      (run readEdge c).reg sY = ((occs g k).getD (i * k + j) (0, 0)).2 ∧
      Agree readWrites c (run readEdge c) ∧ AddrOK S readEdge c := by
  have hq := occ_lt hi hj
  have hk : 0 < k := by omega
  have hq2 := occ_lt hi (next_lt hk (j := j))
  set x := (verts g k).getD (i * k + j) 0
  set y := (verts g k).getD (i * k + next k j) 0
  have he : (occs g k).getD (i * k + j) (0, 0) = edge x y := occs_getD hi hj
  have hx : c.mem (source + (i * k + j)) = x := hverts.getD (by rw [length_verts]; exact hq)
  have hy : c.mem (source + (i * k + next k j)) = y := hverts.getD (by rw [length_verts]; exact hq2)
  obtain ⟨h1q, h1x, a1⟩ := edgeA_run c
  obtain ⟨h2p, a2⟩ := nextPos_run (c := run edgeA c) (base := i * k)
    (by rw [a1.reg sJ (by decide), hJ]) (by rw [a1.reg gK (by decide), hK])
    (by rw [h1q, hB, hJ]) (by rw [a1.reg sBase (by decide), hB])
  obtain ⟨h3y, a3⟩ := ldY_run (run nextPos (run edgeA c))
  obtain ⟨h4x, h4y, a4⟩ := minmax_run (run (ld sY gV sP) (run nextPos (run edgeA c)))
  have ha : Agree readWrites c (run readEdge c) :=
    (((a1.mono (by decide)).trans (a2.mono (by decide))).trans (a3.mono (by decide))).trans
      (a4.mono (by decide))
  have ex : (run (ld sY gV sP) (run nextPos (run edgeA c))).reg sX = x := by
    rw [a3.reg sX (by decide), a2.reg sX (by decide), h1x, hsource, hB, hJ, hx]
  have ey : (run (ld sY gV sP) (run nextPos (run edgeA c))).reg sY = y := by
    rw [h3y, a2.mem, a1.mem, a2.reg gV (by decide), a1.reg gV (by decide), h2p, hsource, hy]
  refine ⟨?_, ?_, ?_, ha, ?_⟩
  · change (run minmax (run (ld sY gV sP) (run nextPos (run edgeA c)))).reg sQ = _
    rw [a4.reg sQ (by decide), a3.reg sQ (by decide), a2.reg sQ (by decide), h1q, hB, hJ]
  · rw [show run readEdge c = run minmax (run (ld sY gV sP) (run nextPos (run edgeA c))) from rfl,
      h4x, ex, ey, he]; rfl
  · rw [show run readEdge c = run minmax (run (ld sY gV sP) (run nextPos (run edgeA c))) from rfl,
      h4y, ex, ey, he]; rfl
  · refine AddrOK.seq (by addr_ok [edgeA, hsource, hB, hJ])
      (AddrOK.seq (AddrOK.of_memFree rfl) (AddrOK.seq ?_ (AddrOK.of_memFree rfl)))
    rw [addrOK_ld, a2.reg gV (by decide), a1.reg gV (by decide), h2p, hsource]
    omega

def putEdge : Stmt :=
  .seq (.add coreAddress sQ sQ)
    (.seq (addc coreAddress coreAddress 1)
      (.seq (.add coreAddress coreBase coreAddress)
        (.seq (.add coreAddress coreAddress coreAddress)
          (.seq (.add coreAddress coreAddress coreAddress)
            (.seq (.add coreAddress coreAddress coreTwo)
              (.seq (.store coreAddress sX)
                (.seq (.add coreAddress coreAddress coreFour) (.store coreAddress sY))))))))

def edgeBody : Stmt := .seq readEdge putEdge
def edgeRow : Stmt := .seq (forUp sJ gK edgeBody) (.add sBase sBase gK)
def edgeLoop : Stmt := .seq (.const sBase 0) (forUp sI gT edgeRow)

def edgeMemory (memory : ℕ → ℕ) (base : ℕ) (edges : List Edge) (q : ℕ) : ℕ → ℕ :=
  (List.range q).foldl (fun m i =>
    upd (upd m (4 * (base + 1 + 2 * i) + 2) (edges.getD i (0, 0)).1)
      (4 * (base + 2 + 2 * i) + 2) (edges.getD i (0, 0)).2) memory

@[simp] theorem edgeMemory_zero (memory : ℕ → ℕ) (base : ℕ) (edges : List Edge) :
    edgeMemory memory base edges 0 = memory := rfl

theorem edgeMemory_succ (memory : ℕ → ℕ) (base : ℕ) (edges : List Edge) (q : ℕ) :
    edgeMemory memory base edges (q + 1) =
      upd (upd (edgeMemory memory base edges q) (4 * (base + 1 + 2 * q) + 2) (edges.getD q (0, 0)).1)
        (4 * (base + 2 + 2 * q) + 2) (edges.getD q (0, 0)).2 := by
  simp [edgeMemory, List.range_succ]

theorem edgeMemory_outside {memory : ℕ → ℕ} {base q a : ℕ} {edges : List Edge}
    (ha : a < 4 * (base + 1) + 2 ∨ 4 * (base + 1 + 2 * q) + 2 ≤ a ∨ a % 4 ≠ 2) :
    edgeMemory memory base edges q a = memory a := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [edgeMemory_succ]
    simp only [upd, ite_eq_right (show a ≠ 4 * (base + 2 + 2 * q) + 2 by omega),
      ite_eq_right (show a ≠ 4 * (base + 1 + 2 * q) + 2 by omega)]
    exact ih (by omega)

theorem edgeMemory_pair {memory : ℕ → ℕ} {base q i : ℕ} {edges : List Edge} (hi : i < q) :
    edgeMemory memory base edges q (4 * (base + 1 + 2 * i) + 2) = (edges.getD i (0, 0)).1 ∧
      edgeMemory memory base edges q (4 * (base + 2 + 2 * i) + 2) = (edges.getD i (0, 0)).2 := by
  induction q with
  | zero => omega
  | succ q ih =>
    rw [edgeMemory_succ]
    by_cases he : i = q
    · subst i
      simp [upd, show 4 * (base + 1 + 2 * q) + 2 ≠ 4 * (base + 2 + 2 * q) + 2 by omega]
    · have hlt : i < q := by omega
      have hp := ih hlt
      constructor
      · simp only [upd, ite_eq_right (show 4 * (base + 1 + 2 * i) + 2 ≠
          4 * (base + 2 + 2 * q) + 2 by omega),
          ite_eq_right (show 4 * (base + 1 + 2 * i) + 2 ≠ 4 * (base + 1 + 2 * q) + 2 by omega)]
        exact hp.1
      · simp only [upd, ite_eq_right (show 4 * (base + 2 + 2 * i) + 2 ≠
          4 * (base + 2 + 2 * q) + 2 by omega),
          ite_eq_right (show 4 * (base + 2 + 2 * i) + 2 ≠ 4 * (base + 1 + 2 * q) + 2 by omega)]
        exact hp.2

def vertexPut : Stmt :=
  .seq (ld sX gV copyIndex)
    (.seq (.add coreAddress gKT gKT)
      (.seq (addc coreAddress coreAddress 3)
        (.seq (.add coreAddress coreAddress copyIndex)
          (.seq (.add coreAddress coreBase coreAddress)
            (.seq (.add coreAddress coreAddress coreAddress)
              (.seq (.add coreAddress coreAddress coreAddress)
                (.seq (.add coreAddress coreAddress coreTwo) (.store coreAddress sX))))))))

def vertexLoop : Stmt := forUp copyIndex gKT vertexPut

def vertexMemory (memory : ℕ → ℕ) (base count : ℕ) (values : List ℕ) (q : ℕ) : ℕ → ℕ :=
  (List.range q).foldl (fun m i => upd m (4 * (base + 2 * count + 3 + i) + 2) (values.getD i 0)) memory

@[simp] theorem vertexMemory_zero (memory : ℕ → ℕ) (base count : ℕ) (values : List ℕ) :
    vertexMemory memory base count values 0 = memory := rfl

theorem vertexMemory_succ (memory : ℕ → ℕ) (base count : ℕ) (values : List ℕ) (q : ℕ) :
    vertexMemory memory base count values (q + 1) =
      upd (vertexMemory memory base count values q) (4 * (base + 2 * count + 3 + q) + 2)
        (values.getD q 0) := by simp [vertexMemory, List.range_succ]

theorem vertexMemory_outside {memory : ℕ → ℕ} {base count q a : ℕ} {values : List ℕ}
    (ha : a < 4 * (base + 2 * count + 3) + 2 ∨
      4 * (base + 2 * count + 3 + q) + 2 ≤ a ∨ a % 4 ≠ 2) :
    vertexMemory memory base count values q a = memory a := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [vertexMemory_succ]
    simp only [upd, ite_eq_right (show a ≠ 4 * (base + 2 * count + 3 + q) + 2 by omega)]
    exact ih (by omega)

theorem vertexMemory_get {memory : ℕ → ℕ} {base count q i : ℕ} {values : List ℕ} (hi : i < q) :
    vertexMemory memory base count values q (4 * (base + 2 * count + 3 + i) + 2) = values.getD i 0 := by
  induction q with
  | zero => omega
  | succ q ih =>
    rw [vertexMemory_succ]
    by_cases he : i = q
    · subst i; simp [upd]
    · simp only [upd, ite_eq_right (show 4 * (base + 2 * count + 3 + i) + 2 ≠
          4 * (base + 2 * count + 3 + q) + 2 by omega)]
      exact ih (by omega)

def VertexGlobals (source base count : ℕ) (c : Config) : Prop :=
  c.reg gV = source ∧ c.reg coreBase = base ∧ c.reg gKT = count ∧ c.reg coreTwo = 2

def VertexInv (source base : ℕ) (values : List ℕ) (memory : ℕ → ℕ) (out : List ℕ)
    (q : ℕ) (c : Config) : Prop :=
  VertexGlobals source base values.length c ∧
    c.mem = vertexMemory memory base values.length values q ∧ c.out = out

theorem vertexPut_spec {S source base : ℕ} {values : List ℕ} {memory : ℕ → ℕ} {out : List ℕ}
    (hvalues : Arr memory source values) (hsep : source + values.length ≤ 4 * base + 2)
    (hS : 4 * (base + 3 * values.length + 3) + 2 ≤ S) (q : ℕ) (hq : q < values.length) :
    HTB S vertexPut
      (fun c => VertexInv source base values memory out q c ∧ c.reg copyIndex = q ∧ c.reg gKT = values.length)
      (fun c => VertexInv source base values memory out (q + 1) c ∧ c.reg copyIndex = q ∧ c.reg gKT = values.length)
      11 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨⟨hs, hb, hn, htwo⟩, hm, ho⟩, hi, _⟩
  have hread : c.mem (source + q) = values.getD q 0 := by
    rw [hm, vertexMemory_outside (Or.inl (by omega))]
    exact hvalues.getD hq
  refine ⟨?_, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · addr_ok [vertexPut, hs, hb, hn, htwo, hi]
  all_goals simp +decide only [vertexPut, run_seq', run_ld, run_add, run_addc,
    run_store, setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd, setReg_out,
    setMem_out, hs, hb, hn, htwo, hi, hread, hm, ho, ↓reduceIte]
  · rw [vertexMemory_succ]
    congr 1
    ring

theorem vertexLoop_spec {S source base : ℕ} {values : List ℕ} {memory : ℕ → ℕ} {out : List ℕ}
    (hvalues : Arr memory source values) (hsep : source + values.length ≤ 4 * base + 2)
    (hS : 4 * (base + 3 * values.length + 3) + 2 ≤ S) :
    HTB S vertexLoop
      (fun c => VertexGlobals source base values.length c ∧ c.mem = memory ∧ c.out = out)
      (fun c => VertexGlobals source base values.length c ∧
        c.mem = vertexMemory memory base values.length values values.length ∧ c.out = out)
      (15 * values.length + 3) := by
  have hl := HTB.forUpC (S := S) (i := copyIndex) (n := gKT) (N := values.length)
    (body := vertexPut) (VertexInv source base values memory out) 11
    (by decide) (by decide) (by decide) (fun _ => by indep [VertexInv, VertexGlobals])
    (fun q hq => vertexPut_spec hvalues hsep hS q hq)
  refine hl.mono ?_ (fun c h => h.1) (by omega)
  rintro c ⟨hg, hm, ho⟩
  exact ⟨⟨hg, by simpa [vertexMemory_zero] using hm, ho⟩, hg.2.2.1⟩

def EdgeGlobals (source base k t : ℕ) (c : Config) : Prop :=
  c.reg gV = source ∧ c.reg coreBase = base ∧ c.reg gK = k ∧ c.reg gT = t ∧
    c.reg coreTwo = 2 ∧ c.reg coreFour = 4

def EdgeInv (g : Graph) (k source base : ℕ) (memory : ℕ → ℕ) (out : List ℕ)
    (q : ℕ) (c : Config) : Prop :=
  EdgeGlobals source base k (cycles g k).length c ∧
    c.mem = edgeMemory memory base (occs g k) q ∧ c.out = out

def RowInv (g : Graph) (k source base : ℕ) (memory : ℕ → ℕ) (out : List ℕ)
    (i j : ℕ) (c : Config) : Prop :=
  EdgeInv g k source base memory out (i * k + j) c ∧ c.reg sBase = i * k ∧ c.reg sI = i

theorem edgeBody_spec {S k source base : ℕ} {g : Graph} {memory : ℕ → ℕ} {out : List ℕ}
    (hverts : Arr memory source (verts g k))
    (hsep : source + k * (cycles g k).length ≤ 4 * base + 2)
    (hS : 4 * (base + 1 + 2 * (k * (cycles g k).length)) + 2 ≤ S)
    (i j : ℕ) (hi : i < (cycles g k).length) (hj : j < k) :
    HTB S edgeBody
      (fun c => RowInv g k source base memory out i j c ∧ c.reg sJ = j ∧ c.reg gK = k)
      (fun c => RowInv g k source base memory out i (j + 1) c ∧ c.reg sJ = j ∧ c.reg gK = k) 40 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨⟨hg, hm, ho⟩, hb, hiReg⟩, hjReg, hkReg⟩
  rcases hg with ⟨hs, hbase, hk, ht, htwo, hfour⟩
  have hq := occ_lt hi hj
  have hv : Arr c.mem source (verts g k) := by
    intro a ha
    rw [hm, edgeMemory_outside (Or.inl (by rw [length_verts] at ha; omega))]
    exact hverts a ha
  obtain ⟨rq, rx, ry, agreeRead, haddrRead⟩ :=
    readEdge_run (S := S) (by omega) hi hj hv hs hk hjReg hb
  have hrbase : (run readEdge c).reg coreBase = base :=
    (agreeRead.reg _ (by decide)).trans hbase
  have hrtwo : (run readEdge c).reg coreTwo = 2 :=
    (agreeRead.reg _ (by decide)).trans htwo
  have hrfour : (run readEdge c).reg coreFour = 4 :=
    (agreeRead.reg _ (by decide)).trans hfour
  have hfinal : (run edgeBody c).mem =
      upd (upd c.mem (4 * (base + 1 + 2 * (i * k + j)) + 2)
        ((occs g k).getD (i * k + j) (0, 0)).1)
        (4 * (base + 2 + 2 * (i * k + j)) + 2)
        ((occs g k).getD (i * k + j) (0, 0)).2 := by
    change (run putEdge (run readEdge c)).mem = _
    generalize run readEdge c = cr at rq rx ry hrbase hrtwo hrfour agreeRead ⊢
    simp +decide only [putEdge, run_seq', run_add, run_addc,
      run_store, setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd,
      rq, rx, ry, hrbase, hrtwo, hrfour, agreeRead.mem, ↓reduceIte]
    have hfirst : base + (i * k + j + (i * k + j) + 1) +
        (base + (i * k + j + (i * k + j) + 1)) +
        (base + (i * k + j + (i * k + j) + 1) +
          (base + (i * k + j + (i * k + j) + 1))) + 2 =
          4 * (base + 1 + 2 * (i * k + j)) + 2 := by ring
    rw [hfirst, show 4 * (base + 1 + 2 * (i * k + j)) + 2 + 4 =
      4 * (base + 2 + 2 * (i * k + j)) + 2 by ring]
  have hglobals : EdgeGlobals source base k (cycles g k).length (run edgeBody c) :=
    (show RegIndep (wregs edgeBody) (EdgeGlobals source base k (cycles g k).length) by
      indep [EdgeGlobals, edgeBody, readEdge, edgeA, nextPos, minmax, putEdge,
        forUp, ifLt, swap, ld, addc, mov]).run (by decide) ⟨hs, hbase, hk, ht, htwo, hfour⟩
  refine ⟨AddrOK.seq haddrRead (by addr_ok [putEdge, rq, rx, ry, hrbase, hrtwo, hrfour]),
    ⟨⟨hglobals, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · rw [hfinal, hm, show i * k + (j + 1) = i * k + j + 1 by omega, edgeMemory_succ]
  · exact (run_out_of_writes (by decide) (by decide) c).trans ho
  · exact (run_reg_of_not_mem (by decide) (by decide) c).trans hb
  · exact (run_reg_of_not_mem (by decide) (by decide) c).trans hiReg
  · exact (run_reg_of_not_mem (by decide) (by decide) c).trans hjReg
  · exact hglobals.2.2.1

theorem edgeRow_spec {S k source base : ℕ} {g : Graph} {memory : ℕ → ℕ} {out : List ℕ}
    (hverts : Arr memory source (verts g k))
    (hsep : source + k * (cycles g k).length ≤ 4 * base + 2)
    (hS : 4 * (base + 1 + 2 * (k * (cycles g k).length)) + 2 ≤ S)
    (i : ℕ) (hi : i < (cycles g k).length) :
    HTB S edgeRow
      (fun c => EdgeInv g k source base memory out (i * k) c ∧ c.reg sBase = i * k ∧
        c.reg sI = i ∧ c.reg gT = (cycles g k).length)
      (fun c => EdgeInv g k source base memory out ((i + 1) * k) c ∧
        c.reg sBase = (i + 1) * k ∧ c.reg sI = i ∧ c.reg gT = (cycles g k).length)
      (44 * k + 4) := by
  have hl := HTB.forUpC (S := S) (i := sJ) (n := gK) (N := k) (body := edgeBody)
    (fun j c => RowInv g k source base memory out i j c ∧ c.reg gT = (cycles g k).length) 40
    (by decide) (by decide) (by decide)
    (fun _ => by indep [RowInv, EdgeInv, EdgeGlobals])
    (fun j hj => (edgeBody_spec hverts hsep hS i j hi hj).frameReg
      (F := fun c => c.reg gT = (cycles g k).length)
      (by intro c c' hreg hg; exact (hreg _ (by decide)).trans hg)
      |>.mono (fun c h => ⟨⟨h.1.1, h.2.1, h.2.2⟩, h.1.2⟩)
        (fun c h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩) le_rfl)
  have hadd : HTB S (.add sBase sBase gK)
      (fun c => (RowInv g k source base memory out i k c ∧ c.reg gT = (cycles g k).length) ∧
        c.reg sJ = k ∧ c.reg gK = k)
      (fun c => EdgeInv g k source base memory out ((i + 1) * k) c ∧
        c.reg sBase = (i + 1) * k ∧ c.reg sI = i ∧ c.reg gT = (cycles g k).length) 1 := by
    refine HTB.run_le (by decide) (by decide) ?_
    rintro c ⟨⟨⟨hstate, hb, hi⟩, ht⟩, _, hk⟩
    have hstate' : EdgeInv g k source base memory out ((i + 1) * k) c := by
      rwa [show (i + 1) * k = i * k + k by ring]
    refine ⟨AddrOK.of_memFree rfl, ?_, ?_, ?_, ?_⟩
    · exact (show Indep [sBase] (EdgeInv g k source base memory out ((i + 1) * k)) by
        indep [EdgeInv, EdgeGlobals]).setReg (by decide) _ hstate'
    · simp +decide [hb, hk]; ring
    · simp +decide [hi]
    · simp +decide [ht]
  refine (hl.seq hadd).mono ?_ (fun c h => h) (by omega)
  rintro c ⟨hstate, hb, hiReg, ht⟩
  exact ⟨⟨⟨by simpa using hstate, hb, hiReg⟩, ht⟩, hstate.1.2.2.1⟩

def CycleInv (g : Graph) (k source base : ℕ) (memory : ℕ → ℕ) (out : List ℕ)
    (i : ℕ) (c : Config) : Prop :=
  EdgeInv g k source base memory out (i * k) c ∧ c.reg sBase = i * k

theorem edgeLoop_spec {S k source base : ℕ} {g : Graph} {memory : ℕ → ℕ} {out : List ℕ}
    (hverts : Arr memory source (verts g k))
    (hsep : source + k * (cycles g k).length ≤ 4 * base + 2)
    (hS : 4 * (base + 1 + 2 * (k * (cycles g k).length)) + 2 ≤ S) :
    HTB S edgeLoop
      (fun c => EdgeGlobals source base k (cycles g k).length c ∧ c.mem = memory ∧ c.out = out)
      (fun c => EdgeInv g k source base memory out (k * (cycles g k).length) c)
      (44 * k * (cycles g k).length + 8 * (cycles g k).length + 4) := by
  have hz : HTB S (.const sBase 0)
      (fun c => EdgeGlobals source base k (cycles g k).length c ∧ c.mem = memory ∧ c.out = out)
      (fun c => CycleInv g k source base memory out 0 c ∧ c.reg gT = (cycles g k).length) 1 := by
    refine HTB.run_le (by decide) (by decide) ?_
    rintro c ⟨hg, hm, ho⟩
    refine ⟨AddrOK.of_memFree rfl, ⟨?_, ?_⟩, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · exact (show RegIndep [sBase] (EdgeGlobals source base k (cycles g k).length) by
          indep [EdgeGlobals]).setReg (by decide) _ hg
      · simpa [edgeMemory_zero] using hm
      · exact ho
    · simp
    · simpa using hg.2.2.2.1
  have hl := HTB.forUpC (S := S) (i := sI) (n := gT) (N := (cycles g k).length)
    (body := edgeRow) (CycleInv g k source base memory out) (44 * k + 4)
    (by decide) (by decide) (by decide) (fun _ => by indep [CycleInv, EdgeInv, EdgeGlobals])
    (fun i hi => (edgeRow_spec (out := out) hverts hsep hS i hi).mono
      (fun c h => ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩)
      (fun c h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩) le_rfl)
  refine (hz.seq hl).mono (fun c h => h) ?_ (by ring_nf; omega)
  rintro c ⟨⟨hstate, _⟩, _, _⟩
  simpa only [Nat.mul_comm] using hstate

theorem headerMemory_outside {memory : ℕ → ℕ} {base count k t budget a : ℕ}
    (ha : a ≠ 4 * base + 2 ∧ a ≠ 4 * (base + 2 * count + 1) + 2 ∧
      a ≠ 4 * (base + 2 * count + 2) + 2 ∧ a ≠ 4 * (base + 3 * count + 3) + 2) :
    headerMemory memory base count k t budget a = memory a := by
  simp only [headerMemory, upd, ite_eq_right ha.2.2.2, ite_eq_right ha.2.2.1,
    ite_eq_right ha.2.1, ite_eq_right ha.1]

theorem headerMemory_fields (memory : ℕ → ℕ) (base count k t budget : ℕ) :
    headerMemory memory base count k t budget (4 * base + 2) = count ∧
    headerMemory memory base count k t budget (4 * (base + 2 * count + 1) + 2) = k ∧
    headerMemory memory base count k t budget (4 * (base + 2 * count + 2) + 2) = t ∧
    headerMemory memory base count k t budget (4 * (base + 3 * count + 3) + 2) = budget := by
  simp only [headerMemory, upd]
  split_ifs <;> omega

def coreMemory (memory : ℕ → ℕ) (base : ℕ) (g : Graph) (k budget : ℕ) : ℕ → ℕ :=
  let count := k * (cycles g k).length
  headerMemory (vertexMemory (edgeMemory memory base (occs g k) count)
    base count (verts g k) count) base count k (cycles g k).length budget

def coreInput (g : Graph) (k budget : ℕ) : List ℕ :=
  graphInput (coreOccurrenceGraph g k) ++ k :: (cycles g k).length :: (verts g k ++ [budget])

theorem coreInput_length (g : Graph) (k budget : ℕ) :
    (coreInput g k budget).length = 3 * (k * (cycles g k).length) + 4 := by
  simp [coreInput, length_graphInput, coreOccurrenceGraph_length, length_verts]
  ring

theorem coreInput_semantic (g : Graph) (k budget : ℕ) :
    coreInput g k budget = boundedCostInput (coreOccurrenceGraph g k) k budget := by
  simp [coreInput, boundedCostInput, zeroCostInput, verts, coreOccurrenceGraph_cycles,
    List.append_assoc]

theorem coreMemory_input (memory : ℕ → ℕ) (base : ℕ) (g : Graph) (k budget : ℕ) :
    Flow.OffsetInput (coreMemory memory base g k budget) base (coreInput g k budget) := by
  let count := k * (cycles g k).length
  let pairs := occs g k
  let values := verts g k
  let next := coreMemory memory base g k budget
  let strided := fun a => next (4 * a + 2)
  have hpairs : pairs.length = count := length_occs g k
  have hvalues : values.length = count := length_verts g k
  have hhead := headerMemory_fields
    (vertexMemory (edgeMemory memory base pairs count) base count values count)
      base count k (cycles g k).length budget
  have he (i : ℕ) (hi : i < count) :
      next (4 * (base + 1 + 2 * i) + 2) = (pairs.getD i (0, 0)).1 ∧
      next (4 * (base + 2 + 2 * i) + 2) = (pairs.getD i (0, 0)).2 := by
    have hp := edgeMemory_pair (memory := memory) (base := base) (edges := pairs) hi
    constructor
    · dsimp only [next, coreMemory]
      rw [headerMemory_outside (by dsimp [count] at hi ⊢; omega),
        vertexMemory_outside (Or.inl (by dsimp [count] at hi ⊢; omega))]
      exact hp.1
    · dsimp only [next, coreMemory]
      rw [headerMemory_outside (by dsimp [count] at hi ⊢; omega),
        vertexMemory_outside (Or.inl (by dsimp [count] at hi ⊢; omega))]
      exact hp.2
  have hv (i : ℕ) (hi : i < count) :
      next (4 * (base + 2 * count + 3 + i) + 2) = values.getD i 0 := by
    dsimp only [next, coreMemory]
    rw [headerMemory_outside (by dsimp [count] at hi ⊢; omega)]
    exact vertexMemory_get hi
  apply (show Arr strided base (coreInput g k budget) →
      Flow.OffsetInput (coreMemory memory base g k budget) base (coreInput g k budget) from
    fun h i hi => h.getD hi)
  rw [coreInput, arr_append]
  constructor
  · change Arr strided base (pairs.length :: R0.ents pairs)
    rw [arr_cons]
    refine ⟨?_, ?_⟩
    · dsimp [strided, next, coreMemory, count, values, pairs] at hhead ⊢
      simpa only [length_occs] using hhead.1
    · intro i hi
      have hi' : i < 2 * count := by simpa only [R0.length_ents, hpairs] using hi
      have hq : i / 2 < count := by omega
      have hq' : i / 2 < pairs.length := by omega
      obtain ⟨hl, hr⟩ := R0.ents_pair pairs (i / 2) hq'
      have hg := he (i / 2) hq
      have helem : pairs[i / 2] = pairs.getD (i / 2) (0, 0) :=
        List.getElem_eq_getD (h := hq') (0, 0)
      have hl' : (R0.ents pairs).getD (2 * (i / 2)) 0 = (pairs.getD (i / 2) (0, 0)).1 := by
        rw [← List.getElem_eq_getD (h := by simp [R0.length_ents]; omega) 0, hl, helem]
      have hr' : (R0.ents pairs).getD (2 * (i / 2) + 1) 0 = (pairs.getD (i / 2) (0, 0)).2 := by
        rw [← List.getElem_eq_getD (h := by simp [R0.length_ents]; omega) 0, hr, helem]
      rw [List.getElem_eq_getD (h := hi) 0]
      by_cases hmod : i % 2 = 0
      · have ie : i = 2 * (i / 2) := by omega
        have ha : 4 * (base + 1 + i) + 2 = 4 * (base + 1 + 2 * (i / 2)) + 2 := by omega
        dsimp only [strided]
        rw [ha, hg.1, congrArg (fun x => (R0.ents pairs).getD x 0) ie, hl']
      · have ie : i = 2 * (i / 2) + 1 := by omega
        have ha : 4 * (base + 1 + i) + 2 = 4 * (base + 2 + 2 * (i / 2)) + 2 := by omega
        dsimp only [strided]
        rw [ha, hg.2]
        rw [congrArg (fun x => (R0.ents pairs).getD x 0) ie, hr']
  · rw [length_graphInput, coreOccurrenceGraph_length, arr_cons, arr_cons, arr_append]
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp [strided, next, coreMemory, count, values, pairs] at hhead ⊢
      simpa only [Nat.add_zero, Nat.add_assoc] using hhead.2.1
    · dsimp [strided, next, coreMemory, count, values, pairs] at hhead ⊢
      convert hhead.2.2.1 using 1 <;> congr 1 <;> omega
    · intro i hi
      have hi' : i < count := by simpa only [length_verts] using hi
      have hg := hv i hi'
      have helem : values[i] = values.getD i 0 := List.getElem_eq_getD (h := hi) 0
      dsimp only [strided]
      rw [show 4 * (base + (2 * (k * (cycles g k).length) + 1) + 1 + 1 + i) + 2 =
          4 * (base + 2 * count + 3 + i) + 2 by dsimp [count]; omega, hg, ← helem]
    · rw [arr_singleton]
      dsimp [strided, next, coreMemory, count, values, pairs] at hhead ⊢
      rw [length_verts]
      convert hhead.2.2.2 using 1 <;> congr 1 <;> omega

def ready : Stmt := .seq (.const coreTwo 2) (.seq (.const coreFour 4)
  (.seq (mov coreBase rFREE) (.seq (.add coreLength gKT gKT)
    (.seq (.add coreLength coreLength gKT)
      (.seq (addc coreLength coreLength 4) (.const coreBudget 0))))))

def CoreGlobals (g : Graph) (k : ℕ) (c : Config) : Prop :=
  EdgeGlobals (bV g) (bD g k) k (cycles g k).length c ∧
    c.reg gKT = k * (cycles g k).length ∧
    c.reg coreLength = 3 * (k * (cycles g k).length) + 4 ∧ c.reg coreBudget = 0

def program : Stmt := .seq stepInit (.seq ready (.seq edgeLoop (.seq vertexLoop header)))

def coreSpace (g : Graph) (k : ℕ) : ℕ :=
  4 * (bD g k + 3 * (k * (cycles g k).length) + 4) + 4

theorem CoreGlobals.transfer {g : Graph} {k : ℕ} {c c' : Config}
    (h : CoreGlobals g k c)
    (hreg : ∀ r ∈ [gV, coreBase, gK, gT, coreTwo, coreFour, gKT, coreLength, coreBudget],
      c'.reg r = c.reg r) : CoreGlobals g k c' := by
  obtain ⟨⟨hs, hb, hk, ht, htwo, hfour⟩, hn, hl, hbudget⟩ := h
  exact ⟨⟨(hreg _ (by decide)).trans hs, (hreg _ (by decide)).trans hb,
    (hreg _ (by decide)).trans hk, (hreg _ (by decide)).trans ht,
    (hreg _ (by decide)).trans htwo, (hreg _ (by decide)).trans hfour⟩,
    (hreg _ (by decide)).trans hn, (hreg _ (by decide)).trans hl,
    (hreg _ (by decide)).trans hbudget⟩

theorem ready_spec {g : Graph} {k S : ℕ} :
    HTB S ready (fun c => InitPost g k c ∧ c.mem = (initial (zeroCostInput g k)).mem)
      (fun c => CoreGlobals g k c ∧ c.mem = (initial (zeroCostInput g k)).mem ∧ c.out = []) 9 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨h, hm⟩
  obtain ⟨⟨hk, ht, hv, hn, _⟩, hb, _, _, ho⟩ := h
  refine ⟨AddrOK.of_memFree rfl, ?_⟩
  simp +decide only [ready, CoreGlobals, EdgeGlobals, run_seq', run_const,
    run_mov, run_add, run_addc, setReg_reg, setReg_mem, setReg_out, hk, ht, hv,
    hn, hb, ho, hm, ↓reduceIte]
  simp only [true_and, and_true]
  omega

theorem program_spec {g : Graph} {k S : ℕ} (hk : 1 ≤ k) (hS : coreSpace g k ≤ S) :
    HTB S program (· = initial (zeroCostInput g k))
      (fun c => CoreGlobals g k c ∧
        Flow.OffsetInput c.mem (bD g k) (coreInput g k 0) ∧ c.out = [])
      (100 * (k * (cycles g k).length + 1)) := by
  intro c hc
  subst c
  let memory := (initial (zeroCostInput g k)).mem
  have hsmall : bD g k ≤ S := by dsimp [coreSpace] at hS; omega
  have hsep : bV g + k * (cycles g k).length ≤ 4 * bD g k + 2 := by
    dsimp [bV, bD]
    omega
  have hedgeS : 4 * (bD g k + 1 + 2 * (k * (cycles g k).length)) + 2 ≤ S := by
    dsimp [coreSpace] at hS
    omega
  have hvertexS : 4 * (bD g k + 3 * (verts g k).length + 3) + 2 ≤ S := by
    rw [length_verts]
    dsimp [coreSpace] at hS
    omega
  have hheaderS : 4 * (bD g k + 3 * (k * (cycles g k).length) + 3) + 2 < S := by
    dsimp [coreSpace] at hS
    omega
  obtain ⟨c₁, t₁, he₁, hs₁, ht₁⟩ := stepInit_spec g k hsmall (initial (zeroCostInput g k)) rfl
  have hm₁ : c₁.mem = memory := he₁.mem_frame (by decide)
  obtain ⟨c₂, t₂, he₂, ⟨hg₂, hm₂, ho₂⟩, ht₂⟩ := ready_spec c₁ ⟨hs₁, hm₁⟩
  have hverts : Arr memory (bV g) (verts g k) := (input_facts g k).2.2.2.1
  obtain ⟨c₃, t₃, he₃, ⟨heg₃, hm₃, ho₃⟩, ht₃⟩ :=
    edgeLoop_spec (out := []) hverts hsep hedgeS c₂ ⟨hg₂.1, hm₂, ho₂⟩
  have hg₃ : CoreGlobals g k c₃ := by
    refine ⟨heg₃, ?_, ?_, ?_⟩
    · exact (he₃.reg_frame (by decide)).trans hg₂.2.1
    · exact (he₃.reg_frame (by decide)).trans hg₂.2.2.1
    · exact (he₃.reg_frame (by decide)).trans hg₂.2.2.2
  have hverts₃ : Arr c₃.mem (bV g) (verts g k) := by
    intro i hi
    rw [hm₃, edgeMemory_outside (Or.inl (by rw [length_verts] at hi; omega))]
    exact hverts i hi
  have hvGlobals : VertexGlobals (bV g) (bD g k) (verts g k).length c₃ := by
    rw [length_verts]
    exact ⟨hg₃.1.1, hg₃.1.2.1, hg₃.2.1, hg₃.1.2.2.2.2.1⟩
  obtain ⟨c₄, t₄, he₄, ⟨_, hm₄, ho₄⟩, ht₄⟩ :=
    vertexLoop_spec hverts₃ (by simpa only [length_verts] using hsep) hvertexS c₃ ⟨hvGlobals, rfl, ho₃⟩
  have hg₄ : CoreGlobals g k c₄ := by
    apply hg₃.transfer
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact he₄.reg_frame (by decide)
  have hhGlobals : HeaderGlobals (bD g k) (k * (cycles g k).length) k (cycles g k).length 0 c₄ :=
    ⟨hg₄.1.2.1, hg₄.2.1, hg₄.1.2.2.1, hg₄.1.2.2.2.1, hg₄.2.2.2, hg₄.1.2.2.2.2.1⟩
  obtain ⟨c₅, t₅, he₅, ⟨_, hm₅, ho₅⟩, ht₅⟩ :=
    header_spec hheaderS c₄ ⟨hhGlobals, rfl, ho₄⟩
  have hg₅ : CoreGlobals g k c₅ := by
    apply hg₄.transfer
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact he₅.reg_frame (by decide)
  have hinput : Flow.OffsetInput c₅.mem (bD g k) (coreInput g k 0) := by
    rw [hm₅, hm₄, hm₃, length_verts]
    exact coreMemory_input memory (bD g k) g k 0
  have ht : (cycles g k).length ≤ k * (cycles g k).length := Nat.le_mul_of_pos_left _ hk
  refine ⟨c₅, t₁ + (t₂ + (t₃ + (t₄ + t₅))),
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ he₅))), ⟨hg₅, hinput, ho₅⟩, ?_⟩
  rw [length_verts] at ht₄
  rw [Nat.mul_assoc] at ht₃
  omega

def callerProgram : Stmt := onCallerRegisters program

theorem callerProgram_spec {g : Graph} {k S : ℕ} (hk : 1 ≤ k) (hS : coreSpace g k ≤ S) :
    HTB S callerProgram (· = initial (zeroCostInput g k))
      (fun c => CoreGlobals g k (registerView callerRegister c) ∧
        Flow.OffsetInput c.mem (bD g k) (coreInput g k 0) ∧ c.out = [] ∧
        ∀ r, c.reg (Flow.rl 0 r) = 0)
      (100 * (k * (cycles g k).length + 1)) := by
  have h := onCallerRegisters_htb (program_spec hk hS)
  intro c hc
  subst c
  have hv : registerView callerRegister (initial (zeroCostInput g k)) = initial (zeroCostInput g k) := by
    simp [registerView, initial]
  obtain ⟨d, t, he, hd, ht⟩ := h (initial (zeroCostInput g k)) hv
  refine ⟨d, t, he, ⟨hd.1, hd.2.1, hd.2.2, ?_⟩, ht⟩
  intro r
  exact (callerRegister_exec_zero he r).trans (initial_reg _ _)

end STACS2027.Runtimes.BoundedCost.CoreRAM
