module

public import Runtimes.GeneralCycles.RegTests
public import Runtimes.GeneralCycles.Definitions
import Mathlib.Tactic

/-!
# Label-independent edge membership on the RAM

The input edge list is scanned at consecutive addresses. Vertex labels are
compared as register values and never used as addresses. Artifact date:
2026-10-12.
-/

@[expose] public section

namespace STACS2027.Runtimes.GeneralCycles

open STACS2027 STACS2027.RAM

abbrev edgeCount : ℕ := 11
abbrev edgeCounter : ℕ := 20
abbrev edgeAddr : ℕ := 21
abbrev edgeFirst : ℕ := 22
abbrev edgeSecond : ℕ := 23
abbrev edgeFound : ℕ := 24

def edgeScratch : List ℕ := [rT, edgeCounter, edgeAddr, edgeFirst, edgeSecond, edgeFound]

def edgeWrites : List ℕ := [rT, edgeAddr, edgeFirst, edgeSecond, edgeFound]

def readEdge : Stmt :=
  .seq (.add edgeAddr edgeCounter edgeCounter)
    (.seq (addc edgeAddr edgeAddr 1)
      (.seq (.load edgeFirst edgeAddr)
        (.seq (addc edgeAddr edgeAddr 1) (.load edgeSecond edgeAddr))))

def inputEdgeTest (a b : ℕ) : RegTest :=
  .either
    (.both (.neg (.less b a)) (.both (.equal a edgeFirst) (.equal b edgeSecond)))
    (.both (.less b a) (.both (.equal b edgeFirst) (.equal a edgeSecond)))

def markEdge (a b : ℕ) : Stmt := (inputEdgeTest a b).branch (.const edgeFound 1) .skip

def edgeBody (a b : ℕ) : Stmt := .seq readEdge (markEdge a b)

def scanEdge (a b : ℕ) : Stmt :=
  .seq (.const edgeFound 0) (forUp edgeCounter edgeCount (edgeBody a b))

theorem inputEdgeTest_eval (a b : ℕ) (c : Config) :
    (inputEdgeTest a b).eval c = decide
      (edge (c.reg a) (c.reg b) = (c.reg edgeFirst, c.reg edgeSecond)) := by
  by_cases h : c.reg b < c.reg a
  · have hle : c.reg b ≤ c.reg a := Nat.le_of_lt h
    simp [inputEdgeTest, RegTest.eval, edge, Nat.min_eq_right hle, Nat.max_eq_left hle, h]
  · have hle : c.reg a ≤ c.reg b := by omega
    simp [inputEdgeTest, RegTest.eval, edge, Nat.min_eq_left hle, Nat.max_eq_right hle, h]

theorem inputEdgeTest_safe {a b : ℕ} (ha : 50 ≤ a) (hb : 50 ≤ b) :
    rT ∉ (inputEdgeTest a b).sources := by
  simp [inputEdgeTest, RegTest.sources, edgeFirst, edgeSecond, rT]
  omega

theorem readEdge_loopFree : LoopFree readEdge := by simp [readEdge, LoopFree]

theorem markEdge_loopFree (a b : ℕ) : LoopFree (markEdge a b) :=
  (inputEdgeTest a b).branch_loopFree trivial trivial

theorem edgeBody_loopFree (a b : ℕ) : LoopFree (edgeBody a b) :=
  ⟨readEdge_loopFree, markEdge_loopFree a b⟩

theorem markEdge_memFree (a b : ℕ) : memFree (markEdge a b) = true :=
  (inputEdgeTest a b).branch_memFree rfl rfl

theorem edgeBody_stores (a b : ℕ) : stores (edgeBody a b) = false := by
  have hm := (inputEdgeTest a b).branch_stores (s := .const edgeFound 1) (u := .skip) rfl rfl
  simpa [edgeBody, markEdge, readEdge, stores] using hm

theorem edgeBody_writes (a b : ℕ) : writes (edgeBody a b) = false := by
  have hm := (inputEdgeTest a b).branch_writes (s := .const edgeFound 1) (u := .skip) rfl rfl
  simpa [edgeBody, markEdge, readEdge, writes] using hm

theorem edgeBody_wregs {a b r : ℕ} (hr : r ∈ wregs (edgeBody a b)) : r ∈ edgeWrites := by
  simp only [edgeBody, wregs, List.mem_append] at hr
  rcases hr with hr | hr
  · simp [readEdge, wregs] at hr
    simp [edgeWrites]
    tauto
  · rcases (inputEdgeTest a b).branch_wregs hr with h | h | h
    · simp [edgeWrites, h]
    · simp [wregs] at h
      simp [edgeWrites, h]
    · simp [wregs] at h

theorem edgeBody_agree (a b : ℕ) (c : Config) : Agree edgeWrites c (run (edgeBody a b) c) :=
  agree_run (edgeBody_loopFree a b) (edgeBody_stores a b) (edgeBody_writes a b)
    (fun _ => edgeBody_wregs) c

theorem readEdge_values (c : Config) :
    (run readEdge c).reg edgeFirst = c.mem (2 * c.reg edgeCounter + 1) ∧
    (run readEdge c).reg edgeSecond = c.mem (2 * c.reg edgeCounter + 2) ∧
    (run readEdge c).reg edgeFound = c.reg edgeFound := by
  simp [readEdge, addc, edgeCounter, edgeAddr, edgeFirst, edgeSecond, edgeFound, rT,
    Nat.two_mul, Nat.add_assoc]

theorem readEdge_reg {r : ℕ} (hr : r ∉ [rT, edgeAddr, edgeFirst, edgeSecond]) (c : Config) :
    (run readEdge c).reg r = c.reg r :=
  run_reg_of_not_mem readEdge_loopFree (by simp_all [readEdge, wregs]) c

theorem edgeBody_found {a b : ℕ} (ha : 50 ≤ a) (hb : 50 ≤ b) (c : Config) :
    (run (edgeBody a b) c).reg edgeFound =
      if edge (c.reg a) (c.reg b) =
        (c.mem (2 * c.reg edgeCounter + 1), c.mem (2 * c.reg edgeCounter + 2))
      then 1 else c.reg edgeFound := by
  let d := run readEdge c
  have ha' : a ∉ [rT, edgeAddr, edgeFirst, edgeSecond] := by
    simp [rT, edgeAddr, edgeFirst, edgeSecond]; omega
  have hb' : b ∉ [rT, edgeAddr, edgeFirst, edgeSecond] := by
    simp [rT, edgeAddr, edgeFirst, edgeSecond]; omega
  have hda := readEdge_reg ha' c
  have hdb := readEdge_reg hb' c
  have hv := readEdge_values c
  obtain ⟨v, he⟩ := (inputEdgeTest a b).run_branch (inputEdgeTest_safe ha hb)
    (.const edgeFound 1) .skip d
  simp only [edgeBody, run_seq', markEdge]
  rw [he]
  have ht : (inputEdgeTest a b).eval d = decide
      (edge (c.reg a) (c.reg b) =
        (c.mem (2 * c.reg edgeCounter + 1), c.mem (2 * c.reg edgeCounter + 2))) := by
    rw [inputEdgeTest_eval]
    simp only [d, hda, hdb, hv.1, hv.2.1]
  rw [ht]
  split <;> simp_all [d, edgeFound, rT]

def GraphMemory (g : Graph) (memory : ℕ → ℕ) : Prop :=
  ∀ j (hj : j < g.length), memory (2 * j + 1) = g[j].1 ∧
    memory (2 * j + 2) = g[j].2

theorem graphMemory_initial (g : Graph) : GraphMemory g (initial (graphInput g)).mem :=
  initial_graphInput_entry g

def EdgeInv (g : Graph) (memory : ℕ → ℕ) (P : Config → Prop)
    (a b x y j : ℕ) (c : Config) : Prop :=
  P c ∧ c.reg edgeCount = g.length ∧ c.mem = memory ∧ c.reg a = x ∧ c.reg b = y ∧
    c.reg edgeFound = if edge x y ∈ g.take j then 1 else 0

theorem edgeInv_indep {g : Graph} {memory : ℕ → ℕ} {P : Config → Prop}
    {a b x y j : ℕ} (ha : 50 ≤ a) (hb : 50 ≤ b) (hP : Indep edgeScratch P) :
    Indep [edgeCounter, rT] (EdgeInv g memory P a b x y j) := by
  intro c c' hag ⟨hp, hn, hm, hx, hy, hf⟩
  have hwide := hag.mono (show ∀ r ∈ [edgeCounter, rT], r ∈ edgeScratch by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [edgeScratch])
  have hna : a ∉ [edgeCounter, rT] := by simp [edgeCounter, rT]; omega
  have hnb : b ∉ [edgeCounter, rT] := by simp [edgeCounter, rT]; omega
  exact ⟨hP _ _ hwide hp, (hag.reg _ (by decide)).trans hn, hag.mem.trans hm,
    (hag.reg _ hna).trans hx, (hag.reg _ hnb).trans hy,
    (hag.reg _ (by decide)).trans hf⟩

theorem edgeBody_spec {g : Graph} {memory : ℕ → ℕ} {P : Config → Prop}
    {a b x y j S : ℕ} (ha : 50 ≤ a) (hb : 50 ≤ b) (hP : Indep edgeScratch P)
    (hmem : GraphMemory g memory) (hj : j < g.length) (hS : 2 * g.length + 1 ≤ S) :
    HTB S (edgeBody a b)
      (fun c => EdgeInv g memory P a b x y j c ∧ c.reg edgeCounter = j ∧
        c.reg edgeCount = g.length)
      (fun c => EdgeInv g memory P a b x y (j + 1) c ∧ c.reg edgeCounter = j ∧
        c.reg edgeCount = g.length) (size (edgeBody a b)) := by
  refine HTB.run (edgeBody_loopFree a b) ?_
  intro c ⟨⟨hp, hn, hm, hx, hy, hf⟩, hc, _⟩
  have hag := edgeBody_agree a b c
  have hwide : Agree edgeScratch c (run (edgeBody a b) c) := hag.mono (by
    intro r hr; simp only [edgeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [edgeScratch, List.mem_cons, List.not_mem_nil, or_false]
    tauto)
  have hna : a ∉ edgeWrites := by simp [edgeWrites, edgeAddr,
    edgeFirst, edgeSecond, edgeFound, rT]; omega
  have hnb : b ∉ edgeWrites := by simp [edgeWrites, edgeAddr,
    edgeFirst, edgeSecond, edgeFound, rT]; omega
  refine ⟨?_, ⟨hP _ _ hwide hp, (hag.reg _ (by decide)).trans hn, hag.mem.trans hm,
    (hag.reg _ hna).trans hx, (hag.reg _ hnb).trans hy, ?_⟩, ?_, ?_⟩
  · apply AddrOK.seq
    · simp [readEdge, addrOK_seq, run_seq', addc, hc, edgeCounter, edgeAddr,
        edgeFirst, edgeSecond, rT]
      omega
    · exact AddrOK.of_memFree (markEdge_memFree a b)
  · rw [edgeBody_found ha hb, hx, hy, hc, hm, (hmem j hj).1, (hmem j hj).2, hf,
      List.take_succ_eq_append_getElem hj]
    simp only [List.mem_append, List.mem_singleton]
    by_cases h : edge x y = g[j] <;> by_cases h' : edge x y ∈ g.take j <;> simp [h, h']
  · exact (hag.reg _ (by decide)).trans hc
  · exact (hag.reg _ (by decide)).trans hn

theorem scanEdge_spec {g : Graph} {memory : ℕ → ℕ} {P : Config → Prop}
    {a b x y S : ℕ} (ha : 50 ≤ a) (hb : 50 ≤ b) (hP : Indep edgeScratch P)
    (hmem : GraphMemory g memory) (hS : 2 * g.length + 1 ≤ S) :
    HTB S (scanEdge a b)
      (fun c => P c ∧ c.reg edgeCount = g.length ∧ c.mem = memory ∧
        c.reg a = x ∧ c.reg b = y)
      (fun c => P c ∧ c.reg edgeCount = g.length ∧ c.mem = memory ∧
        c.reg a = x ∧ c.reg b = y ∧
        c.reg edgeFound = if edge x y ∈ g then 1 else 0)
      (g.length * (size (edgeBody a b) + 4) + 4) := by
  have hinit : HTB S (.const edgeFound 0)
      (fun c => P c ∧ c.reg edgeCount = g.length ∧ c.mem = memory ∧
        c.reg a = x ∧ c.reg b = y)
      (fun c => EdgeInv g memory P a b x y 0 c ∧ c.reg edgeCount = g.length) 1 := by
    refine HTB.run_le trivial le_rfl ?_
    intro c ⟨hp, hn, hm, hx, hy⟩
    have hna : a ≠ edgeFound := by simp [edgeFound]; omega
    have hnb : b ≠ edgeFound := by simp [edgeFound]; omega
    refine ⟨trivial, ?_⟩
    change EdgeInv g memory P a b x y 0 (c.setReg edgeFound 0) ∧
      (c.setReg edgeFound 0).reg edgeCount = g.length
    refine ⟨⟨hP.setReg (by simp [edgeScratch]) _ hp, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [edgeCount, edgeFound] using hn
    · simpa using hm
    · simpa [setReg_reg, hna] using hx
    · simpa [setReg_reg, hnb] using hy
    · simp
    · simpa [edgeCount, edgeFound] using hn
  have hloop := HTB.forUpC (EdgeInv g memory P a b x y) (size (edgeBody a b))
    (by decide) (by decide) (by decide) (fun _ => edgeInv_indep ha hb hP)
    (fun _ hj => edgeBody_spec ha hb hP hmem hj hS)
  refine (hinit.seq hloop).mono (fun _ h => h) ?_ (by omega)
  rintro c ⟨⟨hp, hn, hm, hx, hy, hf⟩, _, _⟩
  exact ⟨hp, hn, hm, hx, hy, by simpa using hf⟩

end STACS2027.Runtimes.GeneralCycles
