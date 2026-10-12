module

public import Runtimes.Flow.EdgeSpec
public import Outerplanar.RAM.BoundedLib
import Mathlib.Tactic

/-!
# Theorem 4 for `k = 3`: the cost check on the RAM

The decision form of Theorem 4 for triangles (`Runtimes/BoundedCost/TriDecide.lean`) computes the
positions `pos` of an optimal assignment with the triangle pipeline and then compares its cost
with `Ψ`. This file is that comparison, `triCheck`, a RAM program on an input whose memory holds
`m` at cell `0`, `t` at cell `2m + 2`, the vertices `vs` of `t` triangles (three each) from cell
`bV = 2m + 3` on, `Ψ` at cell `bV + 3t` and the positions `ps` (`t` of them) after it — the layout
of `boundedCostInput g 3 Ψ ++ pos`.

**The abstract side.** In a triangle `c = [c₀, c₁, c₂]` the path left by deleting position
`p < 3` is the single edge between the two other vertices (`selected_tri`: positions
`off1 p`, `off2 p`); `triE vs ps i` is that edge for triangle `i`. The cost of a family of
single-edge paths is the number of pairs `i < j` with equal edges (`cost_tri`: `allc f n`, the
sum over `j < n` of `colc f j j = #{i < j : f i = f j}`).

**The program** `triCheck` (`O(t² + 1)` steps, it does not store, and it reads only the cells
of its input: `HTB S` for any `S` above the input): `checkInit` reads `m`, `t`,
`Ψ`; for every `j < t` (`outerBody`) it computes the edge of triangle `j` (`edgeAt`: the two
vertices read at the offsets of `p = ps[j]`, ordered with a subtraction test) and, for every
`i < j` (`innerBody`), the edge of triangle `i`, adding `1` to the counter when the two ordered
pairs are equal (`ifEq`); finally (`answer`) it writes `[0]` if the count exceeds `Ψ`, and `1`
followed by the positions otherwise (`triCheck_spec`).
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.Tri

open STACS2027 STACS2027.RAM

/-! ### The abstract side -/

/-- The first end of the edge left by deleting position `p` of a triangle. -/
def off1 (p : ℕ) : ℕ := if p = 0 then 1 else if p = 1 then 2 else 0

/-- The second end of the edge left by deleting position `p` of a triangle. -/
def off2 (p : ℕ) : ℕ := if p = 0 then 2 else if p = 1 then 0 else 1

theorem off1_lt (p : ℕ) : off1 p < 3 := by unfold off1; split_ifs <;> omega

theorem off2_lt (p : ℕ) : off2 p < 3 := by unfold off2; split_ifs <;> omega

/-- **The path of a triangle**: deleting position `p < 3` leaves the edge between the two other
vertices. -/
theorem selected_tri {c : Cycle} (hc : c.length = 3) {p : ℕ} (hp : p < 3) :
    selected c p = [edge (c.getD (off1 p) 0) (c.getD (off2 p) 0)] := by
  match c, hc with
  | [a, b, d], _ => interval_cases p <;> rfl

/-- The edge chosen in triangle `i`: the vertices `vs` (three per triangle) and the positions
`ps`. -/
def triE (vs ps : List ℕ) (i : ℕ) : Edge :=
  edge (vs.getD (i * 3 + off1 (ps.getD i 0)) 0) (vs.getD (i * 3 + off2 (ps.getD i 0)) 0)

/-- `#{i < n : f i = f j}`. -/
def colc (f : ℕ → Edge) (j n : ℕ) : ℕ := ((List.range n).filter fun i => f i = f j).length

/-- The number of pairs `i < j < n` with `f i = f j`. -/
def allc (f : ℕ → Edge) (n : ℕ) : ℕ := ((List.range n).map fun j => colc f j j).sum

theorem colc_zero (f : ℕ → Edge) (j : ℕ) : colc f j 0 = 0 := rfl

theorem colc_succ (f : ℕ → Edge) (j n : ℕ) :
    colc f j (n + 1) = colc f j n + if f n = f j then 1 else 0 := by
  unfold colc
  rw [List.range_succ, List.filter_append]
  by_cases h : f n = f j <;> simp [h]

theorem allc_zero (f : ℕ → Edge) : allc f 0 = 0 := rfl

theorem allc_succ (f : ℕ → Edge) (n : ℕ) : allc f (n + 1) = allc f n + colc f n n := by
  simp [allc, List.range_succ]

theorem overlap_single (x y : Edge) : overlap [x] [y] = if y = x then 1 else 0 := by
  by_cases h : y = x <;> simp [overlap, h]

theorem sum_overlap (f : ℕ → Edge) (j n : ℕ) :
    (((List.range n).map fun i => [f i]).map (overlap [f j])).sum = colc f j n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, ih, colc_succ]
    simp [overlap_single]

/-- **The cost of single-edge paths** is the number of pairs with equal edges. -/
theorem cost_tri (f : ℕ → Edge) (n : ℕ) : cost ((List.range n).map fun i => [f i]) = allc f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, cost_snoc, ih, sum_overlap, allc_succ]
    ring

/-! ### Registers -/

/-- `m`. -/
abbrev wM : ℕ := 10
/-- `bV = 2m + 3`, the address of the vertices. -/
abbrev wV : ℕ := 11
/-- `t`. -/
abbrev wT : ℕ := 12
/-- `bV + 3t`, the address of `Ψ`. -/
abbrev wD : ℕ := 13
/-- `Ψ`. -/
abbrev wS : ℕ := 14
/-- `bV + 3t + 1`, the address of the positions. -/
abbrev wP : ℕ := 15
/-- The outer counter `j`. -/
abbrev wJ : ℕ := 16
/-- The inner counter `i`. -/
abbrev wI : ℕ := 17
/-- The number of pairs with equal edges. -/
abbrev wN : ℕ := 18
/-- The smaller end of the edge of triangle `j`. -/
abbrev wA : ℕ := 19
/-- The larger end of the edge of triangle `j`. -/
abbrev wB : ℕ := 20
/-- The smaller end of the edge computed by `edgeAt`. -/
abbrev wX : ℕ := 21
/-- The larger end of the edge computed by `edgeAt`. -/
abbrev wY : ℕ := 22
/-- Scratch: the position. -/
abbrev wQ : ℕ := 23
/-- Scratch: the address of the triangle. -/
abbrev wU : ℕ := 24
/-- The first offset. -/
abbrev wO : ℕ := 25
/-- The second offset. -/
abbrev wO' : ℕ := 26
/-- A value to write. -/
abbrev wW : ℕ := 27
/-- The index of the triangle read by `edgeAt`. -/
abbrev wK : ℕ := 28

/-! ### The program -/

/-- `wQ := ps[wK]`; `wU := bV + 3 wK`; the offsets `wO = off1 wQ`, `wO' = off2 wQ`. -/
def edgePre : Stmt :=
  .seq (ld wQ wP wK) (.seq (.add wU wK wK) (.seq (.add wU wU wK) (.seq (.add wU wU wV)
    (.ifz wQ (.seq (.const wO 1) (.const wO' 2))
      (.seq (subc wQ wQ 1) (.ifz wQ (.seq (.const wO 2) (.const wO' 0))
        (.seq (.const wO 0) (.const wO' 1))))))))

/-- The edge of triangle `wK`, ordered: `wX ≤ wY`. -/
def edgeAt : Stmt :=
  .seq edgePre (.seq (ld wX wU wO) (.seq (ld wY wU wO') (ifLt wY wX (swap wX wY) .skip)))

/-- One pair `(i, j)`: `wN += 1` if the edge of triangle `i` is the edge `(wA, wB)` of `j`. -/
def innerBody : Stmt :=
  .seq (mov wK wI) (.seq edgeAt (ifEq wA wX (ifEq wB wY (inc wN) .skip) .skip))

/-- The edge of triangle `j` into `(wA, wB)`. -/
def outerPre : Stmt := .seq (mov wK wJ) (.seq edgeAt (.seq (mov wA wX) (mov wB wY)))

/-- Triangle `j`: the pairs `(i, j)`, `i < j`. -/
def outerBody : Stmt := .seq outerPre (forUp wI wJ innerBody)

/-- Reading `m`, `t`, `Ψ`; the addresses; `wN := 0`. -/
def checkInit : Stmt :=
  .seq (.load wM 0) (.seq (.add wV wM wM) (.seq (addc wV wV 3) (.seq (subc wU wV 1)
    (.seq (.load wT wU) (.seq (.add wD wT wT) (.seq (.add wD wD wT) (.seq (.add wD wD wV)
    (.seq (.load wS wD) (.seq (addc wP wD 1) (.const wN 0))))))))))

/-- Writing position `wI`. -/
def outBody : Stmt := .seq (ld wW wP wI) (.write wW)

/-- The answer `1` and the positions. -/
def ansYes : Stmt := .seq (.seq (.const wW 1) (.write wW)) (forUp wI wT outBody)

/-- The answer `[0]`. -/
def ansNo : Stmt := .seq (.const wW 0) (.write wW)

/-- The answer: `[0]` if `wN > Ψ`, else `1` and the positions. -/
def answer : Stmt := .seq (.sub wU wN wS) (.ifz wU ansYes ansNo)

/-- **The cost check.** -/
def triCheck : Stmt := .seq checkInit (.seq (forUp wJ wT outerBody) answer)

variable {S : ℕ}

/-! ### The edge of a triangle -/

theorem edgePre_run (c : Config) :
    (run edgePre c).reg wU = c.reg wK + c.reg wK + c.reg wK + c.reg wV ∧
      (run edgePre c).reg wO = off1 (c.mem (c.reg wP + c.reg wK)) ∧
      (run edgePre c).reg wO' = off2 (c.mem (c.reg wP + c.reg wK)) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals simp +decide only [edgePre, run_seq', run_ld, run_add, run_ifz', run_const,
    run_subc (show wQ ≠ rT by decide), setReg_reg, config_ite_reg, ↓reduceIte, off1, off2]
  · split_ifs <;> rfl
  · split_ifs <;> omega
  · split_ifs <;> omega

/-- **The edge of triangle `i`**, read by `edgeAt`. -/
theorem edgeAt_run {c : Config} {vs ps : List ℕ} {i : ℕ} (hk : c.reg wK = i)
    (hp : c.mem (c.reg wP + i) = ps.getD i 0)
    (hv : ∀ o, o < 3 → c.mem (c.reg wV + (i * 3 + o)) = vs.getD (i * 3 + o) 0) :
    (run edgeAt c).reg wX = (triE vs ps i).1 ∧ (run edgeAt c).reg wY = (triE vs ps i).2 ∧
      Agree [wQ, wU, wO, wO', wX, wY, rT] c (run edgeAt c) := by
  refine ⟨?_, ?_, agree_run (by decide) rfl rfl (by decide) c⟩ <;>
  · obtain ⟨hU, hO1, hO2⟩ := edgePre_run c
    have hm : (run edgePre c).mem = c.mem := run_mem_of_stores (by decide) rfl c
    rw [hk, hp] at hO1 hO2
    rw [hk] at hU
    have ha : (run edgePre c).mem ((run edgePre c).reg wU + (run edgePre c).reg wO) =
        vs.getD (i * 3 + off1 (ps.getD i 0)) 0 := by
      rw [hm, hU, hO1, ← hv _ (off1_lt _)]; congr 1; omega
    have hb : (run edgePre c).mem ((run edgePre c).reg wU + (run edgePre c).reg wO') =
        vs.getD (i * 3 + off2 (ps.getD i 0)) 0 := by
      rw [hm, hU, hO2, ← hv _ (off2_lt _)]; congr 1; omega
    simp only [edgeAt, run_seq', run_ld, run_ifLt, run_swap (show wX ≠ wY by decide), run_skip]
    simp +decide only [config_ite_reg, setReg_reg, setReg_mem, ↓reduceIte, ha, hb, triE, edge]
    split_ifs <;> omega

/-- The addresses of `edgeAt` on triangle `i < t`: the position and two vertices. -/
theorem edgeAt_addrOK {c : Config} {i t bV bP : ℕ} (hk : c.reg wK = i) (hi : i < t)
    (hv : c.reg wV = bV) (hp : c.reg wP = bP) (hS1 : bP + t ≤ S) (hS2 : bV + 3 * t ≤ S) :
    AddrOK S edgeAt c := by
  addr_ok [edgeAt, edgePre, hk, hv, hp]

/-! ### The state -/

/-- The memory `M` and the registers read by the loops of the check. -/
@[mk_iff] structure TG (M : ℕ → ℕ) (bV bP t Ψ : ℕ) (c : Config) : Prop where
  mem : c.mem = M
  rv : c.reg wV = bV
  rp : c.reg wP = bP
  rt : c.reg wT = t
  rs : c.reg wS = Ψ
  out : c.out = []

/-- The data in the memory `M`: the vertices of the triangles at `bV`, the positions at `bP`. -/
structure Dat (M : ℕ → ℕ) (bV bP t : ℕ) (vs ps : List ℕ) : Prop where
  v : ∀ i, i < t → ∀ o, o < 3 → M (bV + (i * 3 + o)) = vs.getD (i * 3 + o) 0
  p : ∀ i, i < t → M (bP + i) = ps.getD i 0

/-- The state of the inner loop before the pair `(i, j)`: the edge of triangle `j` in
`(wA, wB)`, the count `acc + colc f j i`. -/
def InnerI (M : ℕ → ℕ) (bV bP t Ψ : ℕ) (f : ℕ → Edge) (acc j i : ℕ) (c : Config) : Prop :=
  TG M bV bP t Ψ c ∧ c.reg wA = (f j).1 ∧ c.reg wB = (f j).2 ∧ c.reg wN = acc + colc f j i

/-- The state of the outer loop before triangle `j`. -/
def OuterI (M : ℕ → ℕ) (bV bP t Ψ : ℕ) (f : ℕ → Edge) (j : ℕ) (c : Config) : Prop :=
  TG M bV bP t Ψ c ∧ c.reg wN = allc f j

section loops

variable {M : ℕ → ℕ} {bV bP t Ψ : ℕ} {vs ps : List ℕ}

/-- `edgeAt` on triangle `i < t`. -/
theorem edgeAt_tg (hD : Dat M bV bP t vs ps) {c : Config} (hG : TG M bV bP t Ψ c) {i : ℕ}
    (hi : i < t) (hk : c.reg wK = i) :
    (run edgeAt c).reg wX = (triE vs ps i).1 ∧ (run edgeAt c).reg wY = (triE vs ps i).2 ∧
      Agree [wQ, wU, wO, wO', wX, wY, rT] c (run edgeAt c) :=
  edgeAt_run hk (by rw [hG.mem, hG.rp]; exact hD.p i hi)
    (fun o ho => by rw [hG.mem, hG.rv]; exact hD.v i hi o ho)

theorem innerBody_spec (hD : Dat M bV bP t vs ps) (hS1 : bP + t ≤ S) (hS2 : bV + 3 * t ≤ S)
    {acc j : ℕ} (hj : j < t) (i : ℕ) (hi : i < j) :
    HTB S innerBody (fun c => InnerI M bV bP t Ψ (triE vs ps) acc j i c ∧ c.reg wI = i ∧ c.reg wJ = j)
      (fun c => InnerI M bV bP t Ψ (triE vs ps) acc j (i + 1) c ∧ c.reg wI = i ∧ c.reg wJ = j)
      41 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hA, hB, hN⟩, hI, hJ⟩ => ⟨?_, ?_⟩
  · have hk1 : (run (mov wK wI) c).reg wK = i := by
      rw [run_mov (show wI ≠ rT by decide)]; simp [hI]
    exact AddrOK.seq (AddrOK.of_memFree rfl) (AddrOK.seq (edgeAt_addrOK (bV := bV) (bP := bP)
      (t := t) hk1 (by omega) (by rw [run_mov (show wI ≠ rT by decide)]; simp [hG.rv])
      (by rw [run_mov (show wI ≠ rT by decide)]; simp [hG.rp]) hS1 hS2) (AddrOK.of_memFree rfl))
  have hag : Agree [wK, wQ, wU, wO, wO', wX, wY, rT, wN] c (run innerBody c) :=
    agree_run (by decide) rfl rfl (by decide) c
  have hG' : TG M bV bP t Ψ (run innerBody c) :=
    (show Indep [wK, wQ, wU, wO, wO', wX, wY, rT, wN] (TG M bV bP t Ψ) by indep [tG_iff]) c _ hag hG
  refine ⟨⟨hG', by rw [hag.reg wA (by decide), hA], by rw [hag.reg wB (by decide), hB], ?_⟩,
    by rw [hag.reg wI (by decide), hI], by rw [hag.reg wJ (by decide), hJ]⟩
  have hag1 : Agree [rT, wK] c (run (mov wK wI) c) := agree_run (by decide) rfl rfl (by decide) c
  have hk1 : (run (mov wK wI) c).reg wK = i := by
    rw [run_mov (show wI ≠ rT by decide)]; simp [hI]
  have hG1 : TG M bV bP t Ψ (run (mov wK wI) c) :=
    (show Indep [rT, wK] (TG M bV bP t Ψ) by indep [tG_iff]) c _ hag1 hG
  obtain ⟨hX, hY, hag2⟩ := edgeAt_tg hD hG1 (by omega) hk1
  have hA2 : (run edgeAt (run (mov wK wI) c)).reg wA = (triE vs ps j).1 := by
    rw [hag2.reg wA (by decide), hag1.reg wA (by decide), hA]
  have hB2 : (run edgeAt (run (mov wK wI) c)).reg wB = (triE vs ps j).2 := by
    rw [hag2.reg wB (by decide), hag1.reg wB (by decide), hB]
  have hN2 : (run edgeAt (run (mov wK wI) c)).reg wN = acc + colc (triE vs ps) j i := by
    rw [hag2.reg wN (by decide), hag1.reg wN (by decide), hN]
  have e : run innerBody c = run (ifEq wA wX (ifEq wB wY (inc wN) .skip) .skip)
      (run edgeAt (run (mov wK wI) c)) := rfl
  generalize run edgeAt (run (mov wK wI) c) = c2 at hX hY hA2 hB2 hN2 e
  rw [e, colc_succ]
  simp +decide only [run_ifEq (show wA ≠ rT by decide) (show wX ≠ rT by decide),
    run_ifEq (show wB ≠ rT by decide) (show wY ≠ rT by decide), run_inc (show wN ≠ rT by decide),
    run_skip, config_ite_reg, setReg_reg, ↓reduceIte, hX, hY, hA2, hB2, hN2, Prod.ext_iff]
  split_ifs <;> omega

theorem outerPre_spec (hD : Dat M bV bP t vs ps) (hS1 : bP + t ≤ S) (hS2 : bV + 3 * t ≤ S)
    {j : ℕ} (hj : j < t) :
    HTB S outerPre (fun c => OuterI M bV bP t Ψ (triE vs ps) j c ∧ c.reg wJ = j ∧ c.reg wT = t)
      (fun c => InnerI M bV bP t Ψ (triE vs ps) (allc (triE vs ps) j) j 0 c ∧ c.reg wJ = j) 31 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hN⟩, hJ, _⟩ => ⟨?_, ?_⟩
  · have hk1 : (run (mov wK wJ) c).reg wK = j := by
      rw [run_mov (show wJ ≠ rT by decide)]; simp [hJ]
    exact AddrOK.seq (AddrOK.of_memFree rfl) (AddrOK.seq (edgeAt_addrOK (bV := bV) (bP := bP)
      (t := t) hk1 hj (by rw [run_mov (show wJ ≠ rT by decide)]; simp [hG.rv])
      (by rw [run_mov (show wJ ≠ rT by decide)]; simp [hG.rp]) hS1 hS2) (AddrOK.of_memFree rfl))
  have hag : Agree [wK, wQ, wU, wO, wO', wX, wY, rT, wA, wB] c (run outerPre c) :=
    agree_run (by decide) rfl rfl (by decide) c
  have hG' : TG M bV bP t Ψ (run outerPre c) :=
    (show Indep [wK, wQ, wU, wO, wO', wX, wY, rT, wA, wB] (TG M bV bP t Ψ) by indep [tG_iff])
      c _ hag hG
  have hag1 : Agree [rT, wK] c (run (mov wK wJ) c) := agree_run (by decide) rfl rfl (by decide) c
  have hk1 : (run (mov wK wJ) c).reg wK = j := by
    rw [run_mov (show wJ ≠ rT by decide)]; simp [hJ]
  have hG1 : TG M bV bP t Ψ (run (mov wK wJ) c) :=
    (show Indep [rT, wK] (TG M bV bP t Ψ) by indep [tG_iff]) c _ hag1 hG
  obtain ⟨hX, hY, -⟩ := edgeAt_tg hD hG1 hj hk1
  have e : run outerPre c = run (.seq (mov wA wX) (mov wB wY)) (run edgeAt (run (mov wK wJ) c)) :=
    rfl
  refine ⟨⟨hG', ?_, ?_, by rw [hag.reg wN (by decide), hN, colc_zero, Nat.add_zero]⟩,
    by rw [hag.reg wJ (by decide), hJ]⟩
  · rw [e]
    simp +decide only [run_seq', run_mov (show wX ≠ rT by decide),
      run_mov (show wY ≠ rT by decide), setReg_reg, ↓reduceIte, hX]
  · rw [e]
    simp +decide only [run_seq', run_mov (show wX ≠ rT by decide),
      run_mov (show wY ≠ rT by decide), setReg_reg, ↓reduceIte, hY]

theorem outerBody_spec (hD : Dat M bV bP t vs ps) (hS1 : bP + t ≤ S) (hS2 : bV + 3 * t ≤ S)
    (j : ℕ) (hj : j < t) :
    HTB S outerBody (fun c => OuterI M bV bP t Ψ (triE vs ps) j c ∧ c.reg wJ = j ∧ c.reg wT = t)
      (fun c => OuterI M bV bP t Ψ (triE vs ps) (j + 1) c ∧ c.reg wJ = j ∧ c.reg wT = t)
      (45 * t + 34) := by
  have hl := HTB.forUpC (S := S) (i := wI) (n := wJ) (N := j) (body := innerBody)
    (InnerI M bV bP t Ψ (triE vs ps) (allc (triE vs ps) j) j) 41 (by decide) (by decide)
    (by decide) (fun i => by indep [InnerI, tG_iff])
    (fun i hi => innerBody_spec hD hS1 hS2 hj i hi)
  refine ((outerPre_spec hD hS1 hS2 hj).seq hl).mono (fun _ h => h)
    (fun c ⟨⟨hG, _, _, hN⟩, _, hJ⟩ => ⟨⟨hG, by rw [hN, allc_succ]⟩, hJ, hG.rt⟩) ?_
  nlinarith

end loops

/-! ### Reading the input and writing the answer -/

theorem checkInit_spec {inp : List ℕ} {m t Ψ : ℕ} (f : ℕ → Edge) (hm : (initial inp).mem 0 = m)
    (ht : (initial inp).mem (2 * m + 2) = t) (hs : (initial inp).mem (2 * m + 3 + 3 * t) = Ψ)
    (hS : 2 * m + 3 + 3 * t + 1 ≤ S) :
    HTB S checkInit (· = initial inp)
      (fun c => OuterI (initial inp).mem (2 * m + 3) (2 * m + 3 + 3 * t + 1) t Ψ f 0 c ∧
        c.reg wT = t) 14 := by
  refine HTB.of_HT_addrOK (by decide) (fun c hc => by
    subst hc
    have ht' : (initial inp).mem (m + m + 3 - 1) = t := by
      rw [show m + m + 3 - 1 = 2 * m + 2 by omega]; exact ht
    addr_ok [checkInit, initial_reg, hm, ht']) ?_
  refine HT.run_le (by decide) (by decide) fun c hc => ?_
  subst hc
  have ht' : (initial inp).mem (m + m + 3 - 1) = t := by
    rw [show m + m + 3 - 1 = 2 * m + 2 by omega]; exact ht
  have hs' : (initial inp).mem (t + t + t + (m + m + 3)) = Ψ := by
    rw [show t + t + t + (m + m + 3) = 2 * m + 3 + 3 * t by omega]; exact hs
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  all_goals simp +decide only [checkInit, run_seq', run_load, run_add,
    run_addc (show wV ≠ rT by decide), run_addc (show wD ≠ rT by decide),
    run_subc (show wV ≠ rT by decide), run_const, setReg_reg, setReg_mem, setReg_out, ↓reduceIte,
    initial_reg, initial_out, hm, ht', hs', allc_zero]
  · omega
  · omega

theorem answer_spec {M : ℕ → ℕ} {bV bP t Ψ : ℕ} {ps : List ℕ} {f : ℕ → Edge}
    (hp : ∀ i, i < t → M (bP + i) = ps.getD i 0) (hpl : ps.length = t) (hS : bP + t ≤ S) :
    HTB S answer (fun c => OuterI M bV bP t Ψ f t c)
      (fun c => c.out = if allc f t ≤ Ψ then 1 :: ps else [0]) (7 * t + 7) := by
  have h0 : HTB S (.sub wU wN wS) (fun c => OuterI M bV bP t Ψ f t c)
      (fun c => OuterI M bV bP t Ψ f t c ∧ c.reg wU = allc f t - Ψ) 1 := HTB.of_HT rfl <|
    HT.run_le (by decide) (by decide) fun c ⟨hG, hN⟩ =>
      ⟨(show Indep [wU] (OuterI M bV bP t Ψ f t) by indep [OuterI, tG_iff]).setReg (by decide) _
        ⟨hG, hN⟩, by simp +decide [hN, hG.rs]⟩
  have hl := HTB.forUpC (S := S) (i := wI) (n := wT) (N := t) (body := outBody)
    (fun i c => c.mem = M ∧ c.reg wP = bP ∧ c.out = 1 :: ps.take i) 3 (by decide) (by decide)
    (by decide) (fun i => by indep) (fun i hi => HTB.run_le (by decide) (by decide)
      fun c ⟨⟨hm, hP, ho⟩, hI, hT⟩ => by
        refine ⟨by addr_ok [outBody, hP, hI], ⟨?_, ?_, ?_⟩, ?_, ?_⟩
        all_goals simp +decide only [outBody, run_seq', run_ld, run_write, setReg_reg, setReg_mem,
          setReg_out, emit_reg, emit_mem, emit_out, ↓reduceIte, hm, hP, ho, hI, hT]
        rw [hp i hi, List.take_add_one, List.getElem?_eq_getElem (by omega),
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        simp)
  have hyes : HTB S ansYes (fun c => (OuterI M bV bP t Ψ f t c ∧ c.reg wU = allc f t - Ψ) ∧
      c.reg wU = 0) (fun c => c.out = if allc f t ≤ Ψ then 1 :: ps else [0]) (7 * t + 5) := by
    intro c₀ hc₀
    have hle : allc f t ≤ Ψ := by obtain ⟨⟨_, hU⟩, hU0⟩ := hc₀; omega
    have h1 : HTB S (.seq (.const wW 1) (.write wW))
        (fun c => (OuterI M bV bP t Ψ f t c ∧ c.reg wU = allc f t - Ψ) ∧ c.reg wU = 0)
        (fun c => (c.mem = M ∧ c.reg wP = bP ∧ c.out = 1 :: ps.take 0) ∧ c.reg wT = t) 2 :=
      HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hG, _⟩, _⟩, _⟩ => by
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        all_goals simp +decide only [run_seq', run_const, run_write, setReg_reg, setReg_mem,
          setReg_out, emit_reg, emit_mem, emit_out, ↓reduceIte, hG.mem, hG.rp, hG.out, hG.rt]
        simp
    refine ((h1.seq hl).mono (fun _ h => h) ?_ (by omega)) c₀ hc₀
    intro c ⟨⟨_, _, ho⟩, _, _⟩
    rw [ho, ite_eq_left_iff.mpr (fun h => absurd hle h), ← hpl, List.take_length]
  have hno : HTB S ansNo (fun c => (OuterI M bV bP t Ψ f t c ∧ c.reg wU = allc f t - Ψ) ∧
      c.reg wU ≠ 0) (fun c => c.out = if allc f t ≤ Ψ then 1 :: ps else [0]) (7 * t + 5) :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by unfold ansNo; simp only [size]; omega) fun c ⟨⟨⟨hG, _⟩, hU⟩, hU0⟩ => by
      have : ¬ allc f t ≤ Ψ := by omega
      simp +decide only [ansNo, run_seq', run_const, run_write, setReg_reg, setReg_out, emit_out,
        ↓reduceIte, hG.out, this, List.nil_append]
  exact (h0.seq (HTB.ifz hyes hno)).weaken (by omega)

/-- **The cost check** on an input whose memory holds `m` at `0`, `t` at `2m + 2`, the vertices
`vs` of `t` triangles from `2m + 3` on, `Ψ` after them and then the `t` positions `ps`: within
`100 (t² + 1)` steps it writes `1 :: ps` if the cost `allc (triE vs ps) t` of the chosen edges is
at most `Ψ`, and `[0]` otherwise. -/
theorem triCheck_spec {inp : List ℕ} {m t Ψ : ℕ} {vs ps : List ℕ}
    (hm : (initial inp).mem 0 = m) (ht : (initial inp).mem (2 * m + 2) = t)
    (hvs : Arr (initial inp).mem (2 * m + 3) vs) (hvl : vs.length = 3 * t)
    (hΨ : (initial inp).mem (2 * m + 3 + 3 * t) = Ψ)
    (hps : Arr (initial inp).mem (2 * m + 3 + 3 * t + 1) ps) (hpl : ps.length = t)
    (hS : 2 * m + 3 + 3 * t + 1 + t ≤ S) :
    HTB S triCheck (· = initial inp)
      (fun c => c.out = if allc (triE vs ps) t ≤ Ψ then 1 :: ps else [0]) (100 * (t * t + 1)) := by
  have hD : Dat (initial inp).mem (2 * m + 3) (2 * m + 3 + 3 * t + 1) t vs ps :=
    ⟨fun i hi o ho => hvs.getD (by omega), fun i hi => hps.getD (by omega)⟩
  have hl := HTB.forUpC (S := S) (i := wJ) (n := wT) (N := t) (body := outerBody)
    (OuterI (initial inp).mem (2 * m + 3) (2 * m + 3 + 3 * t + 1) t Ψ (triE vs ps)) (45 * t + 34)
    (by decide) (by decide) (by decide) (fun j => by indep [OuterI, tG_iff])
    (fun j hj => outerBody_spec hD (by omega) (by omega) j hj)
  refine ((checkInit_spec (triE vs ps) hm ht hΨ (by omega)).seq (hl.seq
    ((answer_spec hD.p hpl (by omega)).pre fun c h => h.1))).weaken ?_
  nlinarith

end STACS2027.Runtimes.BoundedCost.Tri
