module

public import Runtimes.BoundedCost.TriCheck
public import Runtimes.BoundedCost.Triangle
public import Runtimes.BoundedCost.Top
import Mathlib.Tactic

/-!
# Theorem 4 for `k = 3` as a decision on the RAM, and one machine for all `k ≥ 3`

The machine of Theorem 4 for `k = 3` runs on the same input as for `k ≥ 4`,
`boundedCostInput g 3 Ψ = flowInput g (cycles g 3) 3 ++ [Ψ]` (`boundedCostInput_flow`), and writes `[0]` if
`CPAP(G, 3)` has no assignment of cost at most `Ψ`, and otherwise `1` followed by the positions of
such an assignment (`BoundedCostAnswer g 3 Ψ`). It is `triDecide Q = pipe3 lenP5 dropPsi Q triCheck`
(`Runtimes/Flow/Pipe.lean`, with the space bounds of `pipe3_spec`), for a program `Q` writing the
positions of an optimal assignment on `flowInput g (cycles g 3) 3` (the triangle pipeline with
the sorting front end, `triangle_sort_single`, with the cited min-cost flow program as a
subroutine):

1. `lenP5` (`Runtimes/BoundedCost/Top.lean`): the length `2m + 3 + 3t + 1` of the input;
2. `dropPsi`: writes the input without its last cell `Ψ`, i.e. `flowInput g (cycles g 3) 3`;
3. `Q` on that output: the positions `pos` of an optimal assignment;
4. `triCheck` (`Runtimes/BoundedCost/TriCheck.lean`) on the input followed by `pos`: it counts the pairs
   of triangles whose chosen edges are equal — the cost of the assignment
   (`cost_selected_tri`) — and writes `[0]` if the count exceeds `Ψ`, else `1 :: pos`.

Since `pos` is optimal, the cost exceeds `Ψ` exactly when no assignment of cost `≤ Ψ` exists
(`optCost_budget`), so the answer is correct (`triDecide_spec`). The check takes `O(t² + 1)` steps
(all pairs of triangles), within the manuscript's `kt²` term; the stages other than `Q` read and
write only `O(t + m)` cells.

* `boundedCost_triangle`: within `C (t² + m + 1) + 16 T(21t + 5)` steps and the addresses below
  `C (t + m + 1) + 16 T(21t + 5)`, `T` the bound of the min-cost flow program;
* `boundedCost_triangle_almostLinear`: with an almost-linear `T`, within `C (t² + m + 1)` steps and
  addresses;
* `boundedCost_ram_all`, `boundedCost_ram_all_almostLinear`: **one machine for all `k ≥ 3`**
  (`boundedCostAll`): it reads `k`, restores the initial configuration and runs the triangle machine if
  `k = 3` and the machine of `boundedCost_ram_fpt` (`boundedCostTop F'`, with the cited Almost 2-SAT program
  `F'` under `FPTBound`) otherwise, within `C (15^Ψ Ψ ((Ψ+1)k²t + kt²)³ + k²t + kt² + m + 1)`
  steps plus `16 T(21t + 5)` (without it for an almost-linear `T`), and the addresses below the
  same bound.

No program indexes memory by a vertex label: for `k = 3` the flow construction relabels the
vertices by sorting (`Runtimes/Flow/SortTri.lean`), as the machine for `k ≥ 4` does
(`Runtimes/BoundedCost/Top.lean`), so the memory bounds have no `labelBound g` term.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Flow

/-! ### The input -/

theorem boundedCostInput_three (g : Graph) (Ψ : ℕ) :
    boundedCostInput g 3 Ψ = flowInput g (cycles g 3) 3 ++ [Ψ] := rfl

theorem isCycle_three (g : Graph) : ∀ c ∈ cycles g 3, IsCycle g 3 c :=
  isCycle_of_perm (List.Perm.refl _)

theorem length_flowInput_three (g : Graph) :
    (flowInput g (cycles g 3) 3).length = 2 * g.length + 3 + 3 * (cycles g 3).length := by
  rw [length_flowInput (isCycle_three g), bD, bV]

/-! ### Phase 2: the input without `Ψ` -/

/-- The index of the copy. -/
abbrev dI : ℕ := 700
/-- The value copied. -/
abbrev dW : ℕ := 701

/-- Writing cell `dI`. -/
def dropBody : Stmt := .seq (.load dW dI) (.write dW)

/-- **The input without its last cell**: writes the first `|flowInput g cs 3|` cells. -/
def dropPsi : Stmt := .seq lenFlow (forUp dI xL dropBody)

/-- `dropPsi` writes `flowInput g (cycles g 3) 3`, reading only the input cells below
`|flowInput g (cycles g 3) 3|`. -/
theorem dropPsi_spec (g : Graph) (Ψ : ℕ) {S : ℕ} (hS : (flowInput g (cycles g 3) 3).length ≤ S) :
    HTB S dropPsi (· = initial (boundedCostInput g 3 Ψ)) (fun c => c.out = flowInput g (cycles g 3) 3)
      (5 * (cycles g 3).length + 15 + ((flowInput g (cycles g 3) 3).length * 6 + 3)) := by
  set x := flowInput g (cycles g 3) 3 with hx
  have hbV : bV g ≤ S := by rw [length_flowInput (isCycle_three g)] at hS; unfold bD at hS; omega
  have h1 := lenFlow_value_app (S := S) (isCycle_three g) [Ψ] hbV
  have hl := HTB.forUpC (S := S) (i := dI) (n := xL) (N := x.length) (body := dropBody)
    (fun j c => c.mem = (initial (x ++ [Ψ])).mem ∧ c.out = x.take j) 2 (by decide) (by decide)
    (by decide) (fun j => by indep) (fun j hj => HTB.run_le (by decide) (by decide)
      fun c ⟨⟨hm, ho⟩, hI, hL⟩ => by
        refine ⟨by addr_ok [dropBody, hI], ⟨?_, ?_⟩, ?_, ?_⟩
        all_goals simp +decide only [dropBody, run_seq', run_load, run_write, setReg_reg,
          setReg_mem, setReg_out, emit_reg, emit_mem, emit_out, ↓reduceIte, hm, ho, hI, hL]
        rw [initial_mem, getD_append_left' hj, List.take_add_one,
          List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
        simp)
  refine ((h1.post fun c ⟨hL, hm, ho⟩ => ⟨⟨hm, by simp [ho]⟩, hL⟩).seq hl).mono
    (fun c hc => by rw [hc, boundedCostInput_three]) (fun c ⟨⟨_, ho⟩, _, _⟩ => ?_) le_rfl
  rw [ho, List.take_length]

/-! ### Phase 4: the cost check -/

/-- `triCheck` on the input followed by the `t` positions `pos`, reading only these cells. -/
theorem triCheck_boundedCost (g : Graph) (Ψ : ℕ) {pos : List ℕ} (hpl : pos.length = (cycles g 3).length)
    {S : ℕ} (hS : (boundedCostInput g 3 Ψ ++ pos).length ≤ S) :
    HTB S Tri.triCheck (· = initial (boundedCostInput g 3 Ψ ++ pos))
      (fun c => c.out = if Tri.allc (Tri.triE (Flow.verts (cycles g 3)) pos) (cycles g 3).length ≤ Ψ
        then 1 :: pos else [0])
      (100 * ((cycles g 3).length * (cycles g 3).length + 1)) := by
  have hcs := isCycle_three g
  have he : boundedCostInput g 3 Ψ ++ pos = flowInput g (cycles g 3) 3 ++ (Ψ :: pos) := by
    simp [boundedCostInput_three]
  have hlen : (boundedCostInput g 3 Ψ ++ pos).length =
      2 * g.length + 3 + 3 * (cycles g 3).length + 1 + (cycles g 3).length := by
    rw [List.length_append, boundedCostInput_three, List.length_append, length_flowInput_three, hpl]; rfl
  obtain ⟨h0, -, ht, hv, hr⟩ := input_facts hcs (Ψ :: pos)
  rw [← he] at h0 ht hv hr
  rw [arr_cons] at hr
  simp only [bD, bV] at hv hr
  exact Tri.triCheck_spec h0 ht hv (length_verts hcs) hr.1 hr.2 hpl (by omega)

/-! ### The cost of a triangle assignment -/

/-- The paths of a triangle assignment are the chosen edges `triE`. -/
theorem zipWith_selected_tri {g : Graph} {cs : List Cycle} (hcs : ∀ c ∈ cs, IsCycle g 3 c)
    {pos : List ℕ} (hl : pos.length = cs.length) (hlt : ∀ p ∈ pos, p < 3) :
    List.zipWith selected cs pos =
      (List.range cs.length).map fun i => [Tri.triE (Flow.verts cs) pos i] := by
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 _
    have hi : i < cs.length := by simp [hl] at h1; exact h1
    have hip : i < pos.length := by omega
    rw [List.getElem_zipWith, List.getElem_map, List.getElem_range]
    have hc3 : cs[i].length = 3 := (hcs _ (List.getElem_mem hi)).2.1
    have hp3 : pos[i] < 3 := hlt _ (List.getElem_mem hip)
    have hpi : pos.getD i 0 = pos[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hip]; rfl
    have hci : cyc cs i = cs[i] := by
      rw [cyc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    rw [Tri.selected_tri hc3 hp3, Tri.triE, hpi, verts_getD hcs hi (Tri.off1_lt _),
      verts_getD hcs hi (Tri.off2_lt _), hci]

/-- **The cost of a triangle assignment** is the number of pairs of triangles with equal chosen
edges, the count of `triCheck`. -/
theorem cost_selected_tri {g : Graph} {cs : List Cycle} (hcs : ∀ c ∈ cs, IsCycle g 3 c)
    {pos : List ℕ} (hl : pos.length = cs.length) (hlt : ∀ p ∈ pos, p < 3) :
    cost (List.zipWith selected cs pos) = Tri.allc (Tri.triE (Flow.verts cs) pos) cs.length := by
  rw [zipWith_selected_tri hcs hl hlt, Tri.cost_tri]

/-! ### The machine for `k = 3` -/

/-- **Theorem 4's machine for `k = 3`**, from a program `Q` writing the positions of an optimal
assignment. -/
def triDecide (Q : Stmt) : Stmt := pipe3 lenP5 dropPsi Q Tri.triCheck

/-- **The decision for `k = 3`**: if `Q` writes on `flowInput g (cycles g 3) 3`, in `t₂` steps
and the addresses below `S₂`, the positions `pos` of a valid assignment whose cost answers every
budget, then `triDecide Q` answers Theorem 4's question on `boundedCostInput g 3 Ψ` within
`4 t₂ + 1000 (t² + m + 1)` steps and the addresses below `4 S₂ + 1000 (t + m + 1)`. -/
theorem triDecide_spec {Q : Stmt} {g : Graph} {pos : List ℕ} {t₂ S₂ : ℕ}
    (hQ : ComputesIn Q (flowInput g (cycles g 3) 3) pos t₂ S₂)
    (hl : pos.length = (cycles g 3).length) (hlt : ∀ p ∈ pos, p < 3)
    (hv : ValidChoices ((cycles g 3).map selectedOptions) (List.zipWith selected (cycles g 3) pos))
    (hopt : ∀ Ψ : ℕ, HasAssignment g 3 Ψ ↔ cost (List.zipWith selected (cycles g 3) pos) ≤ Ψ)
    (Ψ : ℕ) :
    ∃ (out : List ℕ) (steps : ℕ),
      ComputesIn (triDecide Q) (boundedCostInput g 3 Ψ) out steps
        (4 * S₂ + 1000 * ((cycles g 3).length + g.length + 1)) ∧
      steps ≤ 4 * t₂ + 1000 * ((cycles g 3).length * (cycles g 3).length + g.length + 1) ∧
      BoundedCostAnswer g 3 Ψ out := by
  have hx : (boundedCostInput g 3 Ψ).length = 2 * g.length + 3 + 3 * (cycles g 3).length + 1 := by
    rw [boundedCostInput_three, List.length_append, length_flowInput_three, List.length_singleton]
  have hy := length_flowInput_three g
  have hz : (boundedCostInput g 3 Ψ ++ pos).length =
      2 * g.length + 3 + 3 * (cycles g 3).length + 1 + (cycles g 3).length := by
    rw [List.length_append, hx, hl]
  obtain ⟨t₁, ht₁, h₁⟩ := HTB.computesIn (dropPsi_spec g Ψ le_rfl)
  obtain ⟨t₃, ht₃, h₃⟩ := HTB.computesIn (triCheck_boundedCost g Ψ hl le_rfl)
  obtain ⟨steps, hc, hs⟩ := pipe3_spec (lenP5_spec (S := bV g) g 3 Ψ le_rfl) h₁ hQ h₃
  refine ⟨_, steps, hc.mono ?_, ?_, ?_⟩
  · rw [hx, hy, hl, hz]; unfold bV; omega
  · rw [hx] at hs
    rw [hy] at ht₁
    have htt := Nat.le_mul_self (cycles g 3).length
    omega
  · rw [← cost_selected_tri (isCycle_three g) hl hlt]
    by_cases h : cost (List.zipWith selected (cycles g 3) pos) ≤ Ψ
    · simp only [h, ↓reduceIte]; exact Or.inr ⟨pos, rfl, hl, hlt, hv, h⟩
    · simp only [h, ↓reduceIte]; exact Or.inl ⟨fun hA => h ((hopt Ψ).mp hA), rfl⟩

/-- **Theorem 4 for `k = 3`**: the answer within `C (t² + m + 1) + 16 T(21t + 5)` steps and
`C (t + m + 1) + 16 T(21t + 5)` addresses (no memory indexed by a vertex label). -/
theorem boundedCost_triangle {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T) :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (Ψ : ℕ),
      ∃ (out : List ℕ) (steps : ℕ),
        RAM.ComputesIn prog (boundedCostInput g 3 Ψ) out steps
          (C * ((cycles g 3).length + g.length + 1) + 16 * T (21 * (cycles g 3).length + 5)) ∧
        steps ≤ C * ((cycles g 3).length * (cycles g 3).length + g.length + 1) +
          16 * T (21 * (cycles g 3).length + 5) ∧
        BoundedCostAnswer g 3 Ψ out := by
  obtain ⟨Q, C, h⟩ := boundedCost_triangle_opt hF
  refine ⟨triDecide Q, 4 * C + 1000, fun g Ψ => ?_⟩
  obtain ⟨pos, t₂, hc, hs, hl, hlt, hv, hopt⟩ := h g
  obtain ⟨out, steps, hc', hs', ha⟩ := triDecide_spec hc hl hlt hv hopt Ψ
  set t := (cycles g 3).length
  have e1 : (4 * C + 1000) * (t * t + g.length + 1) =
      4 * (C * (t * t + g.length + 1)) + 1000 * (t * t + g.length + 1) := by ring
  have e2 : (4 * C + 1000) * (t + g.length + 1) =
      4 * (C * (t + g.length + 1)) + 1000 * (t + g.length + 1) := by ring
  refine ⟨out, steps, hc'.mono ?_, ?_, ha⟩
  · rw [e2]; omega
  · rw [e1]; omega

/-- **Theorem 4 for `k = 3`** with an almost-linear `T`: within `C (t² + m + 1)` steps and
addresses. -/
theorem boundedCost_triangle_almostLinear {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T)
    (hT : AlmostLinear T) :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (Ψ : ℕ),
      ∃ (out : List ℕ) (steps : ℕ),
        RAM.ComputesIn prog (boundedCostInput g 3 Ψ) out steps
          (C * ((cycles g 3).length * (cycles g 3).length + g.length + 1)) ∧
        steps ≤ C * ((cycles g 3).length * (cycles g 3).length + g.length + 1) ∧
        BoundedCostAnswer g 3 Ψ out := by
  obtain ⟨Q, C, h⟩ := boundedCost_triangle_opt_almostLinear hF hT
  refine ⟨triDecide Q, 4 * C + 1000, fun g Ψ => ?_⟩
  obtain ⟨pos, t₂, hc, hs, hl, hlt, hv, hopt⟩ := h g
  obtain ⟨out, steps, hc', hs', ha⟩ := triDecide_spec hc hl hlt hv hopt Ψ
  set t := (cycles g 3).length
  have htt := Nat.le_mul_self t
  have e1 : (4 * C + 1000) * (t * t + g.length + 1) =
      4 * (C * (t * t + g.length + 1)) + 1000 * (t * t + g.length + 1) := by ring
  refine ⟨out, steps, hc'.mono ?_, ?_, ha⟩
  · rw [e1]; omega
  · calc steps ≤ 4 * t₂ + 1000 * (t * t + g.length + 1) := hs'
      _ ≤ 4 * (C * (t * t + g.length + 1)) + 1000 * (t * t + g.length + 1) := by omega
      _ = (4 * C + 1000) * (t * t + g.length + 1) := e1.symm

/-! ### One machine for all `k ≥ 3` -/

/-- Read `k` (the cell `2m + 1` of the input) and put `k - 3` into register `6`, leaving register
`5` zero. -/
def readK : Stmt :=
  .seq (.const 5 0) (.seq (.load 6 5) (.seq (.add 6 6 6) (.seq (.const 5 1)
    (.seq (.add 6 6 5) (.seq (.load 6 6) (.seq (.const 5 3) (.seq (.sub 6 6 5) (.const 5 0))))))))

/-- **The machine of Theorem 4 for all `k ≥ 3`**: if `k ≤ 3`, clear register `6` (restoring the
initial configuration) and run `P3` (the machine for `k = 3`); otherwise clear it and run `P4`
(the machine for `k ≥ 4`). -/
def boundedCostAll (P3 P4 : Stmt) : Stmt :=
  .seq readK (.ifz 6 (.seq (.const 6 0) P3) (.seq (.const 6 0) P4))

theorem boundedCostInput_getD_k (g : Graph) (k Ψ : ℕ) :
    (boundedCostInput g k Ψ).getD (g.length + g.length + 1) 0 = k := by
  have h : (graphInput g).length = 2 * g.length + 1 := length_graphInput g
  simp only [boundedCostInput, ZeroCost.zeroCostInput, List.append_assoc]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  rw [show g.length + g.length + 1 - (graphInput g).length = 0 by omega]
  simp

theorem boundedCostInput_getD_zero (g : Graph) (k Ψ : ℕ) : (boundedCostInput g k Ψ).getD 0 0 = g.length := by
  simp [boundedCostInput, ZeroCost.zeroCostInput, graphInput]

/-- The configuration after `readK`. -/
def cfgK (g : Graph) (k Ψ : ℕ) : Config :=
  ⟨fun i => if i = 6 then k - 3 else 0, fun i => (boundedCostInput g k Ψ).getD i 0, []⟩

theorem exec_readK (g : Graph) (k Ψ : ℕ) :
    Exec readK (initial (boundedCostInput g k Ψ)) 9 (cfgK g k Ψ) := by
  have e := Exec.seq (Exec.const 5 0 (initial (boundedCostInput g k Ψ))) (Exec.seq (Exec.load 6 5 _)
    (Exec.seq (Exec.add 6 6 6 _) (Exec.seq (Exec.const 5 1 _) (Exec.seq (Exec.add 6 6 5 _)
      (Exec.seq (Exec.load 6 6 _) (Exec.seq (Exec.const 5 3 _) (Exec.seq (Exec.sub 6 6 5 _)
        (Exec.const 5 0 _))))))))
  convert e using 1
  · rfl
  have h0 := boundedCostInput_getD_zero g k Ψ
  have hk := boundedCostInput_getD_k g k Ψ
  unfold cfgK initial Config.setReg
  congr 1
  funext i
  by_cases h6 : i = 6
  · subst h6
    simp only [↓reduceIte, show (6 : ℕ) ≠ 5 by decide, h0, hk]
  · by_cases h5 : i = 5
    · subst h5; simp
    · simp [h5, h6]

/-- `readK` reads the cells `0` and `2m + 1` only. -/
theorem execB_readK (g : Graph) (k Ψ : ℕ) {S : ℕ} (hS : 2 * g.length + 2 ≤ S) :
    ExecB S readK (initial (boundedCostInput g k Ψ)) 9 (cfgK g k Ψ) := by
  have h0 : (initial (boundedCostInput g k Ψ)).mem 0 = g.length := by
    rw [initial_mem]; exact boundedCostInput_getD_zero g k Ψ
  have hB := execB_run (S := S) readK (by decide) (initial (boundedCostInput g k Ψ))
    (by addr_ok [readK, initial_reg, h0])
  obtain ⟨ht, hc⟩ := Exec.det hB.exec (exec_readK g k Ψ)
  rw [ht, hc] at hB
  exact hB

theorem cfgK_init (g : Graph) (k Ψ : ℕ) : (cfgK g k Ψ).setReg 6 0 = initial (boundedCostInput g k Ψ) := by
  simp only [cfgK, initial, Config.setReg, Config.mk.injEq, and_true]
  funext i
  by_cases h6 : i = 6 <;> simp [h6]

/-- The machine `boundedCostAll` from machines for `k = 3` and `k ≥ 4`, with their bounds. -/
theorem boundedCostAll_spec {P3 P4 : Stmt} {T3 S3 : Graph → ℕ → ℕ} {T4 S4 : Graph → ℕ → ℕ → ℕ}
    (h3 : ∀ (g : Graph) (Ψ : ℕ), ∃ (out : List ℕ) (steps : ℕ),
      RAM.ComputesIn P3 (boundedCostInput g 3 Ψ) out steps (S3 g Ψ) ∧ steps ≤ T3 g Ψ ∧
        BoundedCostAnswer g 3 Ψ out)
    (h4 : ∀ (g : Graph) (k Ψ : ℕ), 4 ≤ k → ∃ (out : List ℕ) (steps : ℕ),
      RAM.ComputesIn P4 (boundedCostInput g k Ψ) out steps (S4 g k Ψ) ∧ steps ≤ T4 g k Ψ ∧
        BoundedCostAnswer g k Ψ out)
    (g : Graph) (k Ψ : ℕ) (hk : 3 ≤ k) :
    ∃ (out : List ℕ) (steps : ℕ),
      RAM.ComputesIn (boundedCostAll P3 P4) (boundedCostInput g k Ψ) out steps
        (2 * g.length + 2 + (if k = 3 then S3 g Ψ else S4 g k Ψ)) ∧
      steps ≤ 11 + (if k = 3 then T3 g Ψ else T4 g k Ψ) ∧ BoundedCostAnswer g k Ψ out := by
  have hinit := cfgK_init g k Ψ
  rcases Nat.eq_or_lt_of_le hk with rfl | hk4
  · obtain ⟨out, s, ⟨c, he, ho⟩, hs, ha⟩ := h3 g Ψ
    have hr := execB_readK (S := 2 * g.length + 2 + S3 g Ψ) g 3 Ψ (by omega)
    have hz : (cfgK g 3 Ψ).reg 6 = 0 := by simp [cfgK]
    have e := ExecB.seq hr (ExecB.ifzTrue (s := .seq (.const 6 0) P3) (u := .seq (.const 6 0) P4)
      hz (ExecB.seq (ExecB.const 6 0 (cfgK g 3 Ψ)) (hinit ▸ he.mono (by omega))))
    refine ⟨out, _, ⟨c, e, ho⟩, ?_, ha⟩
    simp only [↓reduceIte]; omega
  · obtain ⟨out, s, ⟨c, he, ho⟩, hs, ha⟩ := h4 g k Ψ hk4
    have hr := execB_readK (S := 2 * g.length + 2 + S4 g k Ψ) g k Ψ (by omega)
    have hnz : (cfgK g k Ψ).reg 6 ≠ 0 := by simp [cfgK]; omega
    have e := ExecB.seq hr (ExecB.ifzFalse (s := .seq (.const 6 0) P3) (u := .seq (.const 6 0) P4)
      hnz (ExecB.seq (ExecB.const 6 0 (cfgK g k Ψ)) (hinit ▸ he.mono (by omega))))
    have hk3 : k ≠ 3 := by omega
    rw [ite_eq_right hk3, ite_eq_right hk3]
    exact ⟨out, _, ⟨c, e, ho⟩, by omega, ha⟩

theorem tri_le_all (g : Graph) (Ψ : ℕ) :
    (cycles g 3).length * (cycles g 3).length + g.length + 1 ≤ paper5 g 3 Ψ := by
  unfold paper5
  have e : 3 * (cycles g 3).length * (cycles g 3).length =
      3 * ((cycles g 3).length * (cycles g 3).length) := by ring
  rw [e]
  generalize 15 ^ Ψ * Ψ * ((Ψ + 1) * 3 * 3 * (cycles g 3).length +
    3 * ((cycles g 3).length * (cycles g 3).length)) ^ 3 = Z
  omega

/-- `P ≥ 1`, and the reading of `k` costs at most `2P` addresses. -/
theorem paper5_ge (g : Graph) (k Ψ : ℕ) : 1 ≤ paper5 g k Ψ ∧ 2 * g.length + 2 ≤ 2 * paper5 g k Ψ := by
  unfold paper5; omega

/-- The bounds of the machine for `k = 3` within `P`. -/
theorem tri_le_all' (g : Graph) (Ψ : ℕ) :
    (cycles g 3).length + g.length + 1 ≤ paper5 g 3 Ψ := by
  have := tri_le_all g Ψ
  have := Nat.le_mul_self (cycles g 3).length
  omega

/-- **Theorem 4 for all `k ≥ 3`**, one machine: the answer within `C P + 16 T(21t + 5)` steps and
addresses, `P = 15^Ψ Ψ ((Ψ+1)k²t + kt²)³ + k²t + kt² + m + 1` (no memory indexed by a label). -/
theorem boundedCost_ram_all {F F' : RAM.Stmt} {T : ℕ → ℕ} {T' : ℕ → ℕ → ℕ}
    (hF : MinCostFlowSolver F T) (hA : Almost2SatSolver F' T') (hT' : FPTBound T') :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (k Ψ : ℕ), 3 ≤ k →
      ∃ (out : List ℕ) (steps : ℕ),
        RAM.ComputesIn prog (boundedCostInput g k Ψ) out steps
          (C * (15 ^ Ψ * Ψ * ((Ψ + 1) * k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length) ^ 3 + k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length + g.length + 1) +
            16 * T (21 * (cycles g k).length + 5)) ∧
        steps ≤ C * (15 ^ Ψ * Ψ * ((Ψ + 1) * k * k * (cycles g k).length +
          k * (cycles g k).length * (cycles g k).length) ^ 3 + k * k * (cycles g k).length +
          k * (cycles g k).length * (cycles g k).length + g.length + 1) +
          16 * T (21 * (cycles g k).length + 5) ∧
        BoundedCostAnswer g k Ψ out := by
  obtain ⟨P3, C3, h3⟩ := boundedCost_triangle hF
  obtain ⟨P4, C4, h4⟩ := boundedCost_ram_fpt hA hT'
  refine ⟨boundedCostAll P3 P4, C3 + C4 + 11, fun g k Ψ hk => ?_⟩
  obtain ⟨out, steps, hc, hs, ha⟩ := boundedCostAll_spec h3 h4 g k Ψ hk
  have hP := tri_le_all g Ψ
  have hP' := tri_le_all' g Ψ
  obtain ⟨hp1, hm⟩ := paper5_ge g k Ψ
  have e1 : (C3 + C4 + 11) * paper5 g k Ψ =
      C3 * paper5 g k Ψ + C4 * paper5 g k Ψ + 11 * paper5 g k Ψ := by ring
  have hpE : paper5 g k Ψ = 15 ^ Ψ * Ψ * ((Ψ + 1) * k * k * (cycles g k).length +
      k * (cycles g k).length * (cycles g k).length) ^ 3 + k * k * (cycles g k).length +
      k * (cycles g k).length * (cycles g k).length + g.length + 1 := rfl
  rw [← hpE]
  refine ⟨out, steps, hc.mono ?_, hs.trans ?_, ha⟩
  · split_ifs with h
    · subst h
      have := Nat.mul_le_mul_left C3 hP'
      omega
    · unfold paper5 at *
      omega
  · split_ifs with h
    · subst h
      have := Nat.mul_le_mul_left C3 hP
      omega
    · unfold paper5 at *
      omega

/-- **Theorem 4 for all `k ≥ 3`** with an almost-linear `T`: within `C P` steps and addresses —
the manuscript's bound. -/
theorem boundedCost_ram_all_almostLinear {F F' : RAM.Stmt} {T : ℕ → ℕ} {T' : ℕ → ℕ → ℕ}
    (hF : MinCostFlowSolver F T) (hT : AlmostLinear T) (hA : Almost2SatSolver F' T')
    (hT' : FPTBound T') :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (k Ψ : ℕ), 3 ≤ k →
      ∃ (out : List ℕ) (steps : ℕ),
        RAM.ComputesIn prog (boundedCostInput g k Ψ) out steps
          (C * (15 ^ Ψ * Ψ * ((Ψ + 1) * k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length) ^ 3 + k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length + g.length + 1)) ∧
        steps ≤ C * (15 ^ Ψ * Ψ * ((Ψ + 1) * k * k * (cycles g k).length +
          k * (cycles g k).length * (cycles g k).length) ^ 3 + k * k * (cycles g k).length +
          k * (cycles g k).length * (cycles g k).length + g.length + 1) ∧
        BoundedCostAnswer g k Ψ out := by
  obtain ⟨P3, C3, h3⟩ := boundedCost_triangle_almostLinear hF hT
  obtain ⟨P4, C4, h4⟩ := boundedCost_ram_fpt hA hT'
  refine ⟨boundedCostAll P3 P4, C3 + C4 + 11, fun g k Ψ hk => ?_⟩
  obtain ⟨out, steps, hc, hs, ha⟩ := boundedCostAll_spec h3 h4 g k Ψ hk
  have hP := tri_le_all g Ψ
  obtain ⟨hp1, hm⟩ := paper5_ge g k Ψ
  have e1 : (C3 + C4 + 11) * paper5 g k Ψ =
      C3 * paper5 g k Ψ + C4 * paper5 g k Ψ + 11 * paper5 g k Ψ := by ring
  have hpE : paper5 g k Ψ = 15 ^ Ψ * Ψ * ((Ψ + 1) * k * k * (cycles g k).length +
      k * (cycles g k).length * (cycles g k).length) ^ 3 + k * k * (cycles g k).length +
      k * (cycles g k).length * (cycles g k).length + g.length + 1 := rfl
  rw [← hpE]
  refine ⟨out, steps, hc.mono ?_, hs.trans ?_, ha⟩
  · split_ifs with h
    · subst h
      have := Nat.mul_le_mul_left C3 hP
      omega
    · unfold paper5 at *
      omega
  · split_ifs with h
    · subst h
      have := Nat.mul_le_mul_left C3 hP
      omega
    · unfold paper5 at *
      omega

end STACS2027.Runtimes.BoundedCost
