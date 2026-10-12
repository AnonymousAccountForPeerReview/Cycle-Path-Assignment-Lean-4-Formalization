module

public import Runtimes.Flow.Single
public import Runtimes.Sort.Front
import Mathlib.Tactic

/-!
# The triangle pipeline without label-indexed memory

The construction machine `build3` (`Runtimes/Flow/Prog.lean`) maps the vertex labels to
identifiers with Corollary 5's label dictionary (`labelBound g` cells): right for the
linear-time claims (Theorem 2, the corollary for triangles, Corollary 3), whose memory bounds
contain `labelBound g`. Theorem 4 is a polynomial-time claim, and its programs index no memory
by a vertex label. For its case `k = 3`, on Theorem 4's enumeration `cycles g 3`, the
construction runs the sorting front end of `Runtimes/Sort/Front.lean` instead (as Theorem 4's
machine for `k ≥ 4` and the parser of Lemma 16 do):

* `build3s = ZeroCost.stepInit; Sort.front; out3`: the edge identifiers `EID`, the counts `CNT` and
  the number of distinct edges in the layout of the front end (`Sort.FrontPost`), then the
  output phases `out3` for that layout (`out3_specA`, `ob_of_front`); the identifiers of the
  front end (Corollary 5's `eidOf`, `cntF`, `edgesOnCycles`) are those of the flow construction
  for the list `cycles g k` (`eid_cycles`, `cntF_cycles`, `eList_cycles`: by definition);
* `build3s_spec`: `build3s` writes the network `netEnc3 (cycles g 3)` within `CB (t² + 1)` steps
  (the merge sort takes `O(t log t)`) and the addresses below `bD + 45t + 1`, `bD = 2m + 3 + 3t`
  the length of the input — no `labelBound g`;
* `triangle_sort_single`: the pipeline (construction, the cited min-cost flow program `F` as a
  relocated subroutine, extraction) as one program, within `C (t² + m + 1) + 4 T(21t + 5)` steps
  and the addresses below `C (t + m + 1) + 4 T(21t + 5)`, writing the positions of an optimal
  assignment of `CPAP(G, 3)`; `triangle_sort_single_almostLinear`: with an almost-linear `T`.
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027 STACS2027.RAM

/-! ### The identifiers of the front end are those of the flow construction -/

section ident

variable (g : Graph) (k : ℕ)

theorem flowInput_cycles : flowInput g (cycles g k) k = ZeroCost.zeroCostInput g k := rfl

theorem eList_cycles : eList (cycles g k) = edgesOnCycles g k := rfl

theorem eid_cycles : eid (cycles g k) = ZeroCost.eidOf g k := rfl

theorem cntF_cycles : cntF (cycles g k) = ZeroCost.cntF g k := rfl

end ident

/-- After the front end (free address `F`), the output phases find what they read: `t`, the
number of edges, the identifiers at `fEID` and the counts at `fCNT`. -/
theorem ob_of_front {g : Graph} {k F : ℕ} {c : Config} (h : Sort.FrontPost g k F c) :
    OB (cycles g k) k (Sort.fEID g k F) (Sort.fCNT g k F) c :=
  ⟨h.ga.rt, h.rne, h.reid, h.rcnt, h.meid, h.mcnt⟩

/-! ### The construction machine -/

/-- **The construction machine of the triangle network with the sorting front end**: read `m`,
`k`, `t` (Corollary 5's phase 1), the front end, the output phases. -/
def build3s : Stmt := .seq ZeroCost.stepInit (.seq Sort.front out3)

/-- The constant of the running time of `build3s`. -/
def CB : ℕ := 12 * Sort.CF + 200

/-- The space of `build3s`: the end of the memory of the front end, from the end of the input. -/
def sB3 (g : Graph) : ℕ := Sort.fEnd g 3 (ZeroCost.bD g 3)

theorem isCycle_cycles (g : Graph) (k : ℕ) : ∀ c ∈ cycles g k, IsCycle g k c :=
  isCycle_of_perm (List.Perm.refl _)

/-- `t (⌈log₂ 3t⌉ + 1) ≤ 4 t²`-type bound of the front end's sort for `k = 3`. -/
theorem frontCost3_le (t : ℕ) : 3 * t * (Nat.clog 2 (3 * t) + 1) ≤ 12 * (t * t) := by
  have h : Nat.clog 2 (3 * t) ≤ 3 * t := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have h2 : 3 * t ≤ 3 * (t * t) := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ ht)
  calc 3 * t * (Nat.clog 2 (3 * t) + 1) ≤ 3 * t * (3 * t + 1) := Nat.mul_le_mul_left _ (by omega)
    _ = 9 * (t * t) + 3 * t := by ring
    _ ≤ 12 * (t * t) := by omega

/-- **The construction of the triangle network with the sorting front end**: from the input
`flowInput g (cycles g 3) 3`, `build3s` writes `netEnc3 (cycles g 3)` within `CB (t² + 1)` steps,
accessing only the addresses below any `S ≥ sB3 g` (`sB3_le`: `≤ 2m + 48t + 4`); no memory is
indexed by a vertex label. -/
theorem build3s_spec (g : Graph) {S : ℕ} (hS : sB3 g ≤ S) :
    HTB S build3s (fun c => c = initial (flowInput g (cycles g 3) 3))
      (fun c => c.out = netEnc3 (cycles g 3))
      (CB * ((cycles g 3).length * (cycles g 3).length + 1)) := by
  set t := (cycles g 3).length with ht
  have hf := Sort.ffits g 3 (ZeroCost.bD g 3) hS
  have hd : ZeroCost.bD g 3 ≤ S := by
    have := hf.1
    omega
  have h1 := ZeroCost.stepInit_spec (S := S) g 3 hd
  have h2 : HTB S Sort.front (ZeroCost.InitPost g 3)
      (fun c => OB (cycles g 3) 3 (Sort.fEID g 3 (ZeroCost.bD g 3)) (Sort.fCNT g 3 (ZeroCost.bD g 3)) c ∧
        c.out = [])
      (Sort.CF * (Sort.fL g 3 * (Nat.clog 2 (Sort.fL g 3) + 1) + 1)) :=
    HTB.of_forall fun c₀ hI => (Sort.front_spec g 3 c₀ (Sort.frontIn_of_initPost hI)
      (by rw [hI.rfree]; exact hS)).post fun c ⟨hP, _, ho⟩ => by
        rw [hI.rfree] at hP
        exact ⟨ob_of_front hP, by rw [ho, hI.rout]⟩
  have h3 := out3_specA (isCycle_cycles g 3) (S := S) hf.2.2.2.2.2.1 hf.2.2.2.2.2.2
  refine ((h1.seq (h2.seq h3)).pre fun c hc => hc).weaken ?_
  have hc := frontCost3_le t
  have e : Sort.fL g 3 = 3 * t := rfl
  rw [e]
  have e2 : CB * (t * t + 1) = 12 * Sort.CF * (t * t) + 200 * (t * t) + 12 * Sort.CF + 200 := by
    unfold CB; ring
  have e3 : Sort.CF * (3 * t * (Nat.clog 2 (3 * t) + 1) + 1) ≤ 12 * Sort.CF * (t * t) + Sort.CF := by
    have := Nat.mul_le_mul_left Sort.CF hc
    rw [Nat.mul_add, Nat.mul_one]
    nlinarith
  have htt : t ≤ t * t + 1 := by nlinarith
  rw [e2]
  omega

/-- **The memory of `build3s` is linear** in `t + m + 1`. -/
theorem sB3_le (g : Graph) : sB3 g ≤ 2 * g.length + 48 * (cycles g 3).length + 4 := by
  have := Sort.fEnd_le g 3 (ZeroCost.bD g 3)
  have e : ZeroCost.bD g 3 = 2 * g.length + 3 + 3 * (cycles g 3).length := rfl
  have e2 : Sort.fL g 3 = 3 * (cycles g 3).length := rfl
  unfold sB3
  omega

/-! ### The pipeline as one program -/

/-- The pipeline with the sorting front end: the construction within the space `sB3 g`, the
solver within `T (21t + 5)` steps and addresses, the extraction within `bD g cs 3 + 4t`. -/
theorem triangle_sort_core {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T) (g : Graph) :
    ∃ (out pos : List ℕ) (t₁ t₂ t₃ : ℕ),
      RAM.ComputesIn build3s (flowInput g (cycles g 3) 3) (netEnc3 (cycles g 3)) t₁ (sB3 g) ∧
        t₁ ≤ CB * ((cycles g 3).length * (cycles g 3).length + 1) ∧
      RAM.ComputesIn F (netEnc3 (cycles g 3)) out t₂ (T (21 * (cycles g 3).length + 5)) ∧
        t₂ ≤ T (21 * (cycles g 3).length + 5) ∧
      RAM.ComputesIn extract3 (flowInput g (cycles g 3) 3 ++ out) pos t₃
        (bD g (cycles g 3) 3 + 4 * (cycles g 3).length) ∧
        t₃ ≤ 15 * (cycles g 3).length + 20 ∧
      out.length = 7 * (cycles g 3).length + 1 ∧
      pos.length = (cycles g 3).length ∧ (∀ p ∈ pos, p < 3) ∧
      ValidChoices ((cycles g 3).map selectedOptions) (List.zipWith selected (cycles g 3) pos) ∧
      OptCost g 3 (cost (List.zipWith selected (cycles g 3) pos)) := by
  obtain ⟨t₁, ht₁, h₁⟩ := HTB.computesIn (build3s_spec g le_rfl)
  obtain ⟨out, pos, -, t₂, t₃, -, -, h₂, ht₂, h₃, ht₃, hol, hl, hlt, hv, hopt⟩ :=
    triangle_core hF (List.Perm.refl (cycles g 3))
  exact ⟨out, pos, t₁, t₂, t₃, h₁, ht₁, h₂, ht₂, h₃, ht₃, hol, hl, hlt, hv, hopt⟩

/-- **The triangle pipeline without label-indexed memory, as one RAM program** (the cited
min-cost flow program `F` a relocated subroutine): on `flowInput g (cycles g 3) 3` it writes the
positions of an optimal assignment of `CPAP(G, 3)` within `C (t² + m + 1) + 4 T(21t + 5)` steps,
accessing only the addresses below `C (t + m + 1) + 4 T(21t + 5)`. -/
theorem triangle_sort_single {F : RAM.Stmt} {T : ℕ → ℕ} (hF : MinCostFlowSolver F T) :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ g : Graph,
      ∃ (pos : List ℕ) (steps : ℕ),
        RAM.ComputesIn prog (flowInput g (cycles g 3) 3) pos steps
          (C * ((cycles g 3).length + g.length + 1) + 4 * T (21 * (cycles g 3).length + 5)) ∧
        steps ≤ C * ((cycles g 3).length * (cycles g 3).length + g.length + 1) +
          4 * T (21 * (cycles g 3).length + 5) ∧
        pos.length = (cycles g 3).length ∧ (∀ p ∈ pos, p < 3) ∧
        ValidChoices ((cycles g 3).map selectedOptions) (List.zipWith selected (cycles g 3) pos) ∧
        OptCost g 3 (cost (List.zipWith selected (cycles g 3) pos)) := by
  refine ⟨pipe3 lenFlow build3s F extract3, 4 * CB + 600, fun g => ?_⟩
  have hcs := isCycle_cycles g 3
  obtain ⟨out, pos, t₁, t₂, t₃, h₁, ht₁, h₂, ht₂, h₃, ht₃, hol, hl, hlt, hv, hopt⟩ :=
    triangle_sort_core hF g
  set t := (cycles g 3).length with ht
  have hx := length_flowInput hcs
  have hd : bD g (cycles g 3) 3 = 2 * g.length + 3 + 3 * t := rfl
  have hbv : bV g = 2 * g.length + 3 := rfl
  obtain ⟨steps, hc, hs⟩ :=
    pipe3_spec (lenFlow_spec hcs (S := bD g (cycles g 3) 3) (by omega)) h₁ h₂ h₃
  have hy : (netEnc3 (cycles g 3)).length = 21 * t + 5 := by
    rw [netEnc3, length_netInput, length_net3 hcs]; ring
  have hb := sB3_le g
  refine ⟨pos, steps, hc.mono ?_, ?_, hl, hlt, hv, hopt⟩
  · rw [hx, hy, hol]
    have e : (4 * CB + 600) * (t + g.length + 1) = 4 * CB * (t + g.length + 1) + 600 * t +
        600 * g.length + 600 := by ring
    have : 0 ≤ 4 * CB * (t + g.length + 1) := Nat.zero_le _
    rw [e]
    omega
  · rw [hx] at hs
    have e : (4 * CB + 600) * (t * t + g.length + 1) = 4 * (CB * (t * t + 1)) +
        4 * CB * g.length + 600 * (t * t) + 600 * g.length + 600 := by ring
    have htt : t ≤ t * t + 1 := by nlinarith
    rw [e]
    omega

/-- **The triangle pipeline without label-indexed memory, with an almost-linear min-cost flow
program**: within `C₀ (t² + m + 1) + C_ε t^{1+ε}` steps and `C₀ (t + m + 1) + C_ε t^{1+ε}`
addresses, for every `ε > 0` (`C₀` independent of `ε`). -/
theorem triangle_sort_single_almostLinear {F : RAM.Stmt} {T : ℕ → ℕ}
    (hF : MinCostFlowSolver F T) (hT : AlmostLinear T) :
    ∃ (prog : RAM.Stmt) (C₀ : ℕ), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ g : Graph,
      ∃ (pos : List ℕ) (steps space : ℕ),
        RAM.ComputesIn prog (flowInput g (cycles g 3) 3) pos steps space ∧
        (steps : ℝ) ≤ C₀ * (((cycles g 3).length * (cycles g 3).length : ℕ) + g.length + 1 : ℝ) +
          C * ((cycles g 3).length : ℝ) ^ (1 + ε) ∧
        (space : ℝ) ≤ C₀ * (((cycles g 3).length : ℝ) + g.length + 1) +
          C * ((cycles g 3).length : ℝ) ^ (1 + ε) ∧
        pos.length = (cycles g 3).length ∧ (∀ p ∈ pos, p < 3) ∧
        ValidChoices ((cycles g 3).map selectedOptions) (List.zipWith selected (cycles g 3) pos) ∧
        OptCost g 3 (cost (List.zipWith selected (cycles g 3) pos)) := by
  obtain ⟨prog, C₀, h⟩ := triangle_sort_single hF
  refine ⟨prog, C₀ + 4 * T 5, fun ε hε => ?_⟩
  obtain ⟨Cε, hCε⟩ := hT ε hε
  refine ⟨(4 : ℕ) * (Cε * (35 : ℝ) ^ (1 + ε)), fun g => ?_⟩
  obtain ⟨pos, steps, hc, hs, hl, hlt, hv, hopt⟩ := h g
  refine ⟨pos, steps, _, hc, ?_, ?_, hl, hlt, hv, hopt⟩
  · have := split_bound (s := steps)
      (L := (cycles g 3).length * (cycles g 3).length + g.length + 1) (k := 4) (C₀ := C₀)
      (t := (cycles g 3).length) (a := 21) hε (almostLinear_const hCε) hCε (by norm_num)
      (by omega) hs
    push_cast at this ⊢
    linarith
  · have := split_bound (s := C₀ * ((cycles g 3).length + g.length + 1) +
      4 * T (21 * (cycles g 3).length + 5)) (L := (cycles g 3).length + g.length + 1) (k := 4)
      (C₀ := C₀) (t := (cycles g 3).length) (a := 21) hε (almostLinear_const hCε) hCε
      (by norm_num) (by omega) le_rfl
    push_cast at this ⊢
    linarith

end STACS2027.Runtimes.Flow
