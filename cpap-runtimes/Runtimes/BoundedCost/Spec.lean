module

public import Runtimes.ZeroCost
import Mathlib.Tactic

/-!
# Theorem 4 on the RAM: the abstract side

The machine of Theorem 4 (`Runtimes/BoundedCost/Main.lean`) receives `boundedCostInput g k Ψ`: the input of
Corollary 5 (`zeroCostInput g k`: the graph, `k`, the number `t` of enumerated simple `k`-cycles
and their vertices) followed by the budget `Ψ`. It builds in memory the formula
`Γ' = almostFormula g k Ψ` of Section 4 *in Section 4's order*: `Ψ + 1` copies of the path
constraints `Γ₁` (`pcs g k (Ψ + 1)`), then the candidate-overlap clauses
`b_{C_i,e} ∨ b_{C_{i'},e}` for `i < i'` and the edges `e` of `C_i` (in the order of `C_i`) that
lie on `C_{i'}` (`ovI g k t = (candidateOverlaps g k).map (overlapClause g k)`, `ovI_full`).

The overlap clauses of a pair `(i, i')` are generated in `O(k)` steps with a mark table indexed
by the edge identifiers `eidOf` of Corollary 5 (computed by the sorting front end; the table
`SEEN` has one cell per distinct edge and is zero between pairs): the edges of `C_{i'}` are
marked with their variable `+ 1` (`markF`), the edges of `C_i` are scanned (`markF_eid`,
`ovCl_eq`: a nonzero mark is exactly an overlap, and it gives the second variable), and the
marks are cleared (`clearF_full`). This costs `O(kt²)` for all pairs, the `kt²` term of the
manuscript's bound.

* `updF`: a table after a sequence of updates; `updF_of_ne`, `updF_at`;
* `markF`, `clearF`, `markF_eid`, `clearF_full`;
* `ovCl`, `ovS`, `ovPairCl`, `ovJ`, `ovI` and `ovI_full`; `pcs` and `almostFormula_eq`;
* `input5_facts`, `input5z_facts`: the cells of the initial memory (followed by the solver's
  answer `z` for the extraction).
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT STACS2027.RAM STACS2027.Runtimes.ZeroCost

/-- **The input of Theorem 4's machine**: the input of Corollary 5, then `Ψ`. -/
def boundedCostInput (g : Graph) (k Ψ : ℕ) : List ℕ := zeroCostInput g k ++ [Ψ]

theorem length_boundedCostInput (g : Graph) (k Ψ : ℕ) : (boundedCostInput g k Ψ).length = bD g k + 1 := by
  simp [boundedCostInput, length_zeroCostInput]

/-- The cells of the initial memory on the input followed by `z` (the answer of the solver,
for the extraction). -/
theorem input5z_facts (g : Graph) (k Ψ : ℕ) (z : List ℕ) :
    (initial (boundedCostInput g k Ψ ++ z)).mem 0 = g.length ∧
      (initial (boundedCostInput g k Ψ ++ z)).mem (2 * g.length + 1) = k ∧
      (initial (boundedCostInput g k Ψ ++ z)).mem (2 * g.length + 2) = (cycles g k).length ∧
      Arr (initial (boundedCostInput g k Ψ ++ z)).mem (bV g) (verts g k) ∧
      (initial (boundedCostInput g k Ψ ++ z)).mem (bD g k) = Ψ ∧
      Arr (initial (boundedCostInput g k Ψ ++ z)).mem (bD g k + 1) z ∧
      ZeroFrom (initial (boundedCostInput g k Ψ ++ z)).mem (bD g k + 1 + z.length) := by
  have hA : Arr (initial (boundedCostInput g k Ψ ++ z)).mem 0
      (((graphInput g ++ (k :: (cycles g k).length :: verts g k)) ++ [Ψ]) ++ z) :=
    arr_initial (boundedCostInput g k Ψ ++ z)
  have hZ := zeroFrom_initial (boundedCostInput g k Ψ ++ z)
  rw [List.length_append, length_boundedCostInput] at hZ
  rw [arr_append, arr_append, arr_append] at hA
  obtain ⟨⟨⟨hG, hR⟩, hP⟩, hz⟩ := hA
  have hl : 0 + (graphInput g ++ k :: (cycles g k).length :: verts g k).length = bD g k := by
    rw [← length_zeroCostInput, Nat.zero_add]; rfl
  rw [length_graphInput, arr_cons, arr_cons] at hR
  rw [graphInput, arr_cons] at hG
  refine ⟨by simpa using hG.1, by simpa using hR.1, by simpa [Nat.add_assoc] using hR.2.1, ?_, ?_,
    ?_, hZ⟩
  · have := hR.2.2
    rwa [show 0 + (2 * g.length + 1) + 1 + 1 = bV g by rw [bV]; omega] at this
  · have := (arr_singleton).mp hP
    rwa [hl] at this
  · rwa [List.length_append, List.length_singleton, ← Nat.add_assoc, hl] at hz

/-- The cells of the initial memory read by the machine. -/
theorem input5_facts (g : Graph) (k Ψ : ℕ) :
    (initial (boundedCostInput g k Ψ)).mem 0 = g.length ∧
      (initial (boundedCostInput g k Ψ)).mem (2 * g.length + 1) = k ∧
      (initial (boundedCostInput g k Ψ)).mem (2 * g.length + 2) = (cycles g k).length ∧
      Arr (initial (boundedCostInput g k Ψ)).mem (bV g) (verts g k) ∧
      (initial (boundedCostInput g k Ψ)).mem (bD g k) = Ψ ∧
      ZeroFrom (initial (boundedCostInput g k Ψ)).mem (bD g k + 1) := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := input5z_facts g k Ψ []
  simp only [List.append_nil, List.length_nil, Nat.add_zero] at h1 h2 h3 h4 h5 h7
  exact ⟨h1, h2, h3, h4, h5, h7⟩

/-! ### Tables after a sequence of updates -/

/-- The table `f₀` after the updates `a j ↦ v j`, `j = 0, …, n − 1`. -/
def updF (a v f₀ : ℕ → ℕ) (n : ℕ) : ℕ → ℕ :=
  (List.range n).foldl (fun f j => Function.update f (a j) (v j)) f₀

theorem updF_succ (a v f₀ : ℕ → ℕ) (n : ℕ) :
    updF a v f₀ (n + 1) = Function.update (updF a v f₀ n) (a n) (v n) := by
  simp [updF, List.range_succ]

theorem updF_of_ne {a v f₀ : ℕ → ℕ} {n e : ℕ} (h : ∀ j < n, a j ≠ e) : updF a v f₀ n e = f₀ e := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [updF_succ, Function.update_of_ne (h n (by omega)).symm, ih (fun j hj => h j (by omega))]

theorem updF_at {a v f₀ : ℕ → ℕ} {n : ℕ} (hinj : ∀ j₁ < n, ∀ j₂ < n, a j₁ = a j₂ → j₁ = j₂)
    {j : ℕ} (hj : j < n) : updF a v f₀ n (a j) = v j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [updF_succ]
    by_cases hjn : j = n
    · subst hjn; simp
    · rw [Function.update_of_ne (fun h => hjn (hinj j hj n (by omega) h)),
        ih (fun j₁ h₁ j₂ h₂ => hinj j₁ (by omega) j₂ (by omega)) (by omega)]

/-! ### The marks -/

section marks

variable (g : Graph) (k : ℕ)

/-- The mark table after marking the first `j` edges of `C_{i'}`: the identifier of the edge
at position `j'` gets the variable `i'k + j'` plus one. -/
def markF (i' j : ℕ) : ℕ → ℕ :=
  updF (fun j' => eidOf g k (i' * k + j')) (fun j' => i' * k + j' + 1) (fun _ => 0) j

/-- The mark table after clearing the first `j` edges of `C_{i'}`. -/
def clearF (i' j : ℕ) : ℕ → ℕ :=
  updF (fun j' => eidOf g k (i' * k + j')) (fun _ => 0) (markF g k i' k) j

variable {g k}

theorem markF_succ (i' j : ℕ) :
    markF g k i' (j + 1) = Function.update (markF g k i' j) (eidOf g k (i' * k + j)) (i' * k + j + 1) :=
  updF_succ _ _ _ _

theorem clearF_succ (i' j : ℕ) :
    clearF g k i' (j + 1) = Function.update (clearF g k i' j) (eidOf g k (i' * k + j)) 0 :=
  updF_succ _ _ _ _

theorem clearF_zero (i' : ℕ) : clearF g k i' 0 = markF g k i' k := rfl

theorem markF_zero (i' : ℕ) : markF g k i' 0 = fun _ => 0 := rfl

/-- The edges of a cycle have distinct identifiers. -/
theorem mark_inj {i' : ℕ} (hi' : i' < (cycles g k).length) :
    ∀ j₁ < k, ∀ j₂ < k, eidOf g k (i' * k + j₁) = eidOf g k (i' * k + j₂) → j₁ = j₂ := by
  intro j₁ h₁ j₂ h₂ h
  rw [eidOf_eq_iff (occ_lt hi' h₁), occs_getD_cycleEdgeAt hi' h₁, occs_getD_cycleEdgeAt hi' h₂] at h
  exact edgeAt_inj (kCycle_isCycle g hi') h₁ h₂ h

/-- **The mark of an edge of `C_i`** after marking `C_{i'}`: its variable in `C_{i'}` plus one
if it lies on `C_{i'}`, else `0`. -/
theorem markF_eid {i i' j : ℕ} (hi : i < (cycles g k).length) (hi' : i' < (cycles g k).length)
    (hj : j < k) :
    markF g k i' k (eidOf g k (i * k + j)) =
      if (cycleEdges (kCycle g k i')).contains (cycleEdgeAt g k i j) = true then
        edgeVariable g k i' (cycleEdgeAt g k i j) + 1 else 0 := by
  by_cases hc : (cycleEdges (kCycle g k i')).contains (cycleEdgeAt g k i j) = true
  · simp only [hc, ↓reduceIte]
    have hm : cycleEdgeAt g k i j ∈ cycleEdges (kCycle g k i') := by simpa using hc
    have hj' : edgePosition g k i' (cycleEdgeAt g k i j) < k := edgePosition_lt hi' hm
    have hq : eidOf g k (i' * k + edgePosition g k i' (cycleEdgeAt g k i j)) = eidOf g k (i * k + j) := by
      rw [eidOf_eq_iff (occ_lt hi' hj'), occs_getD_cycleEdgeAt hi' hj', occs_getD_cycleEdgeAt hi hj,
        cycleEdgeAt_edgePosition hi' hm]
    rw [← hq]
    unfold markF
    rw [updF_at (mark_inj hi') hj']
    rfl
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    unfold markF
    rw [updF_of_ne]
    intro j' hj' h
    apply hc
    rw [eidOf_eq_iff (occ_lt hi' hj'), occs_getD_cycleEdgeAt hi' hj', occs_getD_cycleEdgeAt hi hj] at h
    rw [← h]
    simpa using cycleEdgeAt_mem hi' hj'

/-- After clearing all the marks of `C_{i'}`, the table is zero again. -/
theorem clearF_full {i' : ℕ} (hi' : i' < (cycles g k).length) : clearF g k i' k = fun _ => 0 := by
  funext e
  by_cases h : ∃ j < k, eidOf g k (i' * k + j) = e
  · obtain ⟨j, hj, rfl⟩ := h
    exact updF_at (mark_inj hi') hj
  · have h' : ∀ j < k, eidOf g k (i' * k + j) ≠ e := fun j hj he => h ⟨j, hj, he⟩
    unfold clearF markF
    rw [updF_of_ne h', updF_of_ne h']

end marks

/-! ### The overlap clauses in Section 4's order -/

section ov

variable (g : Graph) (k : ℕ)

/-- The overlap clause of the edge at position `j` of `C_i` with `C_{i'}`, if that edge lies on
`C_{i'}`. -/
def ovCl (i i' j : ℕ) : CNF :=
  if (cycleEdges (kCycle g k i')).contains (cycleEdgeAt g k i j) = true then
    [overlapClause g k (i, i', cycleEdgeAt g k i j)] else []

/-- The overlap clauses of the first `j` positions of `C_i` with `C_{i'}`. -/
def ovS (i i' j : ℕ) : CNF := (List.range j).flatMap (ovCl g k i i')

/-- The overlap clauses of the pair `(C_i, C_{i'})`. -/
def ovPairCl (i i' : ℕ) : CNF := ovS g k i i' k

/-- The overlap clauses of `C_i` with the cycles `C_{i'}`, `i < i' < j`. -/
def ovJ (i j : ℕ) : CNF := (List.range j).flatMap fun i' => if i < i' then ovPairCl g k i i' else []

/-- The overlap clauses of the cycles `C_{i₀}`, `i₀ < i`, with their later cycles. -/
def ovI (i : ℕ) : CNF := (List.range i).flatMap fun i₀ => ovJ g k i₀ (cycles g k).length

/-- The `r` copies of the path constraints. -/
def pcs (r : ℕ) : CNF := (List.replicate r (pathConstraints g k)).flatten

variable {g k}

theorem ovS_succ (i i' j : ℕ) : ovS g k i i' (j + 1) = ovS g k i i' j ++ ovCl g k i i' j := by
  simp [ovS, List.range_succ, List.flatMap_append]

theorem ovJ_succ (i j : ℕ) :
    ovJ g k i (j + 1) = ovJ g k i j ++ (if i < j then ovPairCl g k i j else []) := by
  simp [ovJ, List.range_succ, List.flatMap_append]

theorem ovJ_start (i : ℕ) : ovJ g k i 0 = [] := rfl

theorem ovI_succ (i : ℕ) : ovI g k (i + 1) = ovI g k i ++ ovJ g k i (cycles g k).length := by
  simp [ovI, List.range_succ, List.flatMap_append]

theorem pcs_succ (r : ℕ) : pcs g k (r + 1) = pcs g k r ++ pathConstraints g k := by
  simp [pcs, List.replicate_succ']

/-- The clause emitted at the scan of position `j` of `C_i` against the marks of `C_{i'}`. -/
theorem ovCl_eq {i i' j : ℕ} (hi : i < (cycles g k).length) (hi' : i' < (cycles g k).length)
    (hj : j < k) :
    ovCl g k i i' j = if markF g k i' k (eidOf g k (i * k + j)) = 0 then [] else
      [[⟨i * k + j, true⟩, ⟨markF g k i' k (eidOf g k (i * k + j)) - 1, true⟩]] := by
  rw [markF_eid hi hi' hj]
  unfold ovCl
  by_cases hc : (cycleEdges (kCycle g k i')).contains (cycleEdgeAt g k i j) = true
  · simp only [hc, ↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel, overlapClause,
      edgeVariable_eq hi hj, pathVariable]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]

theorem flatMap_ite_singleton {α β : Type} (l : List α) (p : α → Bool) (h : α → β) :
    l.flatMap (fun a => if p a = true then [h a] else []) = (l.filter p).map h := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases hp : p a = true
    · simp [hp, ih]
    · simp [hp, ih]

/-- **The machine's overlap clauses are Section 4's**, in the same order. -/
theorem ovI_full : ovI g k (cycles g k).length = (candidateOverlaps g k).map (overlapClause g k) := by
  unfold ovI ovJ candidateOverlaps
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro i hi
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro i' _
  by_cases hii : i < i'
  · simp only [hii, ↓reduceIte]
    have hc := kCycle_isCycle g (List.mem_range.mp hi)
    have hce : cycleEdges (kCycle g k i) = (List.range k).map (cycleEdgeAt g k i) := by
      have := map_getD_range (cycleEdges (kCycle g k i)) (0, 0)
      rw [hc.edge_length] at this
      exact this.symm
    rw [hce, List.filter_map, List.map_map, List.map_map]
    unfold ovPairCl ovS ovCl
    exact flatMap_ite_singleton _ _ _
  · simp only [hii, ↓reduceIte, List.map_nil]

/-- **The machine's formula is `Γ'`.** -/
theorem almostFormula_eq (Ψ : ℕ) :
    almostFormula g k Ψ = pcs g k (Ψ + 1) ++ ovI g k (cycles g k).length := by
  rw [ovI_full]; rfl

theorem length_pcs (r : ℕ) : (pcs g k r).length = r * (pathConstraints g k).length := by
  simp [pcs]

end ov

end STACS2027.Runtimes.BoundedCost
