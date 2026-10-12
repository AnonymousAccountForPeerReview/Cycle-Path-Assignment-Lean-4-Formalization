module

public import Runtimes.BoundedCost.Prog
import Mathlib.Tactic

/-!
# Theorem 4 on the RAM: the layout and the state of the generation phases

After phase 1 the free address is `bD g k` (the end of the cycles; the cell of `Ψ` is cleared),
and the sorting front end (`Sort.front_spec`, free address `F = bD g k`) leaves the edge
identifiers `EID` at `bE5 g k = Sort.fEID g k (bD g k)` and ends at `bS5 g k = Sort.fEnd g k
(bD g k)`. The machine of Theorem 4 then allocates the mark table `SEEN` (one cell per distinct
edge) at `bS5 g k`, and pushes the literal codes of `Γ'` from `bC5 g k = bS5 g k + nE` on.
No region depends on a vertex label: `bC5 g k ≤ 2m + 3 + 17kt + 1` (`lay5`).

`HS g k s F c`: the registers (`GA`, `EID`, `SEEN`, `CL`), the vertices of the cycles, the
identifiers, the mark table `s`, the codes of the clauses `F` pushed so far, free memory after
them, `rFREE` at the end of the codes, `gNC = |F|`, and no output. The pushes of the phases stay
below a space bound `S` as long as the codes of the formula after the push fit below `S`
(`HS.room`); `length_codes_flatMap_le` gives the monotonicity of the code lengths along the
loops.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost Complexity.SAT

/-! ### The layout -/

section layout

variable (g : Graph) (k : ℕ)

/-- The edge identifiers `EID` (`kt` cells). -/
def bE5 : ℕ := Sort.fEID g k (bD g k)
/-- The mark table `SEEN` (one cell per distinct edge): the end of the front end. -/
def bS5 : ℕ := Sort.fEnd g k (bD g k)
/-- The literal codes of `Γ'`. -/
def bC5 : ℕ := bS5 g k + (edgesOnCycles g k).length

/-- The layout as inequalities (for `omega`). -/
theorem lay5 : bV g + k * (cycles g k).length = bD g k ∧ bD g k + 1 ≤ bE5 g k ∧
    bE5 g k + k * (cycles g k).length ≤ bS5 g k ∧
    bC5 g k = bS5 g k + (edgesOnCycles g k).length ∧
    bS5 g k ≤ bD g k + 15 * (k * (cycles g k).length) + 1 ∧
    (edgesOnCycles g k).length ≤ k * (cycles g k).length ∧ bV g = 2 * g.length + 3 := by
  have h1 := Sort.fEID_eq g k (bD g k)
  have h2 := Sort.fEnd_le g k (bD g k)
  have h3 : Sort.fEnd g k (bD g k) = Sort.fEID g k (bD g k) + 2 * Sort.fL g k := by
    simp only [Sort.fEnd, Sort.fCNT]; omega
  have := nE_le g k
  refine ⟨rfl, ?_, ?_, rfl, h2, this, rfl⟩
  · unfold bE5; omega
  · unfold bE5 bS5; simp only [Sort.fL] at h3; omega

end layout

/-! ### The state -/

/-- The registers fixed during the generation phases. -/
@[mk_iff] structure HG (g : Graph) (k : ℕ) (c : Config) : Prop where
  ga : GA g k c
  reid : c.reg gEID = bE5 g k
  rseen : c.reg gSEEN = bS5 g k
  rcl : c.reg gCL = bC5 g k

/-- The memory of the generation phases. -/
structure HMem (g : Graph) (k : ℕ) (s : ℕ → ℕ) (F : CNF) (m : ℕ → ℕ) : Prop where
  mverts : Arr m (bV g) (verts g k)
  meid : Tab m (bE5 g k) (k * (cycles g k).length) (eidOf g k)
  mseen : Tab m (bS5 g k) (edgesOnCycles g k).length s
  mcodes : Arr m (bC5 g k) (TwoSat.codes F)
  mzero : ZeroFrom m (bC5 g k + (TwoSat.codes F).length)

/-- The state of the generation phases with the marks `s` and the clauses `F`. -/
def HS (g : Graph) (k : ℕ) (s : ℕ → ℕ) (F : CNF) (c : Config) : Prop :=
  HG g k c ∧ c.reg rFREE = bC5 g k + (TwoSat.codes F).length ∧ c.reg gNC = F.length ∧
    HMem g k s F c.mem ∧ c.out = []

/-- Pushing the two codes of a clause. -/
theorem HMem.push2 {g : Graph} {k : ℕ} {s : ℕ → ℕ} {F : CNF} {m : ℕ → ℕ} (h : HMem g k s F m)
    (l₁ l₂ : Literal) :
    HMem g k s (F ++ [[l₁, l₂]]) (upd (upd m (bC5 g k + (TwoSat.codes F).length) (TwoSat.code l₁))
      (bC5 g k + (TwoSat.codes F).length + 1) (TwoSat.code l₂)) := by
  have hl := lay5 g k
  refine ⟨(h.mverts.upd_of_disjoint (by rw [length_verts]; omega)).upd_of_disjoint
      (by rw [length_verts]; omega), (h.meid.upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
    (h.mseen.upd_of_disjoint (by omega)).upd_of_disjoint (by omega), ?_, ?_⟩
  · rw [codes_append_clause, show [TwoSat.code l₁, TwoSat.code l₂] = [TwoSat.code l₁] ++ [TwoSat.code l₂]
      from rfl, ← List.append_assoc]
    exact (h.mcodes.upd_snoc rfl).upd_snoc (by simp; omega)
  · rw [codes_append_clause]
    have := ZeroFrom.upd_at (ZeroFrom.upd_at h.mzero (TwoSat.code l₁)) (TwoSat.code l₂)
    simpa [Nat.add_assoc] using this

/-- Recording a mark. -/
theorem HMem.seen {g : Graph} {k : ℕ} {s : ℕ → ℕ} {F : CNF} {m : ℕ → ℕ} (h : HMem g k s F m)
    {e : ℕ} (he : e < (edgesOnCycles g k).length) (v : ℕ) :
    HMem g k (Function.update s e v) F (upd m (bS5 g k + e) v) := by
  have hl := lay5 g k
  exact ⟨h.mverts.upd_of_disjoint (by rw [length_verts]; omega), h.meid.upd_of_disjoint (by omega),
    h.mseen.upd rfl, h.mcodes.upd_of_disjoint (by omega), h.mzero.upd (by omega)⟩

theorem HG.regIndep (g : Graph) (k : ℕ) : RegIndep WG (HG g k) := by indep [hG_iff, gA_iff]

/-- The registers written by the overlap phase. -/
def WO : List ℕ := [rT, rFREE, gNC, sBase, sI, sW, sA, sJ, sP, sE, sZ, sU, sV]

theorem HG.regIndepO (g : Graph) (k : ℕ) : RegIndep WO (HG g k) := by indep [hG_iff, gA_iff]

/-- Emitting a clause. -/
theorem HS.emit {g : Graph} {k : ℕ} {s : ℕ → ℕ} {F : CNF} {c : Config} (h : HS g k s F c)
    (l₁ l₂ : Literal) {c' : Config} {W : List ℕ} (hW : RegIndep W (HG g k))
    (hreg : ∀ r, r ∉ W → c'.reg r = c.reg r)
    (hfree : c'.reg rFREE = c.reg rFREE + 2) (hnc : c'.reg gNC = c.reg gNC + 1)
    (hmem : c'.mem = upd (upd c.mem (c.reg rFREE) (TwoSat.code l₁)) (c.reg rFREE + 1) (TwoSat.code l₂))
    (hout : c'.out = c.out) : HS g k s (F ++ [[l₁, l₂]]) c' := by
  obtain ⟨hG, hfr, hn, hM, ho⟩ := h
  refine ⟨hW _ _ hreg hG, ?_, ?_, ?_, by rw [hout, ho]⟩
  · rw [hfree, hfr, codes_append_clause]; simp; omega
  · rw [hnc, hn]; simp
  · rw [hmem, hfr]; exact hM.push2 l₁ l₂

/-- The two pushes of a clause stay below `S` if the extended code array does. -/
theorem HS.room {S : ℕ} {g : Graph} {k : ℕ} {s : ℕ → ℕ} {F : CNF} {c : Config} (h : HS g k s F c)
    {l₁ l₂ : Literal} (hSp : bC5 g k + (TwoSat.codes (F ++ [[l₁, l₂]])).length ≤ S) :
    c.reg rFREE + 2 ≤ S := by
  rw [h.2.1]; rw [codes_append_clause] at hSp; simp at hSp; omega

/-- A store into the mark table. -/
theorem HS.seen {g : Graph} {k : ℕ} {s : ℕ → ℕ} {F : CNF} {c c' : Config} (h : HS g k s F c)
    {e : ℕ} (he : e < (edgesOnCycles g k).length) (v : ℕ)
    (hreg : ∀ r, r ∉ WO → c'.reg r = c.reg r) (hfree : c'.reg rFREE = c.reg rFREE)
    (hnc : c'.reg gNC = c.reg gNC) (hmem : c'.mem = upd c.mem (bS5 g k + e) v)
    (hout : c'.out = c.out) : HS g k (Function.update s e v) F c' := by
  obtain ⟨hG, hfr, hn, hM, ho⟩ := h
  exact ⟨(HG.regIndepO g k) _ _ hreg hG, by rw [hfree, hfr], by rw [hnc, hn],
    by rw [hmem]; exact hM.seen he v, by rw [hout, ho]⟩

/-! ### Monotonicity of the code lengths -/

theorem length_codes_append (F F' : CNF) :
    (TwoSat.codes (F ++ F')).length = (TwoSat.codes F).length + (TwoSat.codes F').length := by
  rw [codes_append, List.length_append]

/-- The codes of a prefix of a family are shorter. -/
theorem length_codes_flatMap_le (f : ℕ → CNF) {a b : ℕ} (h : a ≤ b) :
    (TwoSat.codes ((List.range a).flatMap f)).length ≤
      (TwoSat.codes ((List.range b).flatMap f)).length := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih =>
    rw [List.range_succ, List.flatMap_append, length_codes_append]; omega

end STACS2027.Runtimes.BoundedCost
