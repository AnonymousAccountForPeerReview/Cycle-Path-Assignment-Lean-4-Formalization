module

public import Runtimes.C4.EnumRep
import Mathlib.Tactic

/-!
# Phase ENUM, part 3: the insertion of one 2-path in the report walk

`insertP` inserts the 2-path `x – z – y` (registers `xX`, `xZ`, `xY`, with `x < y`: the key
`(x, y)`, read from the triples in the order `insS g`) into the list of `y` for the current
first component `x`:

1. `insStamp`: if `STP[y] ≠ x + 1` (the list of `y` was made for a smaller first component),
   `STP[y] := x + 1` and `HDS[y] := 0` (the empty list);
2. `insCell`: the head cell `xC := HDS + y`, the walker `xQ := M[xC]`;
3. `insWalk`: walk the list (`whileC (mov rT xQ) walkBody`), reporting `((x, y), z, z')` for
   every centre `z'` already in it (`reportB`);
4. `insNode`: a new node at `POOL + gNP` (centre `z`, successor the old head) becomes the
   head; `gNP += 2`.

**`insert_spec`**: from `ERep g c₁ L x (reports L)`, `insertP` reaches
`ERep g c₁ (L ++ [((x, y), z)]) x (reports (L ++ [((x, y), z)]))` (`reports_snoc`) within
`KS + KW · |bucket L (x, y)|` steps (`KW = 347`, one report per element of the list), the walk
being a ghost-indexed loop (`HTB.whileG`) over the number of visited nodes; every address is
below any `S ≥ scanEnd g F₁` (the reports of the prefix are at most the four-cycles).
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo STACS2027.RAM Finset

/-! ### The program -/

/-- The stamp of `y = xY` for the first component `x = xX`. -/
def insStamp : Stmt :=
  .seq (ld xS gSTP xY) (.seq (addc xD xX 1) (ifEq xS xD .skip
    (.seq (st gSTP xY xD) (.seq (.const xH 0) (st gHDS xY xH)))))

/-- The head cell `xC := HDS + y`, the head into the walker `xQ`. -/
def insCell : Stmt := .seq (.add xC gHDS xY) (.seq (.load xH xC) (mov xQ xH))

/-- One step of the walk: report, then move to the successor. -/
def walkBody : Stmt := .seq reportB (.seq (addc xQ xQ 1) (.load xQ xQ))

/-- The walk of the list. -/
def insWalk : Stmt := whileC (mov rT xQ) walkBody

/-- The new node at `POOL + gNP` heads the list. -/
def insNode : Stmt :=
  .seq (.load xH xC) (.seq (.add xW gPOOL gNP) (.seq (.store xW xZ) (.seq (addc xD xW 1)
    (.seq (.store xD xH) (.seq (.store xC xW) (addc gNP gNP 2))))))

/-- **Insertion** of the 2-path `xX – xZ – xY` (`xX < xY`). -/
def insertP : Stmt := .seq insStamp (.seq insCell (.seq insWalk insNode))

/-- The cost of one step of the walk (a report). -/
def KW : ℕ := 347

section

variable {g : Graph} {c₁ : Config} {S : ℕ}

/-- The invariant of the walk: `i` nodes of the list `bucket L k` visited. -/
def WInv (g : Graph) (c₁ : Config) (L : Ins) (k : ℕ × ℕ) (z : ℕ) (i : ℕ) (c : Config) : Prop :=
  ERep g c₁ L k.1 (reports L ++ ((bucket L k).take i).map fun z' => (k, z, z')) c ∧
    LL c.mem (bPOOL g (c₁.reg rFREE)) (bPOOL g (c₁.reg rFREE) + 2 * L.length) (c.reg xQ)
      ((bucket L k).drop i) ∧
    c.reg xX = k.1 ∧ c.reg xZ = z ∧ c.reg xY = k.2 ∧
    c.reg xC = bHDS g (c₁.reg rFREE) + k.2 ∧ c.reg rT = c.reg xQ ∧
    i ≤ (bucket L k).length ∧ c.mem (c₁.reg rFREE + k.2) = k.1 + 1

theorem mem_insS_of_bucket {L : Ins} (hpre : L <+: insS g) {k : ℕ × ℕ} {z' : ℕ}
    (h : z' ∈ bucket L k) : k.1 < k.2 ∧ k.2 < numV g ∧ z' < numV g :=
  lt_of_mem_insS (hpre.subset (mem_bucket.mp h))

/-- The reports up to an insertion are at most the four-cycles. -/
theorem length_reports_le {L : Ins} {k : ℕ × ℕ} {z : ℕ} (hpre : L ++ [(k, z)] <+: insS g) :
    (reports L).length + (bucket L k).length ≤ (cycles g 4).length := by
  rw [← length_reports_insS, ← length_reports_snoc]
  exact length_reports_le_of_prefix hpre

/-- **One step of the walk.** -/
theorem walk_round (hP : ScanPre g c₁) (hSp : scanEnd g (c₁.reg rFREE) ≤ S) {L : Ins}
    {k : ℕ × ℕ} {z : ℕ} (hk1 : k.1 < numV g) (hk2 : k.2 < numV g) (hz : z < numV g)
    (hpre : L ++ [(k, z)] <+: insS g) (i : ℕ) :
    HTBt S (.seq walkBody (mov rT xQ)) (fun c => WInv g c₁ L k z i c ∧ c.reg rT ≠ 0)
      (fun c' t => ∃ y, WInv g c₁ L k z y c' ∧
        KW * ((bucket L k).length - y) + t + 1 ≤ KW * ((bucket L k).length - i)) := by
  by_cases hi' : i < (bucket L k).length
  swap
  · intro c ⟨⟨_, hLL, _, _, _, _, hT, _⟩, hne⟩
    rw [List.drop_eq_nil_of_le (by omega)] at hLL
    exact absurd (by rw [hT, hLL]) hne
  refine HTB.toG (Inv := WInv g c₁ L k z) (Φ := fun y => KW * ((bucket L k).length - y))
    (y := i + 1) (b := 346) (HTB.run_le (by decide) (by decide) fun c hc => ?_)
    (by simp only [KW]; omega)
  obtain ⟨⟨hR, hLL, hX, hZ, hY, hC, hT, hi, hst⟩, hne⟩ := hc
  have hL := scan_layout g (c₁.reg rFREE)
  have hlen := hR.mem.len
  have hrl := length_reports_le hpre
  have hpl : L.length < numPaths g (peelPos g) := by
    have := hpre.length_le
    rw [length_insS] at this
    simp only [List.length_append, List.length_singleton] at this
    omega
  obtain ⟨z', rest, hd⟩ : ∃ z' rest, (bucket L k).drop i = z' :: rest := by
    rcases h : (bucket L k).drop i with _ | ⟨z', rest⟩
    · rw [h] at hLL; exact absurd (by rw [hT, hLL]) hne
    · exact ⟨z', rest, rfl⟩
  rw [hd] at hLL
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hLL
  have hz'm : z' ∈ bucket L k := by
    have : z' ∈ (bucket L k).drop i := by rw [hd]; exact List.mem_cons_self ..
    exact List.mem_of_mem_drop this
  have hz' := (mem_insS_of_bucket (hR.pre) hz'm).2.2
  have hgi : (bucket L k)[i] = z' := by
    have h1 : ((bucket L k).drop i)[0]? = some z' := by rw [hd]; rfl
    rw [List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hi'] at h1
    exact Option.some_injective _ h1
  have hdrop : (bucket L k).drop (i + 1) = rest := by
    rw [← List.drop_drop, hd]; rfl
  have htake : (bucket L k).take (i + 1) = (bucket L k).take i ++ [z'] := by
    rw [List.take_succ_eq_append_getElem hi', hgi]
  have hfree := hR.free
  have hRl : (reports L ++ ((bucket L k).take i).map fun z' => (k, z, z')).length = 
      (reports L).length + i := by
    simp [List.length_take, Nat.min_eq_left hi]
  have hfr4 : c.reg rFREE + 4 ≤ S := by
    rw [hfree, hRl]; unfold scanEnd at hSp; omega
  obtain ⟨hR₁, hreg₁, hmem₁, hA₁⟩ := reportB_run hP (by unfold scanEnd at hSp; omega) hR hk1 hk2
    hz hz' hX hY hZ rfl hq3 (by unfold scanEnd at hSp; omega) hfr4
  have hq1' : c.mem (c.reg xQ + 1) = (run reportB c).mem (c.reg xQ + 1) :=
    (hmem₁ _ (by rw [hfree]; omega)).symm
  have hst₁ : (run reportB c).mem (c₁.reg rFREE + k.2) = k.1 + 1 := by
    rw [hmem₁ _ (by rw [hfree]; omega), hst]
  have hrun : run (.seq walkBody (mov rT xQ)) c =
      run (.seq (addc xQ xQ 1) (.seq (.load xQ xQ) (mov rT xQ))) (run reportB c) := by
    simp [walkBody]
  have hQ₁ : (run reportB c).reg xQ = c.reg xQ := hreg₁ xQ (by decide)
  have hA₂ : AddrOK S (.seq (addc xQ xQ 1) (.seq (.load xQ xQ) (mov rT xQ))) (run reportB c) := by
    unfold scanEnd at hSp
    addr_ok [hQ₁]
  refine ⟨?_, ?_⟩
  · refine AddrOK.seq (AddrOK.seq hA₁ ⟨hA₂.1, hA₂.2.1⟩) ?_
    exact AddrOK.of_memFree rfl
  rw [hrun]
  generalize run reportB c = c₂ at hR₁ hreg₁ hmem₁ hq1' hQ₁ hst₁ hA₂
  have hR₂ : ERep g c₁ L k.1 (reports L ++ ((bucket L k).take (i + 1)).map fun z' => (k, z, z'))
      c₂ := by rw [htake, List.map_append, ← List.append_assoc]; exact hR₁
  refine ⟨(ERep.indep g c₁ L k.1 _).mono (W' := [rT, xQ]) (by decide) c₂ _
    (agree_run (by decide) rfl rfl (by decide) c₂) hR₂, ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩
  · rw [hdrop]
    simp +decide only [run_seq', run_addc (show xQ ≠ rT by decide), run_load, run_mov
      (show xQ ≠ rT by decide), setReg_reg, setReg_mem, ↓reduceIte, hQ₁]
    rw [← hq1']
    exact hq4.congr fun q h1 h2 => hmem₁ q (by rw [hfree]; omega)
  · simp +decide [run_addc, run_mov, hreg₁ xX (by decide), hX]
  · simp +decide [run_addc, run_mov, hreg₁ xZ (by decide), hZ]
  · simp +decide [run_addc, run_mov, hreg₁ xY (by decide), hY]
  · simp +decide [run_addc, run_mov, hreg₁ xC (by decide), hC]
  · simp +decide [run_addc, run_mov]
  · simpa [run_addc, run_mov] using hst₁

/-- The cost of an insertion besides the walk. -/
def KS : ℕ := 37

/-- **Insertion** of the 2-path `x – z – y` (`x < y`) for the current first component `x`. -/
theorem insert_spec (hP : ScanPre g c₁) (hSp : scanEnd g (c₁.reg rFREE) ≤ S) {L : Ins}
    {x y z : ℕ} (hx : x < numV g) (hy : y < numV g) (hz : z < numV g)
    (hpre : L ++ [((x, y), z)] <+: insS g) :
    HTB S insertP (fun c => ERep g c₁ L x (reports L) c ∧ c.reg xX = x ∧ c.reg xZ = z ∧
        c.reg xY = y)
      (ERep g c₁ (L ++ [((x, y), z)]) x (reports (L ++ [((x, y), z)])))
      (19 + (7 + ((2 + (KW * (bucket L (x, y)).length + 1)) + 9))) := by
  have hL := scan_layout g (c₁.reg rFREE)
  have hS' : bCYC g (c₁.reg rFREE) ≤ S := by unfold scanEnd at hSp; omega
  have hlt : L.length < numPaths g (peelPos g) := by
    have := hpre.length_le
    rw [length_insS] at this
    simp only [List.length_append, List.length_singleton] at this
    omega
  -- the stamp
  have h₁ : HTB S insStamp (fun c => ERep g c₁ L x (reports L) c ∧ c.reg xX = x ∧
        c.reg xZ = z ∧ c.reg xY = y)
      (fun c => (ERep g c₁ L x (reports L) c ∧ c.reg xX = x ∧ c.reg xZ = z ∧ c.reg xY = y) ∧
        c.mem (c₁.reg rFREE + y) = x + 1) 19 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hR, hX, hZ, hY⟩ => ?_
    have hG := hR.glob
    refine ⟨by addr_ok [insStamp, hG.stp, hG.hds, hX, hY], ?_⟩
    have hrun : run insStamp c = run (ifEq xS xD .skip (.seq (st gSTP xY xD)
        (.seq (.const xH 0) (st gHDS xY xH)))) (run (.seq (ld xS gSTP xY) (addc xD xX 1)) c) := by
      simp [insStamp]
    set c₂ := run (.seq (ld xS gSTP xY) (addc xD xX 1)) c with hc₂
    have hR₂ : ERep g c₁ L x (reports L) c₂ :=
      (ERep.indep g c₁ L x _).mono (W' := [xS, xD, rT]) (by decide) c c₂
        (agree_run (by decide) rfl rfl (by decide) c) hR
    have hS₂ : c₂.reg xS = c.mem (c₁.reg rFREE + y) := by
      simp +decide [hc₂, run_addc, hG.stp, hY]
    have hD₂ : c₂.reg xD = x + 1 := by simp +decide [hc₂, run_addc, hX]
    have hX₂ : c₂.reg xX = x := by simp +decide [hc₂, run_addc, hX]
    have hY₂ : c₂.reg xY = y := by simp +decide [hc₂, run_addc, hY]
    have hZ₂ : c₂.reg xZ = z := by simp +decide [hc₂, run_addc, hZ]
    have hm₂ : c₂.mem = c.mem := by simp [hc₂, run_addc]
    rw [hrun, run_ifEq (by decide) (by decide)]
    by_cases he : c.mem (c₁.reg rFREE + y) = x + 1
    · have hif : c₂.reg xS = c₂.reg xD := by rw [hS₂, hD₂, he]
      simp only [hif, ↓reduceIte, run_skip]
      refine ⟨⟨(ERep.indep g c₁ L x _).setReg (by decide) _ hR₂, ?_, ?_, ?_⟩, ?_⟩
      · simp +decide [hX₂]
      · simp +decide [hZ₂]
      · simp +decide [hY₂]
      · simp [hm₂, he]
    · have hif : c₂.reg xS ≠ c₂.reg xD := by rw [hS₂, hD₂]; exact he
      simp only [hif, ↓reduceIte]
      have hG₂ := hR₂.glob
      have hm := hR.mem.stamp hy he
      refine ⟨⟨⟨(EGlob.regIndep g c₁).run_of_sub (by decide) (by decide)
        ((EGlob.regIndep g c₁).setReg (by decide) _ hG₂), ?_, ?_, ?_, hR.pre, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
      · simp +decide [run_st, hR₂.np]
      · simp +decide [run_st, hR₂.t]
      · simp +decide [run_st, hR₂.free]
      · simpa +decide [run_st, hG₂.stp, hG₂.hds, hY₂, hD₂, hm₂] using hm
      · simp +decide [run_st, hX₂]
      · simp +decide [run_st, hZ₂]
      · simp +decide [run_st, hY₂]
      · have hne : c₁.reg rFREE + y ≠ bHDS g (c₁.reg rFREE) + y := by unfold bHDS; omega
        simp +decide only [run_seq', run_st, run_const, setReg_reg, setReg_mem, setMem_mem_upd,
          setMem_reg, ↓reduceIte, hG₂.stp, hG₂.hds, hY₂, hD₂]
        rw [upd_ne _ _ hne, upd_same]
  -- the cell and the head
  have h₂ : HTB S insCell
      (fun c => (ERep g c₁ L x (reports L) c ∧ c.reg xX = x ∧ c.reg xZ = z ∧ c.reg xY = y) ∧
        c.mem (c₁.reg rFREE + y) = x + 1)
      (fun c => ERep g c₁ L x (reports L) c ∧
        LL c.mem (bPOOL g (c₁.reg rFREE)) (bPOOL g (c₁.reg rFREE) + 2 * L.length) (c.reg xQ)
          (bucket L (x, y)) ∧
        c.reg xX = x ∧ c.reg xZ = z ∧ c.reg xY = y ∧
        c.reg xC = bHDS g (c₁.reg rFREE) + y ∧ c.mem (c₁.reg rFREE + y) = x + 1) 7 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hX, hZ, hY⟩, hst⟩ => ?_
    have hG := hR.glob
    refine ⟨by addr_ok [insCell, hG.hds, hY], ?_⟩
    have hcell : y + bHDS g (c₁.reg rFREE) = bHDS g (c₁.reg rFREE) + y := by ring
    refine ⟨(ERep.indep g c₁ L x _).mono (W' := [xC, xH, rT, xQ]) (by decide) c _
      (agree_run (by decide) rfl rfl (by decide) c) hR, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp +decide only [insCell, run_seq', run_add, run_load, run_mov
        (show xH ≠ rT by decide), setReg_reg, setReg_mem, ↓reduceIte, hG.hds, hY]
      exact hR.mem.hd y hy hst
    · simp +decide [insCell, run_mov, hX]
    · simp +decide [insCell, run_mov, hZ]
    · simp +decide [insCell, run_mov, hY]
    · simp +decide [insCell, run_mov, hG.hds, hY]
    · simpa [insCell, run_mov] using hst
  -- the walk
  have hinit : HTB S (mov rT xQ) (fun c => ERep g c₁ L x (reports L) c ∧
        LL c.mem (bPOOL g (c₁.reg rFREE)) (bPOOL g (c₁.reg rFREE) + 2 * L.length) (c.reg xQ)
          (bucket L (x, y)) ∧
        c.reg xX = x ∧ c.reg xZ = z ∧ c.reg xY = y ∧
        c.reg xC = bHDS g (c₁.reg rFREE) + y ∧ c.mem (c₁.reg rFREE + y) = x + 1)
      (WInv g c₁ L (x, y) z 0) 2 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨hR, hLL, hX, hZ, hY, hC, hst⟩ => ?_
    rw [run_mov (by decide)]
    refine ⟨(ERep.indep g c₁ L x _).setReg (by decide) _ ((ERep.indep g c₁ L x _).setReg
      (by decide) _ (by simpa using hR)), ?_, ?_, ?_, ?_, ?_, ?_, Nat.zero_le _, by simpa using hst⟩
    · simpa +decide using hLL
    · simp +decide [hX]
    · simp +decide [hZ]
    · simp +decide [hY]
    · simp +decide [hC]
    · simp +decide
  have h₃ := HTB.whileG (cond := mov rT xQ) (body := walkBody) (WInv g c₁ L (x, y) z)
    (fun i => KW * ((bucket L (x, y)).length - i)) 0 hinit
    (walk_round hP hSp hx hy hz hpre)
  -- the new node
  have h₄ : HTB S insNode (fun c => ∃ i, WInv g c₁ L (x, y) z i c ∧ c.reg rT = 0)
      (ERep g c₁ (L ++ [((x, y), z)]) x (reports (L ++ [((x, y), z)]))) 9 := by
    refine HTB.run_le (by decide) (by decide)
      fun c ⟨i, ⟨hR, hLL, _, hZ, _, hC, hT, hi, hst⟩, h0⟩ => ?_
    -- the walk is complete
    have hiB : i = (bucket L (x, y)).length := by
      by_contra hne
      obtain ⟨z', rest, hd⟩ : ∃ z' rest, (bucket L (x, y)).drop i = z' :: rest := by
        rcases h : (bucket L (x, y)).drop i with _ | ⟨z', rest⟩
        · rw [List.drop_eq_nil_iff] at h; omega
        · exact ⟨z', rest, rfl⟩
      rw [hd] at hLL
      have := hLL.ne_zero (by rw [hL.2.1]; have := hP.base.free_pos; omega)
      rw [← hT, h0] at this
      exact this rfl
    rw [hiB, List.take_length, ← reports_snoc] at hR
    have hG := hR.glob
    have hnp := hR.np
    have hm := hR.mem.node (z := z) hy hst hlt
    refine ⟨by addr_ok [insNode, hG.pool, hnp, hC], ?_⟩
    refine ⟨(EGlob.regIndep g c₁).run_of_sub (by decide) (by decide) hG, ?_, ?_, ?_, hpre, ?_⟩
    · simp +decide [insNode, run_addc, hnp]; ring
    · simp +decide [insNode, run_addc, hR.t]
    · simp +decide [insNode, run_addc, hR.free]
    · simpa +decide [insNode, run_addc, hG.pool, hnp, hC, hZ] using hm
  exact (h₁.seq (h₂.seq (h₃.seq h₄)))

end

end STACS2027.Runtimes.C4
