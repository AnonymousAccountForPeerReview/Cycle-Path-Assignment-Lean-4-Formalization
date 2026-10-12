module

public import Runtimes.ZeroCostEdges
import Mathlib.Tactic

/-!
# Corollary 5 on the RAM: building the formula

Phases 6 and 7 of `zeroCostProg` push the literal codes (`TwoSat.codes`) of the formula
`zcf g k` at `bCL g k`, growing into free memory (`rFREE` is the push pointer); they access
only the addresses below any `S ≥ bCL g k + |codes F|`, `F` the formula at the end of the
phase (every push extends a prefix of it: `length_codes_pcI_le`, `length_codes_occPre_le`):
* `stepPc_spec`: the path constraints `pcList k t = pathConstraints g k`, cycle by cycle,
  pair of positions by pair of positions;
* `stepOcc_spec`: for each occurrence `q`, with `e = EID[q]`, the clauses
  `occClOf q x p o = occCl g k q` for `x = SEEN[e] = rank g k q`, `p = CNT[e]`, `o = OFF[e]`, then
  `SEEN[e] := x + 1`. Afterwards the code array holds `codes (zcf g k)` and `gNC = |zcf g k|`
  (`OccPost`).
-/

@[expose] public section

namespace STACS2027.Runtimes.ZeroCost

open STACS2027 STACS2027.RAM STACS2027.RAM.R0 Complexity.SAT

variable {S : ℕ}

/-! ### The state of the generation phases -/

/-- The registers fixed during the generation phases. -/
@[mk_iff] structure GG (g : Graph) (k : ℕ) (c : Config) : Prop where
  ga : GA g k c
  reid : c.reg gEID = bEID g k
  rcnt : c.reg gCNT = bCNT g k
  roff : c.reg gOFF = bOFF g k
  rseen : c.reg gSEEN = bSEEN g k
  rcl : c.reg gCL = bCL g k

/-- The memory of the generation phases: the arrays of phase 5, the ranks seen `s`, and the
codes of the clauses `F` followed by free memory. -/
structure GMem (g : Graph) (k : ℕ) (s : ℕ → ℕ) (F : CNF) (m : ℕ → ℕ) : Prop where
  mverts : Arr m (bV g) (verts g k)
  meid : Tab m (bEID g k) (k * (cycles g k).length) (eidOf g k)
  mcnt : Tab m (bCNT g k) (k * (cycles g k).length) (cntF g k (k * (cycles g k).length))
  moff : Tab m (bOFF g k) (edgesOnCycles g k).length (offF g k)
  mseen : Tab m (bSEEN g k) (edgesOnCycles g k).length s
  mcodes : Arr m (bCL g k) (TwoSat.codes F)
  mzero : ZeroFrom m (bCL g k + (TwoSat.codes F).length)

/-- The state of the generation phases with ranks `s` and clauses `F`. -/
def GState (g : Graph) (k : ℕ) (s : ℕ → ℕ) (F : CNF) (c : Config) : Prop :=
  GG g k c ∧ c.reg rFREE = bCL g k + (TwoSat.codes F).length ∧ c.reg gNC = F.length ∧
    GMem g k s F c.mem ∧ c.out = []

theorem codes_append_clause (F : CNF) (l₁ l₂ : Literal) :
    TwoSat.codes (F ++ [[l₁, l₂]]) = TwoSat.codes F ++ [TwoSat.code l₁, TwoSat.code l₂] := by
  simp [TwoSat.codes]

theorem codes_append (F F' : CNF) : TwoSat.codes (F ++ F') = TwoSat.codes F ++ TwoSat.codes F' := by
  simp [TwoSat.codes]

theorem code_pos (v : ℕ) : TwoSat.code ⟨v, true⟩ = v + v := by simp [TwoSat.code]; ring
theorem code_neg (v : ℕ) : TwoSat.code ⟨v, false⟩ = v + v + 1 := by simp [TwoSat.code]; ring

/-- Pushing the two codes of a clause. -/
theorem GMem.push2 {g : Graph} {k : ℕ} {s : ℕ → ℕ} {F : CNF} {m : ℕ → ℕ} (h : GMem g k s F m)
    (l₁ l₂ : Literal) :
    GMem g k s (F ++ [[l₁, l₂]]) (upd (upd m (bCL g k + (TwoSat.codes F).length) (TwoSat.code l₁))
      (bCL g k + (TwoSat.codes F).length + 1) (TwoSat.code l₂)) := by
  have hl := layout_eqs g k
  have hne := nE_le g k
  refine ⟨(h.mverts.upd_of_disjoint (by rw [length_verts]; omega)).upd_of_disjoint
      (by rw [length_verts]; omega), (h.meid.upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
    (h.mcnt.upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
    (h.moff.upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
    (h.mseen.upd_of_disjoint (by omega)).upd_of_disjoint (by omega), ?_, ?_⟩
  · rw [codes_append_clause, show [TwoSat.code l₁, TwoSat.code l₂] = [TwoSat.code l₁] ++ [TwoSat.code l₂]
      from rfl, ← List.append_assoc]
    exact (h.mcodes.upd_snoc rfl).upd_snoc (by simp; omega)
  · rw [codes_append_clause]
    have := ZeroFrom.upd_at (ZeroFrom.upd_at h.mzero (TwoSat.code l₁)) (TwoSat.code l₂)
    simpa [Nat.add_assoc] using this

/-- Recording a rank. -/
theorem GMem.seen {g : Graph} {k : ℕ} {s : ℕ → ℕ} {F : CNF} {m : ℕ → ℕ} (h : GMem g k s F m)
    {e : ℕ} (he : e < (edgesOnCycles g k).length) (v : ℕ) :
    GMem g k (Function.update s e v) F (upd m (bSEEN g k + e) v) := by
  have hl := layout_eqs g k
  have hne := nE_le g k
  exact ⟨h.mverts.upd_of_disjoint (by rw [length_verts]; omega), h.meid.upd_of_disjoint (by omega),
    h.mcnt.upd_of_disjoint (by omega), h.moff.upd_of_disjoint (by omega), h.mseen.upd rfl,
    h.mcodes.upd_of_disjoint (by omega), h.mzero.upd (by omega)⟩

/-- The registers written by the generation phases. -/
def WG : List ℕ := [rT, rFREE, gNC, sQ, sI, sA, sB, sX, sY, sU, sV, sBase, sE, sR, sP, sO, sS]

theorem GG.regIndep (g : Graph) (k : ℕ) : RegIndep WG (GG g k) := by indep [gG_iff, gA_iff]

/-- Emitting a clause: the two codes in `sU`, `sV` computed by `pre₁`, `pre₂`. -/
theorem GState.emit {g : Graph} {k : ℕ} {s : ℕ → ℕ} {F : CNF} {c : Config} (h : GState g k s F c)
    (l₁ l₂ : Literal) {c' : Config}
    (hreg : ∀ r, r ∉ WG → c'.reg r = c.reg r)
    (hfree : c'.reg rFREE = c.reg rFREE + 2) (hnc : c'.reg gNC = c.reg gNC + 1)
    (hmem : c'.mem = upd (upd c.mem (c.reg rFREE) (TwoSat.code l₁)) (c.reg rFREE + 1) (TwoSat.code l₂))
    (hout : c'.out = c.out) : GState g k s (F ++ [[l₁, l₂]]) c' := by
  obtain ⟨hG, hfr, hn, hM, ho⟩ := h
  refine ⟨(GG.regIndep g k) _ _ hreg hG, ?_, ?_, ?_, by rw [hout, ho]⟩
  · rw [hfree, hfr, codes_append_clause]; simp; omega
  · rw [hnc, hn]; simp
  · rw [hmem, hfr]; exact hM.push2 l₁ l₂

/-- The two pushes of a clause stay below `S` if the extended code array does. -/
theorem GState.room {g : Graph} {k : ℕ} {s : ℕ → ℕ} {F : CNF} {c : Config} (h : GState g k s F c)
    {l₁ l₂ : Literal} (hSp : bCL g k + (TwoSat.codes (F ++ [[l₁, l₂]])).length ≤ S) :
    c.reg rFREE + 2 ≤ S := by
  rw [h.2.1]; rw [codes_append_clause] at hSp; simp at hSp; omega

/-! ### Phase 6: the path constraints -/

section pc

variable (k : ℕ)

/-- The path constraints of the first `i` cycles. -/
def pcI (i : ℕ) : CNF :=
  (List.range i).flatMap fun i' => (List.range k).flatMap fun a => (List.range k).flatMap (pcCl k i' a)

/-- The path constraints of cycle `i` with first position below `a`. -/
def pcA (i a : ℕ) : CNF := (List.range a).flatMap fun a' => (List.range k).flatMap (pcCl k i a')

/-- The path constraints of cycle `i`, first position `a`, second position below `b`. -/
def pcB (i a b : ℕ) : CNF := (List.range b).flatMap (pcCl k i a)

theorem pcB_succ (i a b : ℕ) : pcB k i a (b + 1) = pcB k i a b ++ pcCl k i a b := by
  simp [pcB, List.range_succ, List.flatMap_append]

theorem pcA_succ (i a : ℕ) : pcA k i (a + 1) = pcA k i a ++ pcB k i a k := by
  simp [pcA, pcB, List.range_succ, List.flatMap_append]

theorem pcI_succ (i : ℕ) : pcI k (i + 1) = pcI k i ++ pcA k i k := by
  simp [pcI, pcA, List.range_succ, List.flatMap_append]

theorem pcI_full (g : Graph) : pcI k (cycles g k).length = pathConstraints g k := pcList_eq g k

theorem length_codes_pcB_le (i a : ℕ) {b b' : ℕ} (h : b ≤ b') :
    (TwoSat.codes (pcB k i a b)).length ≤ (TwoSat.codes (pcB k i a b')).length := by
  induction b', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => rw [pcB_succ, codes_append, List.length_append]; omega

theorem length_codes_pcA_le (i : ℕ) {a a' : ℕ} (h : a ≤ a') :
    (TwoSat.codes (pcA k i a)).length ≤ (TwoSat.codes (pcA k i a')).length := by
  induction a', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => rw [pcA_succ, codes_append, List.length_append]; omega

theorem length_codes_pcI_le {i i' : ℕ} (h : i ≤ i') :
    (TwoSat.codes (pcI k i)).length ≤ (TwoSat.codes (pcI k i')).length := by
  induction i', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => rw [pcI_succ, codes_append, List.length_append]; omega

end pc

/-- The state at pair `(a, b)` of cycle `i`. -/
def PcInv (g : Graph) (k i a b : ℕ) (c : Config) : Prop :=
  GState g k (cntF g k 0) (pcI k i ++ pcA k i a ++ pcB k i a b) c ∧ c.reg sBase = i * k ∧
    c.reg sI = i ∧ c.reg sA = a

theorem pcEmit_run {g : Graph} {k : ℕ} {F : CNF} {c : Config} (h : GState g k (cntF g k 0) F c)
    {base a b : ℕ} (hB : c.reg sBase = base) (hA : c.reg sA = a) (hb : c.reg sB = b) :
    GState g k (cntF g k 0) (F ++ [[⟨base + a, false⟩, ⟨base + b, false⟩]]) (run pcEmit c) ∧
      ∀ r, r ∉ [sU, sV, rT, rFREE, gNC] → (run pcEmit c).reg r = c.reg r := by
  have hfr : ∀ r, r ∉ [sU, sV, rT, rFREE, gNC] → (run pcEmit c).reg r = c.reg r := fun r hr =>
    run_reg_of_not_mem (by decide) (fun h => hr (by
      have : ∀ x ∈ wregs pcEmit, x ∈ [sU, sV, rT, rFREE, gNC] := by decide
      exact this r h)) c
  refine ⟨h.emit _ _ (fun r hr => hfr r fun h' => hr (by
      have : ∀ x ∈ [sU, sV, rT, rFREE, gNC], x ∈ WG := by decide
      exact this r h')) ?_ ?_ ?_ ?_, hfr⟩
  · simp +decide [pcEmit, run_push, run_inc]
  · simp +decide [pcEmit, run_push, run_inc]
  · simp +decide only [pcEmit, run_seq', run_add, run_inc (show sU ≠ rT by decide),
      run_inc (show sV ≠ rT by decide), run_inc (show gNC ≠ rT by decide), run_push, setReg_reg,
      setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte, hB, hA, hb, code_neg]
  · simp [pcEmit, run_push, run_inc]

theorem pcCl_pos {k i a b : ℕ} (h : a + 1 < b ∧ ¬ (a = 0 ∧ b + 1 = k)) :
    pcCl k i a b = [[⟨i * k + a, false⟩, ⟨i * k + b, false⟩]] := by
  unfold pcCl; rw [ite_eq_left h]

theorem pcCl_neg {k i a b : ℕ} (h : ¬ (a + 1 < b ∧ ¬ (a = 0 ∧ b + 1 = k))) : pcCl k i a b = [] := by
  unfold pcCl; rw [ite_eq_right h]

theorem PcInv.indep (g : Graph) (k i a b : ℕ) : Indep [rT, sX, sY] (PcInv g k i a b) := by
  indep [PcInv, GState, gG_iff, gA_iff]

/-- The addresses of `pcEmit`: the two pushes at `rFREE`. -/
theorem pcEmit_addrOK {c : Config} (hF : c.reg rFREE + 2 ≤ S) : AddrOK S pcEmit c := by
  addr_ok [pcEmit, push]

theorem pcBody_spec (g : Graph) (k i a b : ℕ)
    (hSp : bCL g k + (TwoSat.codes (pcI k i ++ pcA k i a ++ pcB k i a (b + 1))).length ≤ S) :
    HTB S pcBody (fun c => PcInv g k i a b c ∧ c.reg sB = b ∧ c.reg gK = k)
      (fun c => PcInv g k i a (b + 1) c ∧ c.reg sB = b ∧ c.reg gK = k) 61 := by
  -- the two outcomes
  have hemit : HTB S pcEmit (fun c => (PcInv g k i a b c ∧ c.reg sB = b ∧ c.reg gK = k) ∧
        (a + 1 < b ∧ ¬ (a = 0 ∧ b + 1 = k)))
      (fun c => PcInv g k i a (b + 1) c ∧ c.reg sB = b ∧ c.reg gK = k) 16 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨⟨hS, hB, hI, hA⟩, hb, hK⟩, hc⟩ => ?_
    obtain ⟨hS', hfr⟩ := pcEmit_run hS hB hA hb
    have hl : pcI k i ++ pcA k i a ++ pcB k i a (b + 1) =
        pcI k i ++ pcA k i a ++ pcB k i a b ++ [[⟨i * k + a, false⟩, ⟨i * k + b, false⟩]] := by
      rw [pcB_succ, pcCl_pos hc]; simp only [List.append_assoc]
    rw [hl] at hSp
    exact ⟨pcEmit_addrOK (hS.room hSp), ⟨by rw [hl]; exact hS', by rw [hfr sBase (by decide), hB],
      by rw [hfr sI (by decide), hI], by rw [hfr sA (by decide), hA]⟩, by rw [hfr sB (by decide), hb],
      by rw [hfr gK (by decide), hK]⟩
  have hskip : HTB S .skip (fun c => (PcInv g k i a b c ∧ c.reg sB = b ∧ c.reg gK = k) ∧
        ¬ (a + 1 < b ∧ ¬ (a = 0 ∧ b + 1 = k)))
      (fun c => PcInv g k i a (b + 1) c ∧ c.reg sB = b ∧ c.reg gK = k) 1 := by
    refine HTB.run_le (by decide) le_rfl fun c ⟨h, hc⟩ => ⟨trivial, ?_⟩
    rw [run_skip, PcInv, pcB_succ, pcCl_neg hc, List.append_nil]
    exact h
  have hP1 : Indep [rT, sX, sY] (fun c => PcInv g k i a b c ∧ c.reg sB = b ∧ c.reg gK = k) :=
    (PcInv.indep g k i a b).and (by indep)
  have h1 := HTB.addc (S := S) (d := sX) (a := sA) (k := 1) (x := a) (show sA ≠ rT by decide)
    (hP1.mono (by decide)) (fun c h => h.1.2.2.2)
  -- the branch `a + 1 < b`
  have hS : HTB S (.seq (addc sY sB 1) (.ifz sA (ifEq sY gK .skip pcEmit) pcEmit))
      (fun c => ((PcInv g k i a b c ∧ c.reg sB = b ∧ c.reg gK = k) ∧ c.reg sX = a + 1) ∧
        c.reg sX < c.reg sB)
      (fun c => PcInv g k i a (b + 1) c ∧ c.reg sB = b ∧ c.reg gK = k) 23 := by
    have hY := HTB.addc (S := S) (d := sY) (a := sB) (k := 1) (x := b) (show sB ≠ rT by decide)
      (P := fun c => ((PcInv g k i a b c ∧ c.reg sB = b ∧ c.reg gK = k) ∧ c.reg sX = a + 1) ∧
        c.reg sX < c.reg sB) (by indep [PcInv, GState, gG_iff, gA_iff]) (fun c h => h.1.1.2.1)
    refine (hY.seq (HTB.ifz (b := 20) ?_ ?_)).weaken (by omega)
    · refine HTB.ifEq (B := 16) (show sY ≠ rT by decide) (show gK ≠ rT by decide)
        (by indep [PcInv, GState, gG_iff, gA_iff]) ?_ ?_
      · refine (hskip.pre fun c ⟨⟨⟨⟨⟨hP, _⟩, _⟩, hY⟩, h0⟩, heq⟩ => ⟨hP, ?_⟩).weaken (by omega)
        have ha : a = 0 := by rw [← hP.1.2.2.2, h0]
        have hk : b + 1 = k := by rw [← hY, heq, hP.2.2]
        exact fun ⟨_, hn⟩ => hn ⟨ha, hk⟩
      · refine hemit.pre fun c ⟨⟨⟨⟨⟨hP, hX⟩, hlt⟩, hY⟩, _⟩, hne⟩ => ⟨hP, ?_, ?_⟩
        · rw [hX, hP.2.1] at hlt; exact hlt
        · rintro ⟨_, hk⟩; apply hne; rw [hY, hP.2.2, hk]
    · refine (hemit.pre fun c ⟨⟨⟨⟨hP, hX⟩, hlt⟩, _⟩, h0⟩ => ⟨hP, ?_, ?_⟩).weaken (by omega)
      · rw [hX, hP.2.1] at hlt; exact hlt
      · rintro ⟨ha, _⟩; apply h0; rw [hP.1.2.2.2, ha]
  have hU : HTB S .skip (fun c => ((PcInv g k i a b c ∧ c.reg sB = b ∧ c.reg gK = k) ∧
        c.reg sX = a + 1) ∧ c.reg sB ≤ c.reg sX)
      (fun c => PcInv g k i a (b + 1) c ∧ c.reg sB = b ∧ c.reg gK = k) 23 :=
    (hskip.pre fun c ⟨⟨hP, hX⟩, hle⟩ => ⟨hP, fun ⟨hlt, _⟩ => by rw [hX, hP.2.1] at hle; omega⟩).weaken
      (by omega)
  exact (h1.seq (HTB.ifLt (show sX ≠ rT by decide) (show sB ≠ rT by decide)
    (by indep [PcInv, GState, gG_iff, gA_iff]) hS hU)).weaken (by omega)

/-- The state before the pairs of cycle `i` with first position `a`. -/
def MInv (g : Graph) (k i a : ℕ) (c : Config) : Prop :=
  GState g k (cntF g k 0) (pcI k i ++ pcA k i a) c ∧ c.reg sBase = i * k ∧ c.reg sI = i

/-- The state before cycle `i`. -/
def OInv (g : Graph) (k i : ℕ) (c : Config) : Prop :=
  GState g k (cntF g k 0) (pcI k i) c ∧ c.reg sBase = i * k

theorem pcRowA_spec (g : Graph) (k i a : ℕ)
    (hSp : bCL g k + (TwoSat.codes (pcI k i ++ pcA k i (a + 1))).length ≤ S) :
    HTB S pcRowA (fun c => MInv g k i a c ∧ c.reg sA = a ∧ c.reg gK = k)
      (fun c => MInv g k i (a + 1) c ∧ c.reg sA = a ∧ c.reg gK = k) (k * 65 + 3) := by
  have hl := HTB.forUpC (i := sB) (n := gK) (N := k) (body := pcBody) (PcInv g k i a) 61
    (by decide) (by decide) (by decide) (fun j => by indep [PcInv, GState, gG_iff, gA_iff])
    (fun b hb => pcBody_spec (S := S) g k i a b (by
      have := length_codes_pcB_le k i a (show b + 1 ≤ k by omega)
      simp only [codes_append, List.length_append, pcA_succ] at hSp ⊢; omega))
  refine hl.mono (fun c ⟨⟨hS, hB, hI⟩, hA, hK⟩ => ⟨⟨by simpa [pcB] using hS, hB, hI, hA⟩, hK⟩)
    (fun c ⟨⟨hS, hB, hI, hA⟩, _, hK⟩ => ⟨⟨?_, hB, hI⟩, hA, hK⟩) (by omega)
  rw [pcA_succ, ← List.append_assoc]; exact hS

theorem pcRow_spec (g : Graph) (k i : ℕ)
    (hSp : bCL g k + (TwoSat.codes (pcI k (i + 1))).length ≤ S) :
    HTB S pcRow (fun c => OInv g k i c ∧ c.reg sI = i ∧ c.reg gT = (cycles g k).length)
      (fun c => OInv g k (i + 1) c ∧ c.reg sI = i ∧ c.reg gT = (cycles g k).length)
      (k * (k * 65 + 7) + 4) := by
  have hl := HTB.forUpC (i := sA) (n := gK) (N := k) (body := pcRowA) (MInv g k i) (k * 65 + 3)
    (by decide) (by decide) (by decide) (fun j => by indep [MInv, GState, gG_iff, gA_iff])
    (fun a ha => pcRowA_spec (S := S) g k i a (by
      have := length_codes_pcA_le k i (show a + 1 ≤ k by omega)
      simp only [codes_append, List.length_append, pcI_succ] at hSp ⊢; omega))
  have h2 : HTB S (.add sBase sBase gK) (fun c => MInv g k i k c ∧ c.reg sA = k ∧ c.reg gK = k)
      (fun c => OInv g k (i + 1) c ∧ c.reg sI = i ∧ c.reg gT = (cycles g k).length) 1 :=
      HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨hS, hB, hI⟩, _, hK⟩ => ?_
    have hS' : GState g k (cntF g k 0) (pcI k (i + 1)) c := by rw [pcI_succ]; exact hS
    refine ⟨⟨(show Indep [sBase] (GState g k (cntF g k 0) (pcI k (i + 1))) by
      indep [GState, gG_iff, gA_iff]).setReg (by decide) _ hS', ?_⟩, ?_, ?_⟩
    · simp +decide [hB, hK]; ring
    · simp +decide [hI]
    · simp +decide [hS.1.ga.rt]
  refine (hl.seq h2).mono (fun c ⟨⟨hS, hB⟩, hI, _⟩ => ⟨⟨by simpa [pcA] using hS, hB, hI⟩, hS.1.ga.rk⟩)
    (fun _ h => h) (by ring_nf; omega)

/-- The state after phase 6. -/
def PcPost (g : Graph) (k : ℕ) (c : Config) : Prop := GState g k (cntF g k 0) (pathConstraints g k) c

/-- **Phase 6**: the path constraints. -/
theorem stepPc_spec (g : Graph) (k : ℕ)
    (hSp : bCL g k + (TwoSat.codes (pathConstraints g k)).length ≤ S) :
    HTB S stepPc (OffPost g k) (PcPost g k) ((cycles g k).length * (k * (k * 65 + 7) + 8) + 7) := by
  have h0 : HTB S (.seq (.seq (mov gCL rFREE) (.const gNC 0)) (.const sBase 0)) (OffPost g k)
      (fun c => OInv g k 0 c ∧ c.reg gT = (cycles g k).length) 4 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c hP => ?_
    have hga : GA g k (run (.seq (.seq (mov gCL rFREE) (.const gNC 0)) (.const sBase 0)) c) :=
      (show RegIndep [rT, gCL, gNC, sBase] (GA g k) by indep [gA_iff]).run_of_sub
        (by decide) (by decide) hP.ga
    refine ⟨⟨⟨⟨hga, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    all_goals simp +decide only [run_seq', run_mov (show rFREE ≠ rT by decide), run_const, setReg_reg,
      setReg_mem, setReg_out, ↓reduceIte, hP.reid, hP.rcnt, hP.roff, hP.rseen, hP.rfree, hP.rout,
      hP.ga.rt]
    · simp [pcI, TwoSat.codes]
    · simp [pcI]
    · refine ⟨hP.mverts, hP.meid, hP.mcnt, hP.moff, hP.mseen, by simp [pcI, TwoSat.codes], ?_⟩
      simpa [pcI, TwoSat.codes] using hP.mzero
    · simp
  have hl := HTB.forUpC (i := sI) (n := gT) (N := (cycles g k).length) (body := pcRow) (OInv g k)
    (k * (k * 65 + 7) + 4) (by decide) (by decide) (by decide)
    (fun j => by indep [OInv, GState, gG_iff, gA_iff]) (fun i hi => pcRow_spec (S := S) g k i (by
      have := length_codes_pcI_le k (show i + 1 ≤ (cycles g k).length by omega)
      rw [pcI_full] at this; omega))
  refine HTB.assoc (HTB.assoc ((h0.seq hl).mono (fun _ h => h) (fun c ⟨⟨hS, _⟩, _, _⟩ => ?_)
    (le_of_eq (by ring))))
  rw [PcPost, ← pcI_full]; exact hS

/-! ### Phase 7: the prefix clauses -/

/-- The clauses of the first `q` occurrences. -/
def occPre (g : Graph) (k q : ℕ) : CNF := (List.range q).flatMap (occCl g k)

theorem occPre_succ (g : Graph) (k q : ℕ) : occPre g k (q + 1) = occPre g k q ++ occCl g k q := by
  simp [occPre, List.range_succ, List.flatMap_append]

theorem length_codes_occPre_le (g : Graph) (k : ℕ) {q q' : ℕ} (h : q ≤ q') :
    (TwoSat.codes (occPre g k q)).length ≤ (TwoSat.codes (occPre g k q')).length := by
  induction q', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => rw [occPre_succ, codes_append, List.length_append]; omega

/-- The registers of an occurrence: `sQ = q`, `sE = e`, `sR = x`, `sP = p`, `sS = o + x`,
`sX = x + 1`. -/
def ORegs (q e x p o : ℕ) (c : Config) : Prop :=
  c.reg sQ = q ∧ c.reg sE = e ∧ c.reg sR = x ∧ c.reg sP = p ∧ c.reg sS = o + x ∧ c.reg sX = x + 1

/-- The state inside the body for occurrence `q` (with the registers `ORegs`). -/
def OSt (g : Graph) (k : ℕ) (s : ℕ → ℕ) (F : CNF) (q e x p o : ℕ) (c : Config) : Prop :=
  GState g k s F c ∧ ORegs q e x p o c ∧ c.reg gKT = k * (cycles g k).length

theorem oSt_indep (g : Graph) (k : ℕ) (s : ℕ → ℕ) (F : CNF) (q e x p o : ℕ) :
    Indep [rT] (OSt g k s F q e x p o) := by indep [OSt, ORegs, GState, gG_iff, gA_iff]

/-- Emitting a clause keeps the occurrence registers. -/
theorem emit_regs {c c' : Config} {q e x p o : ℕ}
    (h : ∀ r, r ∉ [sU, sV, rT, rFREE, gNC] → c'.reg r = c.reg r) (hO : ORegs q e x p o c)
    (hK : c.reg gKT = K) : ORegs q e x p o c' ∧ c'.reg gKT = K := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hO
  exact ⟨⟨by rw [h sQ (by decide), h1], by rw [h sE (by decide), h2], by rw [h sR (by decide), h3],
    by rw [h sP (by decide), h4], by rw [h sS (by decide), h5], by rw [h sX (by decide), h6]⟩,
    by rw [h gKT (by decide), hK]⟩

theorem frame_of_wregs {s : Stmt} (hs : LoopFree s) (W : List ℕ) (hW : ∀ r ∈ wregs s, r ∈ W)
    (c : Config) : ∀ r, r ∉ W → (run s c).reg r = c.reg r :=
  fun r hr => run_reg_of_not_mem hs (fun h => hr (hW r h)) c

theorem emit1_spec (g : Graph) (k : ℕ) (s : ℕ → ℕ) (F : CNF) (q e x p o : ℕ)
    (hSp : bCL g k + (TwoSat.codes (F ++ [[⟨q, true⟩, ⟨o + x, true⟩]])).length ≤ S) :
    HTB S emit1 (OSt g k s F q e x p o)
      (OSt g k s (F ++ [[⟨q, true⟩, ⟨o + x, true⟩]]) q e x p o) 10 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hS, hO, hK⟩ => ?_
  have hfr := frame_of_wregs (s := emit1) (by decide) [sU, sV, rT, rFREE, gNC] (by decide) c
  refine ⟨by have := hS.room hSp; addr_ok [emit1, push],
    hS.emit _ _ (fun r hr => hfr r (not_mem_of_sub hr (by decide))) ?_ ?_ ?_ ?_,
    emit_regs hfr hO hK⟩
  · simp +decide [emit1, run_push, run_inc]
  · simp +decide [emit1, run_push, run_inc]
  · simp +decide only [emit1, run_seq', run_add,
      run_inc (show gNC ≠ rT by decide), run_push, setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd,
      ↓reduceIte, hO.1, hO.2.2.2.2.1, code_pos]
  · simp [emit1, run_push, run_inc]

theorem emit2_spec (g : Graph) (k : ℕ) (s : ℕ → ℕ) (F : CNF) (q e x p o : ℕ) (hx : 0 < x)
    (hSp : bCL g k + (TwoSat.codes (F ++ [[⟨o + (x - 1), false⟩, ⟨o + x, true⟩]])).length ≤ S) :
    HTB S emit2 (OSt g k s F q e x p o)
      (OSt g k s (F ++ [[⟨o + (x - 1), false⟩, ⟨o + x, true⟩]]) q e x p o) 14 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hS, hO, hK⟩ => ?_
  have hfr := frame_of_wregs (s := emit2) (by decide) [sU, sV, rT, rFREE, gNC] (by decide) c
  have hs1 : o + x - 1 = o + (x - 1) := by omega
  refine ⟨by have := hS.room hSp; addr_ok [emit2, push],
    hS.emit _ _ (fun r hr => hfr r (not_mem_of_sub hr (by decide))) ?_ ?_ ?_ ?_,
    emit_regs hfr hO hK⟩
  · simp +decide [emit2, run_push, run_inc, run_subc]
  · simp +decide [emit2, run_push, run_inc, run_subc]
  · simp +decide only [emit2, run_seq', run_add, run_subc (show sS ≠ rT by decide),
      run_inc (show sU ≠ rT by decide), run_inc (show gNC ≠ rT by decide), run_push, setReg_reg,
      setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte, hO.2.2.2.2.1, code_pos, code_neg, hs1]
  · simp [emit2, run_push, run_inc, run_subc]

theorem emit3_spec (g : Graph) (k : ℕ) (s : ℕ → ℕ) (F : CNF) (q e x p o : ℕ) (hx : 0 < x)
    (hSp : bCL g k + (TwoSat.codes (F ++ [[⟨q, true⟩, ⟨o + (x - 1), false⟩]])).length ≤ S) :
    HTB S emit3 (OSt g k s F q e x p o)
      (OSt g k s (F ++ [[⟨q, true⟩, ⟨o + (x - 1), false⟩]]) q e x p o) 14 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hS, hO, hK⟩ => ?_
  have hfr := frame_of_wregs (s := emit3) (by decide) [sU, sV, rT, rFREE, gNC] (by decide) c
  have hs1 : o + x - 1 = o + (x - 1) := by omega
  refine ⟨by have := hS.room hSp; addr_ok [emit3, push],
    hS.emit _ _ (fun r hr => hfr r (not_mem_of_sub hr (by decide))) ?_ ?_ ?_ ?_,
    emit_regs hfr hO hK⟩
  · simp +decide [emit3, run_push, run_inc, run_subc]
  · simp +decide [emit3, run_push, run_inc, run_subc]
  · simp +decide only [emit3, run_seq', run_add, run_subc (show sS ≠ rT by decide),
      run_inc (show sV ≠ rT by decide), run_inc (show gNC ≠ rT by decide), run_push, setReg_reg,
      setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte, hO.1, hO.2.2.2.2.1, code_pos, code_neg, hs1]
  · simp [emit3, run_push, run_inc, run_subc]

/-- A pure fact read off the precondition. -/
theorem HT.pre_fact {s : Stmt} {P Q : Config → Prop} {b : ℕ} {p : Prop} (hp : ∀ c, P c → p)
    (h : p → HT s P Q b) : HT s P Q b := fun c hc => h (hp c hc) c hc

/-- The three conditional clauses of an occurrence. -/
theorem occEmit_spec (g : Graph) (k : ℕ) (s : ℕ → ℕ) (F : CNF) (q e x p o : ℕ)
    (hSp : bCL g k + (TwoSat.codes (F ++ occClOf q x p o)).length ≤ S) :
    HTB S occEmit (OSt g k s F q e x p o) (OSt g k s (F ++ occClOf q x p o) q e x p o) 48 := by
  have hskip : ∀ F', HTB S .skip (OSt g k s F' q e x p o) (OSt g k s (F' ++ []) q e x p o) 1 :=
    fun F' => HTB.run_le (by decide) le_rfl fun c h => ⟨trivial, by rw [List.append_nil]; exact h⟩
  set p1 : CNF := if x + 1 < p then [[⟨q, true⟩, ⟨o + x, true⟩]] else []
  set p2 : CNF := if 0 < x ∧ x + 1 < p then [[⟨o + (x - 1), false⟩, ⟨o + x, true⟩]] else []
  set p3 : CNF := if 0 < x then [[⟨q, true⟩, ⟨o + (x - 1), false⟩]] else []
  have hocc : occClOf q x p o = p1 ++ (p2 ++ p3) := rfl
  rw [hocc] at hSp
  simp only [codes_append, List.length_append] at hSp
  -- part 1
  have h1 : HTB S (ifLt sX sP emit1 .skip) (OSt g k s F q e x p o)
      (OSt g k s (F ++ p1) q e x p o) 12 := by
    refine HTB.ifLt (B := 10) (show sX ≠ rT by decide) (show sP ≠ rT by decide)
      (oSt_indep g k s F q e x p o) ?_ ?_
    · refine HTB.pre_fact (p := x + 1 < p) (fun c ⟨⟨_, hO, _⟩, hlt⟩ => ?_) fun hc => ?_
      · rw [hO.2.2.2.2.2, hO.2.2.2.1] at hlt; exact hlt
      · have hp1 : p1 = [[⟨q, true⟩, ⟨o + x, true⟩]] := by simp only [p1]; rw [ite_eq_left hc]
        refine (emit1_spec g k s F q e x p o (by
          rw [codes_append, List.length_append, ← hp1]; omega)).mono (fun c h => h.1)
          (fun c h => ?_) le_rfl
        rw [hp1]; exact h
    · refine HTB.pre_fact (p := ¬ x + 1 < p) (fun c ⟨⟨_, hO, _⟩, hle⟩ => ?_) fun hc => ?_
      · rw [hO.2.2.2.2.2, hO.2.2.2.1] at hle; omega
      · refine ((hskip F).mono (fun c h => h.1) (fun c h => ?_) le_rfl).weaken (by omega)
        simp only [p1]; rw [ite_eq_right hc]; exact h
  -- part 2
  have h2 : ∀ F', bCL g k + (TwoSat.codes (F' ++ p2)).length ≤ S →
      HTB S (.ifz sR .skip (ifLt sX sP emit2 .skip)) (OSt g k s F' q e x p o)
      (OSt g k s (F' ++ p2) q e x p o) 17 := by
    intro F' hF'
    refine HTB.ifz (b := 16) ?_ ?_
    · refine HTB.pre_fact (p := x = 0) (fun c ⟨⟨_, hO, _⟩, h0⟩ => by rw [← hO.2.2.1, h0]) fun hc => ?_
      refine ((hskip F').mono (fun c h => h.1) (fun c h => ?_) le_rfl).weaken (by omega)
      simp only [p2]; rw [ite_eq_right (by omega)]; exact h
    · refine HTB.pre_fact (p := 0 < x) (fun c ⟨⟨_, hO, _⟩, h0⟩ => by rw [hO.2.2.1] at h0; omega)
        fun hx => ?_
      refine HTB.ifLt (B := 14) (show sX ≠ rT by decide) (show sP ≠ rT by decide)
        (by indep [OSt, ORegs, GState, gG_iff, gA_iff]) ?_ ?_
      · refine HTB.pre_fact (p := x + 1 < p) (fun c ⟨⟨⟨_, hO, _⟩, _⟩, hlt⟩ => ?_) fun hc => ?_
        · rw [hO.2.2.2.2.2, hO.2.2.2.1] at hlt; exact hlt
        · have hp2 : p2 = [[⟨o + (x - 1), false⟩, ⟨o + x, true⟩]] := by
            simp only [p2]; rw [ite_eq_left ⟨hx, hc⟩]
          refine (emit2_spec g k s F' q e x p o hx (by rw [← hp2]; exact hF')).mono (fun c h => h.1.1)
            (fun c h => ?_) le_rfl
          rw [hp2]; exact h
      · refine HTB.pre_fact (p := ¬ x + 1 < p) (fun c ⟨⟨⟨_, hO, _⟩, _⟩, hle⟩ => ?_) fun hc => ?_
        · rw [hO.2.2.2.2.2, hO.2.2.2.1] at hle; omega
        · refine ((hskip F').mono (fun c h => h.1.1) (fun c h => ?_) le_rfl).weaken (by omega)
          simp only [p2]; rw [ite_eq_right (fun h' => hc h'.2)]; exact h
  -- part 3
  have h3 : ∀ F', bCL g k + (TwoSat.codes (F' ++ p3)).length ≤ S →
      HTB S (.ifz sR .skip emit3) (OSt g k s F' q e x p o) (OSt g k s (F' ++ p3) q e x p o) 15 := by
    intro F' hF'
    refine HTB.ifz (b := 14) ?_ ?_
    · refine HTB.pre_fact (p := x = 0) (fun c ⟨⟨_, hO, _⟩, h0⟩ => by rw [← hO.2.2.1, h0]) fun hc => ?_
      refine ((hskip F').mono (fun c h => h.1) (fun c h => ?_) le_rfl).weaken (by omega)
      simp only [p3]; rw [ite_eq_right (by omega)]; exact h
    · refine HTB.pre_fact (p := 0 < x) (fun c ⟨⟨_, hO, _⟩, h0⟩ => by rw [hO.2.2.1] at h0; omega)
        fun hx => ?_
      have hp3 : p3 = [[⟨q, true⟩, ⟨o + (x - 1), false⟩]] := by simp only [p3]; rw [ite_eq_left hx]
      refine (emit3_spec g k s F' q e x p o hx (by rw [← hp3]; exact hF')).mono (fun c h => h.1)
        (fun c h => ?_) le_rfl
      rw [hp3]; exact h
  refine (h1.seq ((h2 _ ?_).seq (h3 _ ?_))).mono (fun _ h => h) (fun c h => ?_) (by omega)
  · simp only [codes_append, List.length_append]; omega
  · simp only [codes_append, List.length_append]; omega
  · rw [hocc]; simpa only [List.append_assoc] using h

/-- The state after `q` occurrences of phase 7. -/
def OccInv (g : Graph) (k q : ℕ) (c : Config) : Prop :=
  GState g k (cntF g k q) (pathConstraints g k ++ occPre g k q) c

theorem occRead_run {g : Graph} {k q : ℕ} {c : Config} (hq : q < k * (cycles g k).length)
    (hS : OccInv g k q c) (hQ : c.reg sQ = q) :
    ORegs q (eidOf g k q) (rank g k q) (cntF g k (k * (cycles g k).length) (eidOf g k q))
      (offF g k (eidOf g k q)) (run occRead c) ∧ Agree [sE, sR, sP, sO, sS, sX, rT] c (run occRead c) := by
  obtain ⟨hG, _, _, hM, _⟩ := hS
  have he := eidOf_lt hq
  have hne := nE_le g k
  have h1 : c.mem (bEID g k + q) = eidOf g k q := hM.meid.get hq
  have h2 : c.mem (bSEEN g k + eidOf g k q) = rank g k q := hM.mseen.get he
  have h3 : c.mem (bCNT g k + eidOf g k q) = cntF g k (k * (cycles g k).length) (eidOf g k q) :=
    hM.mcnt.get (by omega)
  have h4 : c.mem (bOFF g k + eidOf g k q) = offF g k (eidOf g k q) := hM.moff.get he
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, agree_run (by decide) rfl rfl (by decide) c⟩
  all_goals simp +decide only [occRead, run_seq', run_ld, run_add, run_addc (show sR ≠ rT by decide),
    setReg_reg, setReg_mem, ↓reduceIte, hQ, hG.reid, hG.rseen, hG.rcnt, hG.roff, h1, h2, h3, h4]

/-- The addresses of `occRead`: `EID + q`, then `SEEN`, `CNT`, `OFF` at the identifier. -/
theorem occRead_addrOK {g : Graph} {k q : ℕ} {c : Config} (hSp : bCL g k ≤ S)
    (hq : q < k * (cycles g k).length) (hS : OccInv g k q c) (hQ : c.reg sQ = q) :
    AddrOK S occRead c := by
  obtain ⟨hG, _, _, hM, _⟩ := hS
  have he := eidOf_lt hq
  have hne := nE_le g k
  have h1 : c.mem (bEID g k + q) = eidOf g k q := hM.meid.get hq
  have := fits g k hSp
  addr_ok [occRead, hQ, hG.reid, hG.rseen, hG.rcnt, hG.roff, h1]

theorem occBody_spec (g : Graph) (k q : ℕ) (hq : q < k * (cycles g k).length)
    (hSp : bCL g k + (TwoSat.codes (pathConstraints g k ++ occPre g k (q + 1))).length ≤ S) :
    HTB S occBody (fun c => OccInv g k q c ∧ c.reg sQ = q ∧ c.reg gKT = k * (cycles g k).length)
      (fun c => OccInv g k (q + 1) c ∧ c.reg sQ = q ∧ c.reg gKT = k * (cycles g k).length) 61 := by
  set e := eidOf g k q
  set x := rank g k q
  set p := cntF g k (k * (cycles g k).length) e
  set o := offF g k e
  have he := eidOf_lt hq
  have hl : pathConstraints g k ++ occPre g k (q + 1) =
      pathConstraints g k ++ occPre g k q ++ occClOf q x p o := by
    simp [occPre, List.range_succ, List.flatMap_append, occCl, x, p, o, e]
  have hSp' : bCL g k ≤ S := le_trans (Nat.le_add_right _ _) hSp
  have h1 : HTB S occRead (fun c => OccInv g k q c ∧ c.reg sQ = q ∧ c.reg gKT = k * (cycles g k).length)
      (OSt g k (cntF g k q) (pathConstraints g k ++ occPre g k q) q e x p o) 11 :=
    HTB.run_le (by decide) (by decide) fun c ⟨hS, hQ, hK⟩ => by
      obtain ⟨hR, ha⟩ := occRead_run hq hS hQ
      exact ⟨occRead_addrOK hSp' hq hS hQ, (show Indep [sE, sR, sP, sO, sS, sX, rT] (OccInv g k q) by
        indep [OccInv, GState, gG_iff, gA_iff]) c _ ha hS, hR, by rw [ha.reg gKT (by decide), hK]⟩
  have h3 : HTB S (st gSEEN sE sX) (OSt g k (cntF g k q) (pathConstraints g k ++ occPre g k q ++
        occClOf q x p o) q e x p o)
      (fun c => OccInv g k (q + 1) c ∧ c.reg sQ = q ∧ c.reg gKT = k * (cycles g k).length) 2 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hfr, hn, hM, ho⟩, hO, hK⟩ => ?_
    have hs : cntF g k (q + 1) = Function.update (cntF g k q) e (x + 1) := cntF_succ q
    refine ⟨by
      have := fits g k hSp'
      have hne := nE_le g k
      addr_ok [hG.rseen, hO.2.1], ?_⟩
    rw [run_st (show sX ≠ rT by decide)]
    refine ⟨?_, ?_, ?_⟩
    · unfold OccInv
      rw [hl, hs]
      refine ⟨(GG.regIndep g k).setReg (by decide) _ ((GG.regIndep g k).setMem _ _ hG), ?_, ?_, ?_, ?_⟩
      · simp +decide [hfr]
      · simp +decide [hn]
      · simp only [setReg_mem, setMem_mem_upd, hG.rseen, hO.2.1, hO.2.2.2.2.2]
        exact hM.seen he _
      · simp [ho]
    · simp +decide [hO.1]
    · simp +decide [hK]
  exact (h1.seq ((occEmit_spec g k _ _ q e x p o (by rw [← hl]; exact hSp)).seq h3)).weaken
    (by omega)

/-- **Phase 7**: the prefix clauses; afterwards the codes of `zcf g k` are at `bCL g k`. -/
theorem stepOcc_spec (g : Graph) (k : ℕ) (hSp : bCL g k + (TwoSat.codes (zcf g k)).length ≤ S) :
    HTB S stepOcc (PcPost g k)
      (fun c => GState g k (cntF g k (k * (cycles g k).length)) (zcf g k) c)
      (k * (cycles g k).length * 65 + 3) := by
  have hl := HTB.forUpC (i := sQ) (n := gKT) (N := k * (cycles g k).length) (body := occBody)
    (OccInv g k) 61 (by decide) (by decide) (by decide)
    (fun j => by indep [OccInv, GState, gG_iff, gA_iff]) (fun q hq => occBody_spec (S := S) g k q hq (by
      have := length_codes_occPre_le g k (show q + 1 ≤ k * (cycles g k).length by omega)
      have hz : zcf g k = pathConstraints g k ++ occPre g k (k * (cycles g k).length) := rfl
      rw [hz, codes_append, List.length_append] at hSp
      rw [codes_append, List.length_append]; omega))
  refine hl.mono (fun c h => ⟨?_, h.1.ga.rkt⟩) (fun c h => ?_) (by omega)
  · unfold OccInv; simpa [occPre, PcPost] using h
  · exact h.1
