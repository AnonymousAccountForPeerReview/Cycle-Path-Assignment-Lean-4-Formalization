module

public import Runtimes.ZeroCostGen
import Mathlib.Tactic

/-!
# Corollary 5 on the RAM: the recovery of the omitted positions

Phase 9 of `zeroCostProg` (`stepRec_spec`), within any space bound `S` above the input
(`bD g k ≤ S`) and the assignment (`A + kt ≤ S`). The memory `m` and the address `A` of the 2-SAT
assignment are fixed; `σ x = (m (A + x) = 1)` is the assignment. If `tOK = 0` the machine
writes `0`. Otherwise it writes `1` and, for each cycle `i < t`, the first position `i₀ < k`
passing the test `posOk g k σ i i₀` (every edge of `C_i` whose variable is true is incident to
the vertex at `i₀`), or `0` if there is none: the output is `1 :: (range t).map (recPos g k σ)`,
which is `omittedPosition g k σ` of Algorithm 3 (`omittedPosition_eq`). The test of one position
costs `O(k)`, so the phase costs `O(k²t)`.
-/

@[expose] public section

namespace STACS2027.Runtimes.ZeroCost

open STACS2027 STACS2027.RAM STACS2027.RAM.R0 Complexity.SAT

variable {S : ℕ}

/-- The position written for cycle `i`: the first position passing the test (`0` if none). -/
def recPos (g : Graph) (k : ℕ) (σ : Assignment) (i : ℕ) : ℕ :=
  ((List.range k).find? (posOk g k σ i)).getD 0

/-- The assignment read from memory `m` at `A`. -/
def memAsg (m : ℕ → ℕ) (A : ℕ) : Assignment := fun x => decide (m (A + x) = 1)

/-- The fixed part of the recovery state. -/
def RG (g : Graph) (k : ℕ) (m : ℕ → ℕ) (A : ℕ) (c : Config) : Prop :=
  GA g k c ∧ c.mem = m ∧ c.reg TwoSat.tAS = A

/-- The term of position `j` in the test of position `a` of cycle `i`. -/
def testTerm (g : Graph) (k : ℕ) (σ : Assignment) (i a j : ℕ) : Bool :=
  !σ (i * k + j) || ((verts g k).getD (i * k + j) 0 == (verts g k).getD (i * k + a) 0 ||
    (verts g k).getD (i * k + next k j) 0 == (verts g k).getD (i * k + a) 0)

/-- The state after `j` positions of the test of position `a` of cycle `i`. -/
def RJ (g : Graph) (k : ℕ) (m : ℕ → ℕ) (A : ℕ) (O : List ℕ) (fd res i a j : ℕ) (c : Config) : Prop :=
  RG g k m A c ∧ c.reg sBase = i * k ∧ c.reg sI = i ∧ c.reg sA = a ∧
    c.reg sC = (verts g k).getD (i * k + a) 0 ∧
    c.reg sOk = (if (List.range j).all (testTerm g k (memAsg m A) i a) then 1 else 0) ∧
    c.reg sF = fd ∧ c.reg sRes = res ∧ c.out = O

theorem recCheck_run {c : Config} {base j k : ℕ} (hJ : c.reg sJ = j) (hK : c.reg gK = k)
    (hQ : c.reg sQ = base + j) (hB : c.reg sBase = base) :
    (run recCheck c).reg sOk = (if c.mem (c.reg gV + (base + j)) = c.reg sC ∨
      c.mem (c.reg gV + (base + next k j)) = c.reg sC then c.reg sOk else 0) ∧
      Agree [sX, sP, sY, sOk, rT] c (run recCheck c) := by
  refine ⟨?_, agree_run (by decide) rfl rfl (by decide) c⟩
  obtain ⟨hp, ap⟩ := nextPos_run (c := run (ld sX gV sQ) c) (base := base) (j := j) (k := k)
    (by simp +decide [hJ]) (by simp +decide [hK]) (by simp +decide [hQ]) (by simp +decide [hB])
  have hx : (run nextPos (run (ld sX gV sQ) c)).reg sX = c.mem (c.reg gV + (base + j)) := by
    rw [ap.reg sX (by decide)]; simp [hQ]
  have hgv : (run nextPos (run (ld sX gV sQ) c)).reg gV = c.reg gV := by
    rw [ap.reg gV (by decide)]; simp
  have hsc : (run nextPos (run (ld sX gV sQ) c)).reg sC = c.reg sC := by
    rw [ap.reg sC (by decide)]; simp
  have hok : (run nextPos (run (ld sX gV sQ) c)).reg sOk = c.reg sOk := by
    rw [ap.reg sOk (by decide)]; simp
  have hm : (run nextPos (run (ld sX gV sQ) c)).mem = c.mem := by rw [ap.mem]; simp
  show (run (.seq (ld sY gV sP) (ifEq sX sC .skip (ifEq sY sC .skip (.const sOk 0))))
    (run nextPos (run (ld sX gV sQ) c))).reg sOk = _
  generalize run nextPos (run (ld sX gV sQ) c) = c' at hp hx hgv hsc hok hm
  simp only [run_seq', run_ld, run_ifEq (show sX ≠ rT by decide) (show sC ≠ rT by decide),
    run_ifEq (show sY ≠ rT by decide) (show sC ≠ rT by decide), run_skip, run_const]
  simp +decide only [setReg_reg, ↓reduceIte, hx, hp, hgv, hsc, hm]
  by_cases h1 : c.mem (c.reg gV + (base + j)) = c.reg sC
  · simp [h1, hok]
  · by_cases h2 : c.mem (c.reg gV + (base + next k j)) = c.reg sC
    · simp [h1, h2, hok]
    · simp [h1, h2]

/-- The addresses of `recCheck`: the two ends of the edge in the cycle part of the input. -/
theorem recCheck_addrOK {c : Config} {base j k : ℕ} (hJ : c.reg sJ = j) (hK : c.reg gK = k)
    (hQ : c.reg sQ = base + j) (hB : c.reg sBase = base) (h1 : c.reg gV + (base + j) < S)
    (h2 : c.reg gV + (base + next k j) < S) : AddrOK S recCheck c := by
  obtain ⟨hp, ap⟩ := nextPos_run (c := run (ld sX gV sQ) c) (base := base) (j := j) (k := k)
    (by simp +decide [hJ]) (by simp +decide [hK]) (by simp +decide [hQ]) (by simp +decide [hB])
  refine AddrOK.seq (by rw [addrOK_ld, hQ]; exact h1) (AddrOK.seq (AddrOK.of_memFree rfl)
    (AddrOK.seq ?_ (AddrOK.of_memFree rfl)))
  rw [addrOK_ld, ap.reg gV (by decide), hp]
  simpa using h2

theorem recBody_spec (g : Graph) (k : ℕ) (m : ℕ → ℕ) (A : ℕ) (O : List ℕ) (fd res i a j : ℕ)
    (hi : i < (cycles g k).length) (hj : j < k) (hV : Arr m (bV g) (verts g k))
    (hbits : ∀ x < k * (cycles g k).length, m (A + x) ≤ 1) (hSV : bD g k ≤ S)
    (hSA : A + k * (cycles g k).length ≤ S) :
    HTB S recBody (fun c => RJ g k m A O fd res i a j c ∧ c.reg sJ = j ∧ c.reg gK = k)
      (fun c => RJ g k m A O fd res i a (j + 1) c ∧ c.reg sJ = j ∧ c.reg gK = k) 36 := by
  refine HTB.run_le (by decide) (by decide)
    fun c ⟨⟨⟨hga, hm, hA⟩, hB, hI, hAa, hC, hOk, hF, hR, ho⟩, hJ, hK⟩ => ⟨?_, ?_⟩
  · have hq := occ_lt hi hj
    have hq2 : i * k + next k j < k * (cycles g k).length := occ_lt hi (next_lt (by omega))
    have hb : bD g k = bV g + k * (cycles g k).length := rfl
    refine AddrOK.seq (AddrOK.of_memFree rfl) (AddrOK.seq (by addr_ok [hA, hB, hJ])
      (AddrOK.ifz (fun _ => trivial) (fun _ => recCheck_addrOK (base := i * k) (j := j) (k := k)
        (by simp +decide [hJ]) (by simp +decide [hK]) (by simp +decide [hB, hJ])
        (by simp +decide [hB]) (by simp +decide [hga.rv]; omega) (by simp +decide [hga.rv]; omega))))
  have hq := occ_lt hi hj
  have hq2 : i * k + next k j < k * (cycles g k).length := occ_lt hi (next_lt (by omega))
  have hag : Agree [sQ, sZ, sX, sP, sY, sOk, rT] c (run recBody c) := agree_run (by decide) rfl rfl (by decide) c
  have hxv : m (bV g + (i * k + j)) = (verts g k).getD (i * k + j) 0 :=
    hV.getD (by rw [length_verts]; exact hq)
  have hyv : m (bV g + (i * k + next k j)) = (verts g k).getD (i * k + next k j) 0 :=
    hV.getD (by rw [length_verts]; exact hq2)
  have hok' : (run recBody c).reg sOk =
      (if (List.range (j + 1)).all (testTerm g k (memAsg m A) i a) then 1 else 0) := by
    rw [all_range_succ]
    generalize (List.range j).all (testTerm g k (memAsg m A) i a) = b at hOk
    set c1 := run (.add sQ sBase sJ) c
    have h1q : c1.reg sQ = i * k + j := by simp +decide [c1, hB, hJ]
    set c2 := run (ld sZ TwoSat.tAS sQ) c1
    have h2z : c2.reg sZ = m (A + (i * k + j)) := by
      simp +decide [c2, c1, hB, hJ, hA, hm]
    have h2q : c2.reg sQ = i * k + j := by simp +decide [c2, h1q]
    have a12 : Agree [sQ, sZ, rT] c c2 := (agree_run (s := .add sQ sBase sJ) (by decide) rfl rfl
      (by decide) c).trans (agree_run (s := ld sZ TwoSat.tAS sQ) (by decide) rfl rfl (by decide) c1)
    show (run (.ifz sZ .skip recCheck) c2).reg sOk = _
    have hbit := hbits (i * k + j) hq
    simp only [run_ifz', h2z]
    by_cases hz : m (A + (i * k + j)) = 0
    · have hT : testTerm g k (memAsg m A) i a j = true := by simp [testTerm, memAsg, hz]
      simp only [hz, ↓reduceIte, run_skip, hT, Bool.and_true]
      rw [a12.reg sOk (by decide), hOk]
    · have h1 : m (A + (i * k + j)) = 1 := by omega
      simp only [hz, ↓reduceIte]
      obtain ⟨hr, _⟩ := recCheck_run (c := c2) (base := i * k) (j := j) (k := k)
        (by rw [a12.reg sJ (by decide), hJ]) (by rw [a12.reg gK (by decide), hK]) h2q
        (by rw [a12.reg sBase (by decide), hB])
      rw [hr, a12.reg gV (by decide), a12.reg sC (by decide), a12.reg sOk (by decide), a12.mem, hga.rv,
        hm, hxv, hyv, hC, hOk]
      have hT : testTerm g k (memAsg m A) i a j =
          ((verts g k).getD (i * k + j) 0 == (verts g k).getD (i * k + a) 0 ||
            (verts g k).getD (i * k + next k j) 0 == (verts g k).getD (i * k + a) 0) := by
        simp only [testTerm, memAsg, h1, decide_true, Bool.not_true, Bool.false_or]
      rw [hT]
      generalize (verts g k).getD (i * k + j) 0 = x
      generalize (verts g k).getD (i * k + next k j) 0 = y
      generalize (verts g k).getD (i * k + a) 0 = z
      by_cases ht1 : x = z <;> by_cases ht2 : y = z <;> cases b <;> simp [ht1, ht2]
  refine ⟨⟨⟨(show RegIndep [sQ, sZ, sX, sP, sY, sOk, rT] (GA g k) by indep [gA_iff]).indep c _ hag hga,
    by rw [hag.mem, hm], by rw [hag.reg _ (by decide), hA]⟩, ?_, ?_, ?_, ?_, hok', ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals first
    | (rw [hag.out]; exact ho)
    | (rwa [hag.reg _ (by decide)])

/-- The state before the test of position `a` of cycle `i`. -/
def RA (g : Graph) (k : ℕ) (m : ℕ → ℕ) (A : ℕ) (O : List ℕ) (i a : ℕ) (c : Config) : Prop :=
  RG g k m A c ∧ c.reg sBase = i * k ∧ c.reg sI = i ∧
    c.reg sF = (if ((List.range a).find? (posOk g k (memAsg m A) i)).isSome then 1 else 0) ∧
    c.reg sRes = ((List.range a).find? (posOk g k (memAsg m A) i)).getD 0 ∧ c.out = O

theorem recUpd_spec (g : Graph) (k : ℕ) (m : ℕ → ℕ) (A : ℕ) (O : List ℕ) (i a : ℕ) :
    HTB S recUpd (fun c => RJ g k m A O
        (if ((List.range a).find? (posOk g k (memAsg m A) i)).isSome then 1 else 0)
        (((List.range a).find? (posOk g k (memAsg m A) i)).getD 0) i a k c ∧ c.reg sJ = k ∧ c.reg gK = k)
      (fun c => RA g k m A O i (a + 1) c ∧ c.reg sA = a ∧ c.reg gK = k) 7 := HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hG, hB, hI, hAa, _, hOk, hF, hR, ho⟩, _, hK⟩ => ?_
  have hag : Agree [sRes, sF, rT] c (run recUpd c) := agree_run (by decide) rfl rfl (by decide) c
  have hpos : (List.range k).all (testTerm g k (memAsg m A) i a) = posOk g k (memAsg m A) i a := rfl
  rw [hpos] at hOk
  have hG' : RG g k m A (run recUpd c) :=
    (show Indep [sRes, sF, rT] (RG g k m A) by indep [RG, gA_iff]) c _ hag hG
  refine ⟨⟨hG', by rw [hag.reg sBase (by decide), hB], by rw [hag.reg sI (by decide), hI], ?_, ?_,
    by rw [hag.out, ho]⟩, by rw [hag.reg sA (by decide), hAa], by rw [hag.reg gK (by decide), hK]⟩
  all_goals
    rw [find?_range_succ]
    simp only [recUpd, run_ifz', run_skip, run_seq', run_mov (show sA ≠ rT by decide), run_const]
    cases hfd : (List.range a).find? (posOk g k (memAsg m A) i) with
    | some r =>
      simp only [hfd, Option.isSome_some, ↓reduceIte] at hF hR
      simp [hF, hR]
    | none =>
      simp only [hfd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.getD_none] at hF hR
      cases hp : posOk g k (memAsg m A) i a
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hOk
        simp [hF, hOk, hR]
      · simp only [hp, ↓reduceIte] at hOk
        simp +decide [hF, hOk, hAa]

theorem recA_spec (g : Graph) (k : ℕ) (m : ℕ → ℕ) (A : ℕ) (O : List ℕ) (i a : ℕ)
    (hi : i < (cycles g k).length) (ha : a < k) (hV : Arr m (bV g) (verts g k))
    (hbits : ∀ x < k * (cycles g k).length, m (A + x) ≤ 1) (hSV : bD g k ≤ S)
    (hSA : A + k * (cycles g k).length ≤ S) :
    HTB S recA (fun c => RA g k m A O i a c ∧ c.reg sA = a ∧ c.reg gK = k)
      (fun c => RA g k m A O i (a + 1) c ∧ c.reg sA = a ∧ c.reg gK = k) (k * 40 + 14) := by
  set fd := if ((List.range a).find? (posOk g k (memAsg m A) i)).isSome then 1 else 0
  set res := ((List.range a).find? (posOk g k (memAsg m A) i)).getD 0
  have h0 : HTB S (.seq (.seq (.const sOk 1) (.add sQ sBase sA)) (ld sC gV sQ))
      (fun c => RA g k m A O i a c ∧ c.reg sA = a ∧ c.reg gK = k)
      (fun c => RJ g k m A O fd res i a 0 c ∧ c.reg gK = k) 4 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hB, hI, hF, hR, ho⟩, hAa, hK⟩ => ⟨?_, ?_⟩
    · have hq := occ_lt hi ha
      have hb : bD g k = bV g + k * (cycles g k).length := rfl
      addr_ok [hG.1.rv, hB, hAa]
    have hag : Agree [sOk, sQ, sC, rT] c (run (.seq (.seq (.const sOk 1) (.add sQ sBase sA))
        (ld sC gV sQ)) c) := agree_run (by decide) rfl rfl (by decide) c
    have hq := occ_lt hi ha
    have hcv : m (bV g + (i * k + a)) = (verts g k).getD (i * k + a) 0 :=
      hV.getD (by rw [length_verts]; exact hq)
    refine ⟨⟨(show Indep [sOk, sQ, sC, rT] (RG g k m A) by indep [RG, gA_iff]) c _ hag hG,
      by rw [hag.reg sBase (by decide), hB], by rw [hag.reg sI (by decide), hI],
      by rw [hag.reg sA (by decide), hAa], ?_, by simp, by rw [hag.reg sF (by decide), hF],
      by rw [hag.reg sRes (by decide), hR], by rw [hag.out, ho]⟩, by rw [hag.reg gK (by decide), hK]⟩
    simp +decide [hB, hAa, hG.1.rv, hG.2.1, hcv]
  have hl := HTB.forUpC (i := sJ) (n := gK) (N := k) (body := recBody) (RJ g k m A O fd res i a) 36
    (by decide) (by decide) (by decide) (fun j => by indep [RJ, RG, gA_iff])
    (fun j hj => recBody_spec g k m A O fd res i a j hi hj hV hbits hSV hSA)
  exact HTB.assoc (HTB.assoc ((h0.seq (hl.seq (recUpd_spec g k m A O i a))).weaken (by omega)))

/-- The state before cycle `i` of the recovery. -/
def RI (g : Graph) (k : ℕ) (m : ℕ → ℕ) (A : ℕ) (i : ℕ) (c : Config) : Prop :=
  RG g k m A c ∧ c.reg sBase = i * k ∧ c.out = 1 :: (List.range i).map (recPos g k (memAsg m A))

theorem recRow_spec (g : Graph) (k : ℕ) (m : ℕ → ℕ) (A : ℕ) (i : ℕ) (hi : i < (cycles g k).length)
    (hV : Arr m (bV g) (verts g k)) (hbits : ∀ x < k * (cycles g k).length, m (A + x) ≤ 1)
    (hSV : bD g k ≤ S) (hSA : A + k * (cycles g k).length ≤ S) :
    HTB S recRow (fun c => RI g k m A i c ∧ c.reg sI = i ∧ c.reg gT = (cycles g k).length)
      (fun c => RI g k m A (i + 1) c ∧ c.reg sI = i ∧ c.reg gT = (cycles g k).length)
      (k * (k * 40 + 18) + 7) := by
  set O := 1 :: (List.range i).map (recPos g k (memAsg m A))
  have h0 : HTB S (.seq (.const sF 0) (.const sRes 0))
      (fun c => RI g k m A i c ∧ c.reg sI = i ∧ c.reg gT = (cycles g k).length)
      (fun c => (RA g k m A O i 0 c ∧ c.reg gT = (cycles g k).length) ∧ c.reg gK = k) 2 :=
      HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨hG, hB, ho⟩, hI, hT⟩ => ?_
    have hag : Agree [sF, sRes] c (run (.seq (.const sF 0) (.const sRes 0)) c) :=
      agree_run (by decide) rfl rfl (by decide) c
    refine ⟨⟨⟨(show Indep [sF, sRes] (RG g k m A) by indep [RG, gA_iff]) c _ hag hG,
      by rw [hag.reg sBase (by decide), hB], by rw [hag.reg sI (by decide), hI], by simp, by simp,
      by rw [hag.out, ho]⟩, by rw [hag.reg gT (by decide), hT]⟩, by rw [hag.reg gK (by decide), hG.1.rk]⟩
  have hl := HTB.forUpC (i := sA) (n := gK) (N := k) (body := recA)
    (fun a c => RA g k m A O i a c ∧ c.reg gT = (cycles g k).length) (k * 40 + 14)
    (by decide) (by decide) (by decide) (fun j => by indep [RA, RG, gA_iff])
    (fun a ha => (recA_spec g k m A O i a hi ha hV hbits hSV hSA).frame
      (F := fun c => c.reg gT = (cycles g k).length) (fun c c' hfr h => by
        rw [hfr.reg gT (by decide), h]) |>.mono (fun c ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨h1, h3, h4⟩, h2⟩)
        (fun c ⟨⟨h1, h3, h4⟩, h2⟩ => ⟨⟨h1, h2⟩, h3, h4⟩) le_rfl)
  have h2 : HTB S (.seq (.write sRes) (.add sBase sBase gK))
      (fun c => (RA g k m A O i k c ∧ c.reg gT = (cycles g k).length) ∧ c.reg sA = k ∧ c.reg gK = k)
      (fun c => RI g k m A (i + 1) c ∧ c.reg sI = i ∧ c.reg gT = (cycles g k).length) 2 :=
      HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨⟨⟨hga, hm, hA⟩, hB, hI, _, hR, ho⟩, hT⟩, _, hK⟩ => ?_
    refine ⟨⟨⟨(show RegIndep [sBase] (GA g k) by indep [gA_iff]).setReg (by decide) _
      ((show RegIndep [sBase] (GA g k) by indep [gA_iff]).emit _ hga), by simp [hm],
      by simp +decide [hA]⟩, ?_, ?_⟩, ?_, ?_⟩
    · simp +decide [hB, hK]; ring
    · simp only [run_seq', run_write, run_add, setReg_out, emit_out, ho, hR, O, List.range_succ,
        List.map_append, List.map_singleton, List.cons_append, recPos]
    · simp +decide [hI]
    · simp +decide [hT]
  refine HTB.assoc ((h0.seq (hl.seq h2)).weaken (le_of_eq ?_))
  ring

/-- **Phase 9, the recovery**: with the 2-SAT answer `ok` in `tOK` and the assignment at `A` in
the memory `m` (bits `≤ 1`), the machine writes `[0]` if `ok = 0`, and otherwise `1` followed by
the first passing position of every cycle. -/
theorem stepRec_spec (g : Graph) (k : ℕ) (m : ℕ → ℕ) (A ok : ℕ) (hV : Arr m (bV g) (verts g k))
    (hbits : ∀ x < k * (cycles g k).length, m (A + x) ≤ 1) (hSV : bD g k ≤ S)
    (hSA : A + k * (cycles g k).length ≤ S) :
    HTB S stepRec (fun c => RG g k m A c ∧ c.out = [] ∧ c.reg TwoSat.tOK = ok)
      (fun c => c.out = if ok = 0 then [0] else
        1 :: (List.range (cycles g k).length).map (recPos g k (memAsg m A)))
      ((cycles g k).length * (k * (k * 40 + 18) + 11) + 7) := by
  refine HTB.ifz (b := (cycles g k).length * (k * (k * 40 + 18) + 11) + 6) ?_ ?_
  · refine HTB.of_HT rfl <| HT.run_le (by decide) (by simp only [size]; omega)
      fun c ⟨⟨_, ho, hok⟩, h0⟩ => ?_
    rw [hok] at h0
    simp [ho, h0]
  · refine HTB.pre_fact (p := ok ≠ 0) (fun c ⟨⟨_, _, hok⟩, h0⟩ => by rw [← hok]; exact h0) fun hok => ?_
    have h1 : HTB S (.seq (.seq (.const sX 1) (.write sX)) (.const sBase 0))
        (fun c => (RG g k m A c ∧ c.out = [] ∧ c.reg TwoSat.tOK = ok) ∧ c.reg TwoSat.tOK ≠ 0)
        (fun c => RI g k m A 0 c ∧ c.reg gT = (cycles g k).length) 3 := HTB.of_HT rfl <| by
      refine HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hga, hm, hA⟩, ho, _⟩, _⟩ => ?_
      refine ⟨⟨⟨(show RegIndep [sX, sBase] (GA g k) by indep [gA_iff]).run_of_sub (by decide)
        (by decide) hga, by simp [hm], by simp +decide [hA]⟩, by simp +decide, by simp [ho]⟩,
        by simp +decide [hga.rt]⟩
    have hl := HTB.forUpC (i := sI) (n := gT) (N := (cycles g k).length) (body := recRow)
      (RI g k m A) (k * (k * 40 + 18) + 7) (by decide) (by decide) (by decide)
      (fun j => by indep [RI, RG, gA_iff]) (fun i hi => recRow_spec g k m A i hi hV hbits hSV hSA)
    refine HTB.assoc (HTB.assoc ((h1.seq hl).mono (fun _ h => h) (fun c ⟨⟨_, _, ho⟩, _, _⟩ => ?_)
      (le_of_eq ?_)))
    · rw [ho, ite_eq_right hok]
    · ring

end STACS2027.Runtimes.ZeroCost
