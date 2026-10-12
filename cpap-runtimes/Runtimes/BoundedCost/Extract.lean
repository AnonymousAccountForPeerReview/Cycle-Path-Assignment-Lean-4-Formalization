module

public import Runtimes.BoundedCost.Answer
import Mathlib.Tactic

/-!
# Theorem 4 on the RAM: the extraction

`extract5 = stepInit ; readAns ; stepRec` runs on the input `boundedCostInput g k Ψ` followed by the
answer `ans` of the Almost 2-SAT solver on `a2In (shiftF Γ') Ψ` (`A2Answer`):

* `ans = [0]`: the flag `tOK = 0`, and `stepRec` writes `[0]` (`stepRec_zero`); no assignment of
  cost `≤ Ψ` exists (`noAssignment_of_shift`);
* `ans = 1 :: |D| :: (D ++ T)`: the list `T` starts at `P = bD + 3 + |D|`; its entries are
  increasing variables of the shifted formula, so they lie in `[1, kt]`, there are at most `kt`
  of them, and the cell after them is zero (the memory beyond the input). The loop `readBody`
  (`kt` iterations) reads them until the first zero and sets the bits `AS[y − 1] := 1` of a zero
  table `AS` at `A = P + kt`, beyond the answer (`RdInv`). The table is then the assignment
  `x ↦ (x + 1 ∈ T)`, which satisfies `Γ_𝓘` for the deleted overlaps `𝓘`, `|𝓘| ≤ Ψ`
  (`permitted_of_shift`), and Corollary 5's recovery answers correctly (`answer_of_table`).

`extract5_spec`: within `extractCost g k` steps and the addresses below
`extractSpace g k Ψ = bD + 3 + |Γ'| + 2kt` (`|D| ≤ |Γ'|`).
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost Complexity.SAT

variable {S : ℕ}

/-- The state after `i` iterations of the reading loop (`m₀` the initial memory, `P` the start
of `T`, `n = kt`, the table at `P + n`). -/
def RdInv (g : Graph) (k : ℕ) (m₀ : ℕ → ℕ) (P : ℕ) (T : List ℕ) (i : ℕ) (c : Config) : Prop :=
  GA g k c ∧ c.reg eP = P ∧ c.reg TwoSat.tAS = P + k * (cycles g k).length ∧ c.reg eOne = 1 ∧
    c.reg eD = (if T.length < i then 1 else 0) ∧ c.out = [] ∧ c.reg TwoSat.tOK = 1 ∧
    SameOn (· < P + k * (cycles g k).length) m₀ c.mem ∧
    ∀ x < k * (cycles g k).length,
      c.mem (P + k * (cycles g k).length + x) = if x + 1 ∈ T.take i then 1 else 0

/-- What the loop needs to know of the answer: `T` at `P`, zero after it, entries in `[1, n]`,
at most `n` of them, and a zero table at `P + n`. -/
structure AnsMem (m₀ : ℕ → ℕ) (P n : ℕ) (T : List ℕ) : Prop where
  tval : Arr m₀ P T
  tend : m₀ (P + T.length) = 0
  tpos : ∀ y ∈ T, 1 ≤ y ∧ y ≤ n
  tlen : T.length ≤ n
  tzero : ∀ x < n, m₀ (P + n + x) = 0

theorem rdInv_indep (g : Graph) (k : ℕ) (m₀ : ℕ → ℕ) (P : ℕ) (T : List ℕ) (i : ℕ) :
    Indep [sI, rT] (RdInv g k m₀ P T i) := by
  indep [RdInv, gA_iff]

theorem readBody_spec (g : Graph) (k : ℕ) (m₀ : ℕ → ℕ) (P : ℕ) (T : List ℕ)
    (hM : AnsMem m₀ P (k * (cycles g k).length) T)
    (hS : P + 2 * (k * (cycles g k).length) ≤ S) (i : ℕ) (hi : i < k * (cycles g k).length) :
    HTB S readBody (fun c => RdInv g k m₀ P T i c ∧ c.reg sI = i ∧ c.reg gKT = k * (cycles g k).length)
      (fun c => RdInv g k m₀ P T (i + 1) c ∧ c.reg sI = i ∧ c.reg gKT = k * (cycles g k).length)
      10 := by
  refine HTB.run_le (by decide) (by decide)
    fun c ⟨⟨hga, hP, hA, h1, hD, ho, hok, hsame, hbits⟩, hI, hK⟩ => ?_
  have hfr := frame_of_wregs (s := readBody) (by decide) [eY, eD, rT] (by decide) c
  have hga' : GA g k (run readBody c) :=
    (show RegIndep [eY, eD, rT] (GA g k) by indep [gA_iff]) _ _ hfr hga
  have hout : (run readBody c).out = c.out := run_out_of_writes (by decide) (by decide) c
  by_cases hTi : T.length < i
  · -- the list is finished: nothing happens
    have hD1 : c.reg eD = 1 := by rw [hD, ite_eq_left hTi]
    have hrun : run readBody c = c := by simp [readBody, hD1]
    refine ⟨AddrOK.ifz (fun h => absurd h (by omega)) (fun _ => AddrOK.of_memFree rfl), ?_⟩
    rw [hrun]
    have ht : T.take (i + 1) = T.take i := by
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    refine ⟨⟨hga, hP, hA, h1, by rw [hD1, ite_eq_left (by omega)], ho, hok, hsame, fun x hx => ?_⟩,
      hI, hK⟩
    rw [ht]; exact hbits x hx
  · have hD0 : c.reg eD = 0 := by rw [hD, ite_eq_right hTi]
    have hrd : c.mem (P + i) = m₀ (P + i) := hsame _ (by omega)
    rcases Nat.lt_or_ge i T.length with hlt | hge
    · -- an entry `y = T[i]`: `AS[y - 1] := 1`
      have hy : c.mem (P + i) = T[i] := by rw [hrd, hM.tval i hlt]
      have hyb := hM.tpos _ (List.getElem_mem hlt)
      have hyne : T[i] ≠ 0 := by omega
      refine ⟨by addr_ok [readBody, hD0, hP, hI, hy, hA, h1], ?_⟩
      have hmem : (run readBody c).mem =
          upd c.mem (P + k * (cycles g k).length + (T[i] - 1)) 1 := by
        simp +decide only [readBody, run_ifz', run_seq', run_ld, run_dec (show eY ≠ rT by decide),
          run_st (show eOne ≠ rT by decide), setReg_reg, setReg_mem, setMem_mem_upd,
          ↓reduceIte, hD0, hP, hI, hy, hyne, hA, h1]
      have hDr : (run readBody c).reg eD = 0 := by
        simp +decide only [readBody, run_ifz', run_seq', run_ld, run_dec (show eY ≠ rT by decide),
          run_st (show eOne ≠ rT by decide), setReg_reg, setMem_reg, ↓reduceIte, hD0, hP, hI, hy,
          hyne]
      refine ⟨⟨hga', by rw [hfr eP (by decide), hP], by rw [hfr _ (by decide), hA],
        by rw [hfr eOne (by decide), h1], by rw [hDr, ite_eq_right (by omega)],
        by rw [hout, ho], by rw [hfr _ (by decide), hok], ?_, fun x hx => ?_⟩,
        by rw [hfr sI (by decide), hI], by rw [hfr gKT (by decide), hK]⟩
      · intro a ha
        have ha' : a < P + k * (cycles g k).length := ha
        rw [hmem, upd_apply, ite_eq_right (by omega)]
        exact hsame a ha
      · rw [hmem, upd_apply, List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton]
        by_cases hxe : x = T[i] - 1
        · rw [ite_eq_left (by omega), ite_eq_left (Or.inr (by omega))]
        · rw [ite_eq_right (by omega), hbits x hx]
          by_cases hm : x + 1 ∈ T.take i
          · rw [ite_eq_left hm, ite_eq_left (Or.inl hm)]
          · rw [ite_eq_right hm, ite_eq_right (by rintro (h | h); exact hm h; omega)]
    · -- the end of the list: a zero cell
      have heq : i = T.length := by omega
      have hy : c.mem (P + i) = 0 := by rw [hrd, heq, hM.tend]
      refine ⟨by addr_ok [readBody, hD0, hP, hI, hy], ?_⟩
      have hrun : run readBody c = (c.setReg eY 0).setReg eD 1 := by
        simp +decide only [readBody, run_ifz', run_seq', run_ld, run_const, setReg_reg, ↓reduceIte,
          hD0, hP, hI, hy]
      rw [hrun]
      have ht : T.take (i + 1) = T.take i := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      all_goals simp +decide only [Config.setReg, ↓reduceIte]
      · exact ⟨hga.rk, hga.rt, hga.rv, hga.rkt, hga.rnv⟩
      · exact hP
      · exact hA
      · exact h1
      · rw [ite_eq_left (by omega)]
      · exact ho
      · exact hok
      · exact hsame
      · intro x hx; rw [ht]; exact hbits x hx
      · exact hI
      · exact hK

/-- The state after the flag (`1`). -/
def FlagPost (g : Graph) (k : ℕ) (m₀ : ℕ → ℕ) (ok : ℕ) (c : Config) : Prop :=
  GA g k c ∧ c.reg eP = bD g k + 1 ∧ c.reg TwoSat.tOK = ok ∧ c.mem = m₀ ∧ c.out = []

/-- Reading the flag of the answer (cell `bD + 1`). -/
theorem readFlag_spec (g : Graph) (k Ψ : ℕ) (ans : List ℕ) (hS : bD g k + 2 ≤ S) :
    HTB S (.seq (addc eP rFREE 1) (.load TwoSat.tOK eP))
      (fun c => GA g k c ∧ c.reg rFREE = bD g k ∧ c.mem = (initial (boundedCostInput g k Ψ ++ ans)).mem ∧
        c.out = [])
      (FlagPost g k (initial (boundedCostInput g k Ψ ++ ans)).mem
        ((initial (boundedCostInput g k Ψ ++ ans)).mem (bD g k + 1))) 3 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hga, hfr, hm, ho⟩ => ⟨by addr_ok [hfr], ?_⟩
  refine ⟨(show RegIndep [eP, rT, TwoSat.tOK] (GA g k) by indep [gA_iff]).run_of_sub
    (by decide) (by decide) hga, ?_, ?_, ?_, ?_⟩
  all_goals simp +decide [run_addc (show rFREE ≠ rT by decide), hfr, hm, ho]

/-- Before the loop: `|D|`, the start `P = bD + 3 + |D|` of `T`, the table at `P + kt`. -/
theorem readPre_spec (g : Graph) (k : ℕ) (m₀ : ℕ → ℕ) (T : List ℕ) (d : ℕ)
    (hd : m₀ (bD g k + 2) = d) (hz : ∀ x < k * (cycles g k).length,
      m₀ (bD g k + 3 + d + k * (cycles g k).length + x) = 0) (hS : bD g k + 3 ≤ S) :
    HTB S readPre (FlagPost g k m₀ 1)
      (fun c => RdInv g k m₀ (bD g k + 3 + d) T 0 c ∧ c.reg gKT = k * (cycles g k).length) 9 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hga, hP, hok, hm, ho⟩ => ⟨by
    addr_ok [readPre, hP], ?_⟩
  have hfr := frame_of_wregs (s := readPre) (by decide) [eP, eY, rT, TwoSat.tAS, eD, eOne]
    (by decide) c
  have hga' : GA g k (run readPre c) :=
    (show RegIndep [eP, eY, rT, TwoSat.tAS, eD, eOne] (GA g k) by indep [gA_iff]) _ _ hfr hga
  have hmem : (run readPre c).mem = m₀ := by
    rw [run_mem_of_stores (by decide) (by decide) c, hm]
  have hP' : (run readPre c).reg eP = bD g k + 3 + d := by
    simp +decide [readPre, run_inc, hP, hm, hd]; omega
  refine ⟨⟨hga', hP', ?_, ?_, ?_, by rw [run_out_of_writes (by decide) (by decide) c, ho],
    by rw [hfr _ (by decide), hok], by rw [hmem]; exact fun a _ => rfl, fun x hx => ?_⟩,
    by rw [hfr gKT (by decide), hga.rkt]⟩
  · simp +decide [readPre, run_inc, hP, hm, hd, hga.rkt]; omega
  · simp +decide [readPre, run_inc]
  · simp +decide [readPre, run_inc]
  · rw [hmem, hz x hx]; simp

/-- The bound of the reading of the answer. -/
def readCost (g : Graph) (k : ℕ) : ℕ := 14 * (k * (cycles g k).length) + 17

/-- **Reading a positive answer** `1 :: |D| :: (D ++ T)`: the table of `T`. -/
theorem readAns_some (g : Graph) (k Ψ : ℕ) {D T : List ℕ}
    (hM : AnsMem (initial (boundedCostInput g k Ψ ++ (1 :: D.length :: (D ++ T)))).mem
      (bD g k + 3 + D.length) (k * (cycles g k).length) T)
    (hS : bD g k + 3 + D.length + 2 * (k * (cycles g k).length) ≤ S) :
    HTB S readAns
      (fun c => GA g k c ∧ c.reg rFREE = bD g k ∧
        c.mem = (initial (boundedCostInput g k Ψ ++ (1 :: D.length :: (D ++ T)))).mem ∧ c.out = [])
      (RdInv g k (initial (boundedCostInput g k Ψ ++ (1 :: D.length :: (D ++ T)))).mem
        (bD g k + 3 + D.length) T (k * (cycles g k).length)) (readCost g k) := by
  set ans := 1 :: D.length :: (D ++ T)
  set m₀ := (initial (boundedCostInput g k Ψ ++ ans)).mem
  obtain ⟨-, -, -, -, -, hA, -⟩ := input5z_facts g k Ψ ans
  rw [arr_cons, arr_cons] at hA
  have h1 := readFlag_spec (S := S) g k Ψ ans (by omega)
  rw [hA.1] at h1
  have h2 := readPre_spec (S := S) g k m₀ T D.length (by simpa [Nat.add_assoc] using hA.2.1)
    hM.tzero (by omega)
  have hl := HTB.forUpC (S := S) (i := sI) (n := gKT) (N := k * (cycles g k).length)
    (body := readBody) (RdInv g k m₀ (bD g k + 3 + D.length) T) 10 (by decide) (by decide)
    (by decide) (fun j => rdInv_indep g k m₀ _ T j)
    (fun i hi => readBody_spec g k m₀ _ T hM (by omega) i hi)
  refine (h1.seq (HTB.ifz (b := readCost g k - 4) ?_ ?_)).weaken (by unfold readCost; omega)
  · exact HTB.of_false fun c ⟨⟨_, _, hok, _⟩, h0⟩ => by rw [hok] at h0; exact absurd h0 (by decide)
  · refine ((h2.pre fun c ⟨h, _⟩ => h).seq hl).mono (fun _ h => h) (fun c ⟨h, _, _⟩ => h) ?_
    unfold readCost; omega

/-- The bound of the extraction. -/
def extractCost (g : Graph) (k : ℕ) : ℕ :=
  5 * (cycles g k).length + 16 + (readCost g k + ((cycles g k).length * (k * (k * 40 + 18) + 11) + 7))

/-- The space of the extraction. -/
def extractSpace (g : Graph) (k Ψ : ℕ) : ℕ :=
  bD g k + 3 + (almostFormula g k Ψ).length + 2 * (k * (cycles g k).length)

/-- **The extraction** of Theorem 4: on the input followed by any correct answer of the Almost
2-SAT solver on `a2In (shiftF Γ') Ψ`, it writes a correct answer of Theorem 4. -/
theorem extract5_spec (g : Graph) (k Ψ : ℕ) (hk : 4 ≤ k) {ans : List ℕ}
    (hA : A2Answer (shiftF (almostFormula g k Ψ)) Ψ ans) :
    HTB (extractSpace g k Ψ) extract5 (fun c => c = initial (boundedCostInput g k Ψ ++ ans))
      (fun c => BoundedCostAnswer g k Ψ c.out) (extractCost g k) := by
  have hl := lay5 g k
  have hI := stepInitZ_spec (S := extractSpace g k Ψ) g k Ψ ans (by unfold extractSpace; omega)
  rcases hA with ⟨hnot, rfl⟩ | ⟨D, T, rfl, hD, hDm, hDl, hT, hTo, hsat⟩
  · -- no deletion set: `[0]`
    obtain ⟨-, -, -, -, -, hA, -⟩ := input5z_facts g k Ψ [0]
    rw [arr_singleton] at hA
    have h1 := readFlag_spec (S := extractSpace g k Ψ) g k Ψ [0] (by unfold extractSpace; omega)
    rw [hA] at h1
    have h2 : HTB (extractSpace g k Ψ) readAns
        (fun c => GA g k c ∧ c.reg rFREE = bD g k ∧
          c.mem = (initial (boundedCostInput g k Ψ ++ [0])).mem ∧ c.out = [])
        (fun c => c.reg TwoSat.tOK = 0 ∧ c.out = []) 5 := by
      refine (h1.seq (HTB.ifz (b := 1) ?_ ?_)).weaken (by omega)
      · exact (HTB.skip.mono (fun c ⟨⟨_, _, hok, _, ho⟩, _⟩ => ⟨hok, ho⟩) (fun _ h => h) le_rfl)
      · exact HTB.of_false fun c ⟨⟨_, _, hok, _⟩, h0⟩ => h0 hok
    refine (hI.seq (h2.seq stepRec_zero)).mono (fun _ h => h)
      (fun c ho => Or.inl ⟨noAssignment_of_shift hk hnot, ho⟩) (by unfold extractCost readCost; omega)
  · -- a deletion set `D` and the true variables `T`
    set ans := 1 :: D.length :: (D ++ T)
    set m₀ := (initial (boundedCostInput g k Ψ ++ ans)).mem
    have hDf : D.length ≤ (almostFormula g k Ψ).length := by
      have := keptOf_length hD (fun i hi => by simpa using hDm i hi); omega
    have hTb : ∀ y ∈ T, 1 ≤ y ∧ y ≤ k * (cycles g k).length := fun y hy => occursIn_shiftF (almost_two g k Ψ) (hTo y hy)
    have hTl : T.length ≤ k * (cycles g k).length := length_le_of_pairwise hT hTb
    obtain ⟨-, -, -, hV, -, hAr, hZ⟩ := input5z_facts g k Ψ ans
    rw [arr_cons, arr_cons, arr_append] at hAr
    have hlen : ans.length = 2 + D.length + T.length := by simp [ans]; omega
    have hM : AnsMem m₀ (bD g k + 3 + D.length) (k * (cycles g k).length) T :=
      ⟨by simpa [Nat.add_assoc] using hAr.2.2.2, hZ _ (by rw [hlen]; omega), hTb, hTl,
        fun x hx => hZ _ (by rw [hlen]; omega)⟩
    have hR := readAns_some (S := extractSpace g k Ψ) g k Ψ hM (by unfold extractSpace; omega)
    -- the recovery from the table
    have hrec : HTB (extractSpace g k Ψ) stepRec (RdInv g k m₀ (bD g k + 3 + D.length) T (k * (cycles g k).length))
        (fun c => BoundedCostAnswer g k Ψ c.out) ((cycles g k).length * (k * (k * 40 + 18) + 11) + 7) := by
      refine HTB.of_forall fun c₀ hc₀ => ?_
      obtain ⟨hga, -, hAS, -, -, ho, hok, hsame, hbits⟩ := hc₀
      have hbits' : ∀ x < k * (cycles g k).length,
          c₀.mem (bD g k + 3 + D.length + k * (cycles g k).length + x) = if x + 1 ∈ T then 1 else 0 := fun x hx => by
        rw [hbits x hx, List.take_of_length_le hTl]
      have hV' : Arr c₀.mem (bV g) (verts g k) := fun i hi => by
        rw [hsame (bV g + i) (by rw [length_verts] at hi; show bV g + i < _; omega)]
        exact hV i hi
      refine (stepRec_spec g k c₀.mem (bD g k + 3 + D.length + k * (cycles g k).length) 1 hV' (fun x hx => by rw [hbits' x hx]; split <;> omega)
        (by unfold extractSpace; omega) (by unfold extractSpace; omega)).mono
        (fun c hc => by subst hc; exact ⟨⟨hga, rfl, hAS⟩, ho, hok⟩) (fun c ho => ?_) le_rfl
      rw [ho, ite_eq_right (by decide)]
      obtain ⟨I, hIl, hσ⟩ := permitted_of_shift hD hDm hDl hsat
      refine answer_of_table hk _ hIl ?_
      rw [TwoSat.evalCNF_congr (permitted_two g k I) (σ' := fun x => decide (x + 1 ∈ T))
        fun x hx => ?_]
      · exact hσ
      · simp only [memAsg, hbits' x hx]
        by_cases hx' : x + 1 ∈ T <;> simp [hx']
    refine (hI.seq (hR.seq hrec)).weaken (le_of_eq ?_)
    rfl

end STACS2027.Runtimes.BoundedCost
