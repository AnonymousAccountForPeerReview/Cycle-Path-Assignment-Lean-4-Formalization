module

public import ApproximationHardness.RAM.Polarize.Space
import Lean.Elab.Tactic.Omega

/-!
# The Lemma 10 program computes `polarize` in linear time
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

/-! ### The fixed data of a run -/

/-- The input memory. -/
def polBase (f : CNF) : Nat → Nat := (initial (ramInput f)).mem
/-- The input length `N`. -/
def polN (f : CNF) : Nat := (ramInput f).length
/-- `B = N + 2n`, the start of the table of positive kept occurrences. -/
def polB (f : CNF) : Nat := polN f + variableBound f + variableBound f
/-- The memory after the count pass. -/
def polMc (f : CNF) : Nat → Nat := cntMem (polBase f) (polN f) f.flatten

/-- The registers holding the constants and the dimensions. -/
structure PolRegs (f : CNF) (c : Config) : Prop where
  k : Consts c
  N : c.reg Reg.N = polN f
  B : c.reg Reg.B = polB f
  n : c.reg Reg.n = variableBound f

theorem PolRegs.frame {f : CNF} {c c' : Config} (h : PolRegs f c) (hf : ∀ r, KeepFixed r → c'.reg r = c.reg r) :
    PolRegs f c' :=
  ⟨h.k.frame (hf _ (by decide)) (hf _ (by decide)) (hf _ (by decide)) (hf _ (by decide)),
    (hf _ (by decide)).trans h.N, (hf _ (by decide)).trans h.B, (hf _ (by decide)).trans h.n⟩

theorem polBase_zero (f : CNF) : polBase f 0 = f.length := by simp [polBase, initial, ramInput]

theorem polBase_code (f : CNF) (i : Nat) : polBase f (1 + i) = (f.flatMap clauseCode).getD i 0 := by
  simp [polBase, initial, ramInput, Nat.add_comm 1 i]

theorem polBase_above (f : CNF) {a : Nat} (ha : polN f ≤ a) : polBase f a = 0 := by
  simp only [polBase, initial, polN] at *
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

theorem polN_eq (f : CNF) : polN f = 1 + (f.flatMap clauseCode).length := by simp [polN, ramInput]; omega

/-- A memory agreeing with the input below `N`. -/
def InputBelow (f : CNF) (mem : Nat → Nat) : Prop := ∀ a, a < polN f → mem a = polBase f a

theorem inputBelow_cnt (f : CNF) (ls : List Literal) : InputBelow f (cntMem (polBase f) (polN f) ls) :=
  fun _ ha => cntMem_below _ _ _ ha

theorem inputBelow_kp (f : CNF) (M : Nat → Nat) (hM : InputBelow f M) (ks : List Literal) :
    InputBelow f (kpMem M (polB f) ks) := fun a ha => by
  rw [kpMem_below _ _ _ (by unfold polB; omega)]; exact hM a ha

/-! ### Restarting at the first clause -/

theorem restart_run (f : CNF) (c : Config) (hone : c.reg Reg.one = 1) (hm : InputBelow f c.mem) :
    (run restart c).reg Reg.m = f.length ∧ (run restart c).reg Reg.p = 1 ∧
      At (run restart c) (f.flatMap clauseCode) ∧ (run restart c).mem = c.mem ∧ (run restart c).out = c.out ∧
      ∀ r, r ≠ Reg.m → r ≠ Reg.p → (run restart c).reg r = c.reg r := by
  have hN := polN_eq f
  have hm0 : c.mem 0 = f.length := by rw [hm 0 (by omega), polBase_zero]
  have hp : (run restart c).reg Reg.p = 1 := by simp +decide [restart, run, hone]
  have hmem : (run restart c).mem = c.mem := by simp [restart, run]
  refine ⟨by simp +decide [restart, run, hm0], hp, ?_, hmem, by simp [restart, run], ?_⟩
  · intro i hi
    rw [hp, hmem, hm _ (by omega), Nat.add_comm 1 i, ← polBase_code, Nat.add_comm i 1]
  · intro r h1 h2; simp [restart, run, h1, h2]

/-! ### The count pass -/

/-- The invariant of the count pass after the clauses `pre`. -/
def CntInv (f : CNF) (c : Config) (pre : CNF) : Prop :=
  c.mem = cntMem (polBase f) (polN f) pre.flatten ∧ c.reg Reg.p = 1 + (pre.flatMap clauseCode).length ∧
    PolRegs f c ∧ c.reg PR.r = 0 ∧ c.out = [f.length]

/-- The space of the Lemma 10 program: the input, the counts and the table `B + v`. -/
def polSpace (f : CNF) : Nat := polB f + variableBound f

/-- The hypotheses of the address conditions of the passes over the clauses, from the registers. -/
theorem bodyPre_of {f pre suf : CNF} {cl : Clause} {c : Config} (hf : ∀ c ∈ f, c.length = 2 ∨ c.length = 3)
    (hpre : pre ++ cl :: suf = f) (hR : PolRegs f c) (hp : c.reg Reg.p = 1 + (pre.flatMap clauseCode).length)
    (hAt : At c (clauseCode cl ++ suf.flatMap clauseCode)) :
    BodyPre (variableBound f) (polSpace f) cl (suf.flatMap clauseCode) c ∧ c.reg Reg.N + variableBound f +
      variableBound f ≤ polSpace f ∧ c.reg Reg.B + variableBound f ≤ polSpace f := by
  have hclf : cl ∈ f := by rw [← hpre]; simp
  have hN := ramInput_clause_le hpre
  refine ⟨⟨hf cl hclf, hAt, hR.k, fun l hl => literal_lt_variableBound hclf hl, ?_⟩, ?_, ?_⟩
  · rw [hp, clauseCode_length]; unfold polSpace polB polN; omega
  · rw [hR.N]; unfold polSpace polB; omega
  · rw [hR.B]; unfold polSpace; omega

theorem cnt_step (f : CNF) (hf : ∀ c ∈ f, c.length = 2 ∨ c.length = 3) :
    ∀ pre cl suf c, pre ++ cl :: suf = f → (fun pre c => CntInv f c pre) pre c → c.reg Reg.m = suf.length + 1 →
      At c (clauseCode cl ++ suf.flatMap clauseCode) →
      AddrOK (polSpace f) cntBody c ∧
      (fun pre c => CntInv f c pre) (pre ++ [cl]) (run cntBody c) ∧ (run cntBody c).reg Reg.m = suf.length ∧
        At (run cntBody c) (suf.flatMap clauseCode) := by
  intro pre cl suf c hpre ⟨hm, hp, hR, hr, ho⟩ hmc hAt
  have hcl := hf cl (by rw [← hpre]; simp)
  have hlen : c.reg Reg.p + (clauseCode cl ++ suf.flatMap clauseCode).length ≤ c.reg Reg.N := by
    rw [hp, hR.N, polN_eq, ← hpre]; simp; omega
  obtain ⟨hB, hBN, -⟩ := bodyPre_of hf hpre hR hp hAt
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := cntBody_step c cl _ hcl hAt hR.k (by rw [hm, hR.N]) hlen
  refine ⟨cntBody_addrOK hB hBN, ⟨?_, ?_, ?_, ?_, ?_⟩, by rw [m2, hmc]; rfl, m4⟩
  · rw [m1, hR.N]; simp
  · rw [m3, hp]; simp; omega
  · exact ⟨hR.k.frame (m6 _ (by decide)) (m6 _ (by decide)) (m6 _ (by decide)) (m6 _ (by decide)),
      (m6 _ (by decide)).trans hR.N, (m6 _ (by decide)).trans hR.B, (m6 _ (by decide)).trans hR.n⟩
  · rw [m6 _ (by decide)]; exact hr
  · rw [m5]; exact ho

/-! ### Reading the tables -/

theorem polMc_input (f : CNF) : InputBelow f (polMc f) := inputBelow_cnt f _

theorem litAddr_lt (f : CNF) {l : Literal} (hl : l ∈ f.flatten) : litAddr (polN f) l < polN f + variableBound f + variableBound f := by
  obtain ⟨c, hc, hlc⟩ := List.mem_flatten.mp hl
  have := literal_lt_variableBound hc hlc
  have := signCode_le l
  unfold litAddr; omega

theorem polMc_count (f : CNF) (v : Nat) (s : Bool) :
    polMc f (litAddr (polN f) ⟨v, s⟩) = occurrences f v s := by
  unfold polMc cntMem
  rw [polBase_above f (by unfold litAddr; omega), count_map_inj _ (litAddr_inj _) _ _, occurrences_eq_count]; simp

theorem polMc_B (f : CNF) (v : Nat) : polMc f (polB f + v) = 0 := by
  unfold polMc cntMem
  rw [polBase_above f (by unfold polB; omega), List.count_eq_zero_of_not_mem]
  intro h
  obtain ⟨l, hl, he⟩ := List.mem_map.mp h
  have := litAddr_lt f hl
  unfold polB at he; omega

/-- The memory agrees with `polMc` below `B`. -/
def McBelow (f : CNF) (mem : Nat → Nat) : Prop := ∀ a, a < polB f → mem a = polMc f a

theorem mcBelow_kp (f : CNF) (ks : List Literal) : McBelow f (kpMem (polMc f) (polB f) ks) :=
  fun _ ha => kpMem_below _ _ _ ha

theorem countsAt_of (f : CNF) (c : Config) (hN : c.reg Reg.N = polN f) (hm : McBelow f c.mem) (l : Literal)
    (hl : l.var < variableBound f) : CountsAt f c l := by
  refine ⟨?_, ?_⟩
  · rw [hN, hm _ (by unfold polB; omega), ← litAddr_false, polMc_count]
  · rw [hN, hm _ (by unfold polB; omega), ← litAddr_true, polMc_count]

theorem At.advance {c c' : Config} {u w : List Nat} (h : At c (u ++ w)) (hp : c'.reg Reg.p = c.reg Reg.p + u.length)
    (hm : ∀ a, a < c.reg Reg.p + (u ++ w).length → c'.mem a = c.mem a) : At c' w := by
  intro i hi
  rw [hp, hm _ (by simp; omega), Nat.add_assoc]
  have := h (u.length + i) (by simp; omega)
  rw [this, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp

theorem vars_lt {f : CNF} {cl : Clause} (hc : cl ∈ f) : ∀ l ∈ cl, l.var < variableBound f :=
  fun _ hl => literal_lt_variableBound hc hl

/-! ### The keep pass -/

/-- The clauses of `pre` that Lemma 10 keeps. -/
def keptOf (f pre : CNF) : CNF := pre.filter fun c => !deleted f c

theorem keptOf_snoc (f pre : CNF) (cl : Clause) :
    keptOf f (pre ++ [cl]) = if deleted f cl then keptOf f pre else keptOf f pre ++ [cl] := by
  unfold keptOf; rw [List.filter_append]; cases h : deleted f cl <;> simp [h]

def KeepInv (f : CNF) (c : Config) (pre : CNF) : Prop :=
  c.mem = kpMem (polMc f) (polB f) (keptOf f pre).flatten ∧ c.reg Reg.p = 1 + (pre.flatMap clauseCode).length ∧
    PolRegs f c ∧ c.reg PR.r = pre.countP (deleted f) ∧ c.out = [f.length]

theorem keep_step (f : CNF) (hf : ∀ c ∈ f, c.length = 2 ∨ c.length = 3) :
    ∀ pre cl suf c, pre ++ cl :: suf = f → (fun pre c => KeepInv f c pre) pre c → c.reg Reg.m = suf.length + 1 →
      At c (clauseCode cl ++ suf.flatMap clauseCode) →
      AddrOK (polSpace f) keepBody c ∧
      (fun pre c => KeepInv f c pre) (pre ++ [cl]) (run keepBody c) ∧ (run keepBody c).reg Reg.m = suf.length ∧
        At (run keepBody c) (suf.flatMap clauseCode) := by
  intro pre cl suf c hpre ⟨hm, hp, hR, hr, ho⟩ hmc hAt
  obtain ⟨hB, hBN, hBB⟩ := bodyPre_of hf hpre hR hp hAt
  refine ⟨keepBody_addrOK hB hBB hBN, ?_⟩
  have hclf : cl ∈ f := by rw [← hpre]; simp
  have hcl := hf cl hclf
  have hcounts : ∀ l ∈ cl, CountsAt f c l := fun l hl =>
    countsAt_of f c hR.N (by rw [hm]; exact mcBelow_kp f _) l (vars_lt hclf l hl)
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := keepBody_step f c cl _ hcl hAt hR.k hcounts (M := polMc f)
    (ks := (keptOf f pre).flatten) (by rw [hm, hR.B])
  have hlen : c.reg Reg.p + (clauseCode cl ++ suf.flatMap clauseCode).length ≤ polN f := by
    rw [hp, polN_eq, ← hpre]; simp; omega
  refine ⟨⟨?_, ?_, hR.frame m6, ?_, by rw [m5]; exact ho⟩, by rw [m3, hmc]; rfl, ?_⟩
  · rw [m1, hR.B, keptOf_snoc]; split <;> simp
  · rw [m4, hp]; simp; omega
  · rw [m2, hr, List.countP_append]; simp
  · apply At.advance hAt (by rw [m4])
    intro a ha
    have haN : a < polN f := by omega
    have hB : a < polB f := by unfold polB; omega
    rw [m1, hm, hR.B, kpMem_below _ _ _ hB, kpMem_below _ _ _ hB]

/-! ### The output pass -/

theorem kept_eq (f : CNF) : keptOf f f = kept f := rfl

def OutInv (f : CNF) (c : Config) (pre : CNF) : Prop :=
  c.mem = kpMem (polMc f) (polB f) (kept f).flatten ∧ c.reg Reg.p = 1 + (pre.flatMap clauseCode).length ∧
    PolRegs f c ∧ c.reg PR.r = deletedCount f ∧
    c.out = f.length :: (flipFormula (complemented f) (keptOf f pre)).flatMap clauseCode

theorem out_step (f : CNF) (hf : ∀ c ∈ f, c.length = 2 ∨ c.length = 3) :
    ∀ pre cl suf c, pre ++ cl :: suf = f → (fun pre c => OutInv f c pre) pre c → c.reg Reg.m = suf.length + 1 →
      At c (clauseCode cl ++ suf.flatMap clauseCode) →
      AddrOK (polSpace f) outBody c ∧
      (fun pre c => OutInv f c pre) (pre ++ [cl]) (run outBody c) ∧ (run outBody c).reg Reg.m = suf.length ∧
        At (run outBody c) (suf.flatMap clauseCode) := by
  intro pre cl suf c hpre ⟨hm, hp, hR, hr, ho⟩ hmc hAt
  obtain ⟨hB, hBN, hBB⟩ := bodyPre_of hf hpre hR hp hAt
  refine ⟨outBody_addrOK hB hBB hBN, ?_⟩
  have hclf : cl ∈ f := by rw [← hpre]; simp
  have hcl := hf cl hclf
  have hcounts : ∀ l ∈ cl, CountsAt f c l := fun l hl =>
    countsAt_of f c hR.N (by rw [hm]; exact mcBelow_kp f _) l (vars_lt hclf l hl)
  have hF : ∀ l ∈ cl, complemented f l.var = decide (2 ≤ c.mem (c.reg Reg.B + l.var)) := by
    intro l _
    rw [hm, hR.B, kpMem_at, polMc_B, Nat.zero_add, ← occurrences_eq_count]
    rfl
  obtain ⟨o1, m2, p3, mm4, fr5⟩ := outBody_step f (complemented f) c cl _ hcl hAt hR.k hcounts hF
  have hr' : (run outBody c).reg PR.r = c.reg PR.r :=
    run_reg_frame _ _ _ (by simp +decide [])
  refine ⟨⟨by rw [mm4]; exact hm, ?_, hR.frame fr5, by rw [hr']; exact hr, ?_⟩,
    by rw [m2, hmc]; rfl, ?_⟩
  · rw [p3, hp]; simp; omega
  · rw [o1, ho, keptOf_snoc]
    split <;> simp [flipFormula]
  · exact At.advance hAt (by rw [p3]) (fun a _ => by rw [mm4])

/-! ### The padding -/

theorem padding_succ (base j : Nat) :
    padding base (j + 1) = padding base j ++ [[⟨base + 2 * j, true⟩, ⟨base + 2 * j + 1, true⟩]] := by
  simp [padding, List.range_succ]

def PadInv (O : List Nat) (n : Nat) (j : Nat) (c : Config) : Prop :=
  c.out = O ++ (padding n j).flatMap clauseCode ∧ c.reg PR.w = n + 2 * j ∧ Consts c

theorem pad_step (O : List Nat) (n T : Nat) {S : Nat} :
    ∀ j c, j < T → PadInv O n j c → c.reg PR.r = T - j → AddrOK S padBody c ∧ PadInv O n (j + 1) (run padBody c) ∧
      (run padBody c).reg PR.r + 1 = c.reg PR.r := by
  intro j c hj ⟨ho, hw, hk⟩ hr
  have hone := hk.one
  have htwo := hk.two
  refine ⟨AddrOK.of_memFree rfl, ⟨?_, ?_, hk.frame ?_ ?_ ?_ ?_⟩, ?_⟩
  · simp +decide [padBody, run, ho, hw, hone, htwo, padding_succ, clauseCode, litCode, signCode]
    try omega
  · simp +decide [padBody, run, hw, hone]; try omega
  all_goals (simp +decide [padBody, run, hone, hr]; try omega)

end STACS2027.RAM
