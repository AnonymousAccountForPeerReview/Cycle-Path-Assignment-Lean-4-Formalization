module

public import ApproximationHardness.RAM.Orient.Out
public import ApproximationHardness.RAM.Decode.Linear
import Lean.Elab.Tactic.Omega

/-!
# The orientation program computes the planar orientation in linear time

`or_computes`: on the input `ramInput f ++ rot`, the program `orProgram` halts with the
orientation bits `orOutput f rot` within `orCost f` steps, accessing only the addresses below
`orSpace f = 2N + 2n + 4 |f.flatten|` (`N = |ramInput f|`, `n = variableBound f`: the per-variable
cells `E + 2v`, `E + 2v + 1` are indexed by variable numbers). `orCost_le`: the time is at most
`orConst · (|ramInput f| + 1)`, linear in the length of the input.

`orientation_linear_time`: for a bounded-occurrence formula `f` and a planar rotation list `rot`
of its incidence graph, the program halts within `orConst · (|input| + 1)` steps, accessing only
the addresses below `4 · (|input| + n + 1)`, and its output, read as bits, is an endpoint
orientation for which the oriented formula graph is planar (`orientationBits_planar`), for every
gadget parameter `k`.
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity Complexity.SAT Complexity.Planar.Comb PlanarAssembly

/-- The step count of the orientation program. -/
def orCost (f : CNF) : Nat :=
  passACost f + size orPre + ((f.map fun cl => orClauseCost cl + 1).sum + 1) + size orOutPre +
    (f.flatten.length * (size orOut + 1) + 1)

theorem orInput_getD_high (f : CNF) (rot : List Nat) (hrot : rot.length ≤ (ramInput f).length) {a : Nat}
    (ha : orE f ≤ a) : (orInput f rot).getD a 0 = 0 := by
  unfold orE at ha
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [orInput]; omega)]
  rfl

theorem orOutput_eq (f : CNF) (rot : List Nat) :
    orOutput f rot = (List.range f.flatten.length).map (bitNat f rot) := by
  unfold orOutput orientationBits bitNat
  rw [List.map_map, occList_length]
  rfl

/-- The orientation program computes the orientation bits within `orCost f` steps and the space
`orSpace f`, when the darts of the rotation list are below `2 |f.flatten|`. -/
theorem or_computes (f : CNF) (hf : ∀ c ∈ f, c.length ≤ 3) (rot : List Nat)
    (hrot : rot.length ≤ (ramInput f).length) (hrv : ∀ x ∈ rot, x < 2 * f.flatten.length) :
    ∃ t, ComputesIn orProgram (orInput f rot) (orOutput f rot) t (orSpace f) ∧ t ≤ orCost f := by
  have hNl := ramInput_length_eq f
  have hNS : (ramInput f).length ≤ orSpace f := by unfold orSpace orB orE; omega
  -- the first pass
  have hc0 : HoldsInput f (initial (orInput f rot)) := fun i hi => orInput_getD_left f rot hi
  obtain ⟨t1, e1, ht1⟩ := sat_passAq f hf hNS _ ⟨hc0, rfl, rfl, rfl⟩
  have spec1 := passAqModel_spec f _ hc0 rfl rfl rfl
  dsimp only at spec1
  obtain ⟨a1m, a1o, a1one, a1zero, a1n, a1N, -, -⟩ := spec1
  generalize hc1 : passAqModel (initial (orInput f rot)) = c1 at e1 a1m a1o a1one a1zero a1n a1N
  have hM1 : ∀ a, c1.mem a = (orInput f rot).getD a 0 := fun a => by rw [a1m]; rfl
  have hm0 : (orInput f rot).getD 0 0 = f.length := by
    rw [orInput_getD_left f rot (by simp [ramInput])]; simp [ramInput]
  -- the layout
  obtain ⟨t2, e2, ht2⟩ := exec_loopFree (S := orSpace f) (s := orPre) (by simp [orPre, seqs, LoopFree]) c1
    (by simp +decide [orPre, run]; omega)
  generalize hc2 : run orPre c1 = c2 at e2
  have a2mem : c2.mem = c1.mem := by rw [← hc2]; exact run_mem_frame _ _ (by decide)
  have a2out : c2.out = [] := by rw [← hc2, run_out_frame _ _ (by decide), a1o]
  have a2fr : ∀ r, r ∉ regsW orPre → c2.reg r = c1.reg r := fun r h => by
    rw [← hc2]; exact run_reg_frame _ _ _ h
  have hL2 : Layout f c2 := by
    refine ⟨by rw [a2fr _ (by decide), a1one], by rw [a2fr _ (by decide), a1zero], ?_, ?_, ?_,
      by rw [a2fr _ (by decide), a1N], by rw [a2fr _ (by decide), a1n], ?_, ?_⟩
    · rw [← hc2]; simp +decide [orPre, run]
    · rw [← hc2]; simp +decide [orPre, run]
    · rw [← hc2]; simp +decide [orPre, run]
    · rw [← hc2]; simp +decide [orPre, run, a1N, orE]; omega
    · rw [← hc2]; simp +decide [orPre, run, a1N, a1n, orB, orE]; omega
  have a2p : c2.reg Reg.p = 1 := by rw [← hc2]; simp +decide [orPre, run]
  have a2m : c2.reg Reg.m = f.length := by
    rw [← hc2]; simp +decide [orPre, run, hM1]; rw [← List.getD_eq_getElem?_getD]; exact hm0
  have a2occ : c2.reg OR.occ = 0 := by rw [← hc2]; simp +decide [orPre, run]
  -- the clause pass
  have hEB : orE f ≤ orB f := by unfold orB; omega
  have hI2 : ClauseInv f rot [] c2 := by
    refine ⟨hL2, ⟨fun a _ => by rw [a2mem, hM1], fun v _ => ?_, fun v _ => ?_, fun i hi => absurd hi (by simp),
      fun a ha => ?_⟩, by rw [a2occ]; rfl, by rw [a2p]; rfl, a2out⟩
    · rw [a2mem, hM1, orInput_getD_high f rot hrot (by omega)]; simp
    · rw [a2mem, hM1, orInput_getD_high f rot hrot (by omega)]; simp [posCode]
    · have : orB f + 4 * ([] : List Literal).length = orB f := by simp
      rw [a2mem, hM1, orInput_getD_high f rot hrot (by omega)]
  have hAt2 : At c2 (f.flatMap clauseCode) := by
    intro i hi
    rw [a2mem, hM1, a2p, orInput_getD_left f rot (by
      rw [show ramInput f = f.length :: f.flatMap clauseCode from rfl, List.length_cons]; omega)]
    simp [ramInput, Nat.add_comm 1 i]
  obtain ⟨t3, c3, e3, ht3, hI3⟩ := exec_listPass clauseCode f (cnt := Reg.m) (body := orClause)
    (ClauseInv f rot) orClauseCost
    (fun pre cl suf c hxs hI hm hAt => orClause_step f rot pre suf cl c hxs hI hm hAt (Nat.le_refl _))
    c2 hI2 a2m hAt2
  obtain ⟨c3L, c3M, c3occ, -, c3out⟩ := hI3
  -- the output pass
  obtain ⟨t4, e4, ht4⟩ := exec_loopFree (S := orSpace f) (s := orOutPre) (by simp [orOutPre, seqs, LoopFree]) c3
    (AddrOK.of_memFree rfl)
  generalize hc4 : run orOutPre c3 = c4 at e4
  have a4mem : c4.mem = c3.mem := by rw [← hc4]; exact run_mem_frame _ _ (by decide)
  have a4out : c4.out = [] := by rw [← hc4, run_out_frame _ _ (by decide), c3out]
  have a4fr : ∀ r, r ∉ regsW orOutPre → c4.reg r = c3.reg r := fun r h => by
    rw [← hc4]; exact run_reg_frame _ _ _ h
  have hL4 : Layout f c4 := c3L.frame (fun r hr => a4fr r (by revert r; decide))
  have a4cnt : c4.reg OR.cnt = f.flatten.length := by
    rw [← hc4]; simp +decide [orOutPre, run, c3occ, c3L.zero]
  have a4i : c4.reg OR.i = 0 := by rw [← hc4]; simp +decide [orOutPre, run]
  obtain ⟨t5, c5, e5, ht5, hI5⟩ := exec_countLoop (a := OR.cnt) (body := orOut) f.flatten.length
    (OrOutInv f rot c3.mem) (size orOut) (orOut_step f rot hrot c3.mem c3M (Nat.le_refl _) hrv) c4
    ⟨hL4, a4mem, a4i, by rw [a4out]; rfl⟩ a4cnt
  refine ⟨t1 + (t2 + (t3 + (t4 + t5))), ⟨c5, ?_, ?_⟩, ?_⟩
  · exact ExecB.seq e1 (ExecB.seq e2 (ExecB.seq e3 (ExecB.seq e4 e5)))
  · rw [hI5.out, orOutput_eq]
  · unfold orCost; omega

/-! ### The linear bound -/

/-- The step constant of the orientation program. -/
def orConst : Nat :=
  size passApre + clauseACost + size passApost + size orPre + size orClausePre + size orLit + size orOutPre +
    size orOut + 10

theorem orClause_sum (f : CNF) :
    (f.map fun cl => orClauseCost cl + 1).sum =
      f.length * (size orClausePre + 2) + f.flatten.length * (size orLit + 1) := by
  induction f with
  | nil => simp
  | cons c f ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [orClauseCost, List.length_cons, List.flatten_cons, List.length_append, Nat.succ_mul, Nat.add_mul]
    omega

theorem orCost_le (f : CNF) : orCost f ≤ orConst * ((ramInput f).length + 1) := by
  have hNl := ramInput_length_eq f
  unfold orCost passACost
  rw [orClause_sum, hNl]
  have hK1 : size passApre + size passApost + size orPre + size orOutPre + 3 ≤ orConst := by unfold orConst; omega
  have hK2 : clauseACost + 1 + (size orClausePre + 2) ≤ orConst := by unfold orConst; omega
  have hK3 : size orLit + 1 + (size orOut + 1) ≤ orConst := by unfold orConst; omega
  generalize orConst = K at *
  generalize f.length = m
  generalize f.flatten.length = M
  have p1 : m * (clauseACost + 1) + m * (size orClausePre + 2) ≤ m * K := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hK2
  have p2 : M * (size orLit + 1) + M * (size orOut + 1) ≤ M * K := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hK3
  have p3 : K * (1 + m + 2 * M + 1) = K + m * K + 2 * (M * K) + K := by
    rw [Nat.mul_comm K]; simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  rw [p3]
  omega

/-- The orientation bits, read back from the output numbers. -/
theorem orOutput_bits (f : CNF) (rot : List Nat) :
    (orOutput f rot).map (fun x => x == 1) = orientationBits f (rotFun rot) := by
  unfold orOutput
  rw [List.map_map]
  conv => rhs; rw [← List.map_id (orientationBits f (rotFun rot))]
  apply List.map_congr_left
  intro b _
  cases b <;> rfl

/-- **The planar orientation in linear time.** For a bounded-occurrence formula `f` and a planar
rotation list `rot` of its incidence graph, the RAM program `orProgram` halts on
`ramInput f ++ rot` within `orConst · (|input| + 1)` steps, accessing only the addresses below
`4 · (|input| + n + 1)` (`n = variableBound f`), and its output, read as bits, is an endpoint
orientation for which the oriented formula graph is planar, for every `k`. -/
theorem orientation_linear_time (k : Nat) {f : CNF} (hf : BoundedOccurrence f) {rot : List Nat}
    (h : IsPlanarRotation f rot) :
    ∃ t, ComputesIn orProgram (orInput f rot) (orOutput f rot) t
        (4 * ((orInput f rot).length + variableBound f + 1)) ∧
      t ≤ orConst * ((orInput f rot).length + 1) ∧
      PlanarGraph (orientedFormulaGraph (choicesOfBits f ((orOutput f rot).map fun x => x == 1)) k f) := by
  have hf3 : ∀ c ∈ f, c.length ≤ 3 := fun c hc => by rcases hf.1 c hc with h | h <;> omega
  have h3 := ramInput_length_eq f
  have hIG : (incidenceGraph f).length = f.flatten.length := by
    have h1 := placed_occurrence_count f
    have h2 := occList_length f
    unfold occList at h2
    omega
  have hrot : rot.length ≤ (ramInput f).length := by
    obtain ⟨-, -, -, -, hl, -⟩ := h
    omega
  have hrv : ∀ x ∈ rot, x < 2 * f.flatten.length := by
    obtain ⟨G, -, -, -, hl, hnode⟩ := h
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := hnode ⟨i, by omega⟩
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at this
    rw [this, ← hIG]
    exact (G.node _).isLt
  obtain ⟨t, hc, ht⟩ := or_computes f hf3 rot hrot hrv
  have hS : orSpace f ≤ 4 * ((orInput f rot).length + variableBound f + 1) := by
    have : (ramInput f).length ≤ (orInput f rot).length := by simp [orInput]
    unfold orSpace orB orE; omega
  refine ⟨t, hc.mono hS, ?_, ?_⟩
  · have := orCost_le f
    have hl : (ramInput f).length ≤ (orInput f rot).length := by simp [orInput]
    have := Nat.mul_le_mul_left orConst (Nat.add_le_add_right hl 1)
    omega
  · rw [orOutput_bits]
    exact orientationBits_planar k hf h

end STACS2027.RAM
