module

public import ApproximationHardness.RAM.Decode.Program
import Lean.Elab.Tactic.Omega

/-!
# The decoding program: finding the end of the input and filling the tables
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

theorem pathCode_length (p : List Edge) : (pathCode p).length = 1 + 2 * p.length := by
  unfold pathCode
  simp only [List.length_cons]
  induction p with
  | nil => simp
  | cons e p ih => simp [edgeCode] at *; omega

/-! ### Skipping the paths -/

/-- The invariant of the skipping loop: `p` is past the paths of `pre`. -/
def SkipInv (base : Nat) (c0 : Config) (pre : List (List Edge)) (c : Config) : Prop :=
  c.reg Reg.p = base + (pre.flatMap pathCode).length ∧ c.mem = c0.mem ∧ c.out = c0.out ∧
    c.reg Reg.one = 1 ∧
    ∀ r, r ≠ DR.np → r ≠ DR.len → r ≠ Reg.p → r ≠ DR.t → c.reg r = c0.reg r

/-- One path of the skipping loop; it reads the cell `p` (the path's length), inside the input
`[0, base + |code of ps|)`, below `S`. -/
theorem skip_step (base : Nat) (c0 : Config) (ps : List (List Edge)) {S : Nat}
    (hS : base + (ps.flatMap pathCode).length ≤ S) :
    ∀ pre x suf c, pre ++ x :: suf = ps → SkipInv base c0 pre c → c.reg DR.np = suf.length + 1 →
      At c (pathCode x ++ suf.flatMap pathCode) →
      ∃ t c', ExecB S skipPath c t c' ∧ t ≤ size skipPath ∧ SkipInv base c0 (pre ++ [x]) c' ∧
        c'.reg DR.np = suf.length ∧ At c' (suf.flatMap pathCode) := by
  intro pre x suf c hxs ⟨hp, hm, ho, hone, hfr⟩ hnp hAt
  have hlen : (pre.flatMap pathCode).length + (pathCode x).length + (suf.flatMap pathCode).length =
      (ps.flatMap pathCode).length := by rw [← hxs]; simp [List.flatMap_append]; omega
  obtain ⟨t, he, ht⟩ := exec_loopFree (S := S) (s := skipPath) (by simp [skipPath, seqs, LoopFree]) c
    (by have := pathCode_length x; simp +decide [skipPath, run]; omega)
  have hl : c.mem (c.reg Reg.p) = x.length := by have := hAt.head; simpa [pathCode] using this
  have hp' : (run skipPath c).reg Reg.p = c.reg Reg.p + (pathCode x).length := by
    simp +decide [skipPath, run, hone, hl, pathCode_length]; omega
  have hmem : (run skipPath c).mem = c.mem := run_mem_frame _ _ (by decide)
  refine ⟨t, _, he, ht, ⟨?_, by rw [hmem, hm], by rw [run_out_frame _ _ (by decide), ho], ?_, ?_⟩, ?_, ?_⟩
  · rw [hp', hp]; simp [List.flatMap_append]; omega
  · rw [run_reg_frame _ _ _ (by decide)]; exact hone
  · intro r a1 a2 a3 a4
    rw [run_reg_frame _ _ _ (by simp [skipPath, regsW, a1, a2, a3, a4])]; exact hfr r a1 a2 a3 a4
  · simp +decide [skipPath, run, hone, hnp]
  · exact hAt.drop hmem (by rw [hp'])

/-! ### The tables -/

/-- The value of the table cell `E + d`: the block or the offset of vertex `d / 2`. -/
def tabVal (w d : Nat) : Nat := if d % 2 = 0 then (d / 2) / w else (d / 2) % w

/-- The memory with the table filled for the vertices below `X`, above `E`. -/
def tabMem (w E : Nat) (M : Nat → Nat) (X : Nat) (a : Nat) : Nat :=
  if E ≤ a ∧ a < E + 2 * X then tabVal w (a - E) else M a

theorem tabMem_zero (w E : Nat) (M : Nat → Nat) : tabMem w E M 0 = M := by
  funext a; simp [tabMem]; omega

/-- One cell of the table. -/
theorem tabMem_cell (w E : Nat) (M : Nat → Nat) (X : Nat) (j u : Nat) (hw : u < w) (hX : X = j * w + u) :
    tabMem w E M (X + 1) = fun a => if a = E + X + X + 1 then u else if a = E + X + X then j else tabMem w E M X a := by
  funext a
  unfold tabMem tabVal
  by_cases h1 : a = E + X + X + 1
  · subst h1
    simp only [ite_true]
    rw [ite_eq_left (by omega)]
    have : (E + X + X + 1 - E) % 2 = 1 := by omega
    rw [ite_eq_right (by omega), show (E + X + X + 1 - E) / 2 = X by omega, hX]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hw]
  · by_cases h2 : a = E + X + X
    · subst h2
      simp only [h1, ite_false, ite_true]
      rw [ite_eq_left (by omega), ite_eq_left (by omega), show (E + X + X - E) / 2 = X by omega, hX]
      have hw0 : 0 < w := by omega
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw0, Nat.div_eq_of_lt hw, Nat.zero_add]
    · simp only [h1, h2, ite_false]
      by_cases h3 : E ≤ a ∧ a < E + 2 * X
      · rw [ite_eq_left (by omega), ite_eq_left h3]
      · rw [ite_eq_right (by omega), ite_eq_right h3]

/-- The registers the table fill leaves alone. -/
abbrev FillFixed (r : Nat) : Prop := r ≠ DR.nb ∧ r ≠ DR.u ∧ r ≠ DR.ui ∧ r ≠ DR.addr ∧ r ≠ DR.x ∧ r ≠ DR.bi

theorem fillCell_run (c : Config) (w E : Nat) (M : Nat → Nat) (j u : Nat) (hw : u < w)
    (hx : c.reg DR.x = j * w + u) (hbi : c.reg DR.bi = j) (hui : c.reg DR.ui = u) (hE : c.reg DR.E = E)
    (hone : c.reg Reg.one = 1) (hm : c.mem = tabMem w E M (j * w + u)) :
    (run fillCell c).mem = tabMem w E M (j * w + u + 1) ∧ (run fillCell c).reg DR.x = j * w + u + 1 ∧
      (run fillCell c).reg DR.ui = u + 1 ∧ (run fillCell c).reg DR.u = c.reg DR.u - 1 ∧
      (run fillCell c).out = c.out ∧
      ∀ r, r ≠ DR.u → r ≠ DR.addr → r ≠ DR.x → r ≠ DR.ui → (run fillCell c).reg r = c.reg r := by
  refine ⟨?_, ?_, ?_, ?_, run_out_frame _ _ (by decide), ?_⟩
  · rw [tabMem_cell w E M (j * w + u) j u hw rfl]
    funext a
    simp +decide [fillCell, run, hx, hbi, hui, hE, hone, hm]
    try (by_cases h1 : a = E + (j * w + u) + (j * w + u) + 1
         · simp [h1]
         · by_cases h2 : a = E + (j * w + u) + (j * w + u)
           · simp [h2]
           · simp [h1, h2])
  · simp +decide [fillCell, run, hx, hone]
  · simp +decide [fillCell, run, hui, hone]
  · simp +decide [fillCell, run, hone]
  · intro r a1 a2 a3 a4
    exact run_reg_frame _ _ _ (by simp [fillCell, regsW, a1, a2, a3, a4])

/-- The invariant of the fill loop after `j` blocks. -/
structure FillInv (w E : Nat) (M : Nat → Nat) (c0 : Config) (j : Nat) (c : Config) : Prop where
  x : c.reg DR.x = j * w
  bi : c.reg DR.bi = j
  mem : c.mem = tabMem w E M (j * w)
  out : c.out = c0.out
  fixed : ∀ r, FillFixed r → c.reg r = c0.reg r

/-- One block of the tables; it writes the cells `E + 2x`, `E + 2x + 1` of the vertices `x` of block
`j`, below `S` when `(j + 1) w ≤ X` and `E + 2X ≤ S`. -/
theorem fillBlock_exec (w E : Nat) (M : Nat → Nat) (c0 : Config) (_hw : 0 < w) (hwr : c0.reg DR.w = w)
    (hE : c0.reg DR.E = E) (hone : c0.reg Reg.one = 1) (hzero : c0.reg Reg.zero = 0) {S X : Nat}
    (hS : E + X + X ≤ S) (j : Nat) (hjX : j * w + w ≤ X) (c : Config)
    (hI : FillInv w E M c0 j c) (hnb : c.reg DR.nb ≠ 0) :
    ∃ t c', ExecB S fillBlock c t c' ∧ t ≤ 4 + (w * (size fillCell + 1) + 1) + 1 ∧ FillInv w E M c0 (j + 1) c' ∧
      c'.reg DR.nb + 1 = c.reg DR.nb := by
  obtain ⟨hx, hbi, hm, ho, hfix⟩ := hI
  have hw' : c.reg DR.w = w := (hfix _ (by decide)).trans hwr
  have hE' : c.reg DR.E = E := (hfix _ (by decide)).trans hE
  have hone' : c.reg Reg.one = 1 := (hfix _ (by decide)).trans hone
  have hzero' : c.reg Reg.zero = 0 := (hfix _ (by decide)).trans hzero
  let pre := seqs [Stmt.sub DR.nb DR.nb Reg.one, Stmt.add DR.u DR.w Reg.zero, Stmt.const DR.ui 0]
  obtain ⟨t1, e1, ht1⟩ := exec_loopFree (S := S) (s := pre) (by simp [pre, seqs, LoopFree]) c (AddrOK.of_memFree rfl)
  generalize hc1 : run pre c = c1 at e1
  have c1u : c1.reg DR.u = w := by rw [← hc1]; simp +decide [pre, run, hw', hzero']
  have c1ui : c1.reg DR.ui = 0 := by rw [← hc1]; simp +decide [pre, run]
  have c1nb : c1.reg DR.nb + 1 = c.reg DR.nb := by rw [← hc1]; simp +decide [pre, run, hone']; omega
  have c1fr : ∀ r, r ≠ DR.nb → r ≠ DR.u → r ≠ DR.ui → c1.reg r = c.reg r := by
    intro r a b d; rw [← hc1]; simp [pre, run, a, b, d]
  have c1m : c1.mem = c.mem := by rw [← hc1]; rfl
  have c1o : c1.out = c.out := by rw [← hc1]; rfl
  -- the inner loop
  let J : Nat → Config → Prop := fun u d => d.reg DR.x = j * w + u ∧ d.reg DR.ui = u ∧
    d.mem = tabMem w E M (j * w + u) ∧ d.out = c.out ∧
    ∀ r, r ≠ DR.u → r ≠ DR.addr → r ≠ DR.x → r ≠ DR.ui → d.reg r = c1.reg r
  have hstep : ∀ u d, u < w → J u d → d.reg DR.u = w - u →
      ∃ t d', ExecB S fillCell d t d' ∧ t ≤ size fillCell ∧ J (u + 1) d' ∧ d'.reg DR.u + 1 = d.reg DR.u := by
    intro u d hu ⟨dx, dui, dm, dout, dfr⟩ du
    have dbi : d.reg DR.bi = j := by rw [dfr _ (by decide) (by decide) (by decide) (by decide), c1fr _ (by decide)
      (by decide) (by decide), hbi]
    have dE : d.reg DR.E = E := by rw [dfr _ (by decide) (by decide) (by decide) (by decide), c1fr _ (by decide)
      (by decide) (by decide), hE']
    have done' : d.reg Reg.one = 1 := by rw [dfr _ (by decide) (by decide) (by decide) (by decide), c1fr _ (by decide)
      (by decide) (by decide), hone']
    obtain ⟨t, he, ht⟩ := exec_loopFree (S := S) (s := fillCell) (by simp [fillCell, seqs, LoopFree]) d
      (by simp +decide [fillCell, run, dx, dE, done']; omega)
    obtain ⟨m1, m2, m3, m4, m5, m6⟩ := fillCell_run d w E M j u hu dx dbi dui dE done' dm
    refine ⟨t, _, he, ht, ⟨by rw [m2, Nat.add_assoc], m3, by rw [m1, Nat.add_assoc], by rw [m5, dout], fun r a b d' e => by
      rw [m6 r a b d' e, dfr r a b d' e]⟩, by rw [m4]; omega⟩
  obtain ⟨t2, c2, e2, ht2, hJ⟩ := exec_countLoop (a := DR.u) w J (size fillCell) hstep c1
    ⟨by rw [c1fr _ (by decide) (by decide) (by decide), hx]; simp, c1ui, by rw [c1m, hm]; simp,
      c1o, fun r _ _ _ _ => rfl⟩ c1u
  obtain ⟨c2x, -, c2m, c2o, c2fr⟩ := hJ
  obtain ⟨t3, e3, ht3⟩ := exec_loopFree (S := S) (s := Stmt.add DR.bi DR.bi Reg.one) trivial c2 trivial
  refine ⟨t1 + (t2 + t3), _, ExecB.seq e1 (ExecB.seq e2 e3), ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have : size pre = 4 := by simp [pre, size, seqs]
    simp only [size] at ht3; omega
  · simp +decide [run, c2x, Nat.succ_mul]
  · simp +decide [run]
    rw [c2fr _ (by decide) (by decide) (by decide) (by decide), c1fr _ (by decide) (by decide) (by decide),
      hbi, c2fr _ (by decide) (by decide) (by decide) (by decide), c1fr _ (by decide) (by decide) (by decide), hone']
  · simp [run, c2m, Nat.succ_mul]
  · simp [run, c2o, ho]
  · intro r hr
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hr
    simp [run, a6]
    rw [c2fr r a2 a4 a5 a3, c1fr r a1 a2 a3, hfix r ⟨a1, a2, a3, a4, a5, a6⟩]
  · simp +decide [run]
    rw [c2fr _ (by decide) (by decide) (by decide) (by decide)]; exact c1nb

end STACS2027.RAM
