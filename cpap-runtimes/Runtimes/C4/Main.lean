module

public import Runtimes.C4.PeelRAM
public import Runtimes.C4.EnumScan
public import Runtimes.C4.Output
public import Outerplanar.RAM.R1
public import Outerplanar.RAM.R0
import Mathlib.Tactic

/-!
# Four-cycle listing on the RAM: the main theorems

The machine `fourCycles = r0 ; (r1 ; peel ; orient ; sizeP ; enum) ; emit`: outerplanar package's R0 (parsing, relabelling, edge deduplication) and R1 (CSR neighbour lists;
its depth-first search is run as well, at cost `O(m)`), then the phases of this package, and
EMIT, which writes the stored cycles. Every phase is specified within a space bound `S`
(`HTB S`, outerplanar package's `Bounded*`): its memory ends at its initial `rFREE` plus its size.

* **`c4Enum_spec`** (subroutine from `C4Base`): `c4Enum = peel ; orient ; sizeP ; enum`
  reaches `EnumPost g` within `C4E · (m + 1 + t + min (N², ⌈m^{4/3}⌉))` steps, without output,
  storing only at or above the initial `rFREE` `F` and accessing only addresses below any
  `S ≥ F + c4Size g` (`c4Size g = 11N + 6|E| + 6P + 4t + 1`, `P` the inserted 2-paths); it
  writes only `rT`, `rFREE`, `30–49` and `100–149` (`c4Enum_wregs`).
* **`c4Sub_spec`** (subroutine from `R0Post`): `c4Sub = r1 ; c4Enum`, the same with
  `CSub` and `S ≥ R1.endL g F + c4Size g`; it writes only `rT`, `rFREE`, `20–49` and
  `100–149` (`c4Sub_wregs`). Afterwards the cycles `(enumOutS g).flatten` (a permutation of
  `cycles g 4`, `enumOutS_perm`; in labels, each cycle canonical: smallest label first, its
  smaller neighbour second) are at `gCYC = 40`, four cells per cycle, their number in
  `gT = 41`, and everything of R0 below the initial `rFREE` (labels, dictionary, input) is
  unchanged.
* **`emit_spec`**: writes `(enumOutS g).flatten` within `28 t + 5` steps.
* **`fourCycles_spec`**: the whole machine, within `CF · (m + 1 + t + min (N², ⌈m^{4/3}⌉))`
  steps and the space `c4Space g = R1.endL g (R0.endR0 g) + c4Size g`, which is at most
  `CS4 · (labelBound g + m + 1 + t + min (N², ⌈m^{4/3}⌉))` (`c4Space_le`).
* **`fourCycles_ram`**: there are a program and a constant `C` such that on every graph `g`
  the machine halts after `T ≤ C · (m + 1 + t + min (N², ⌈m^{4/3}⌉))` steps, accessing only the
  addresses below `C · (labelBound g + m + 1 + t + min (N², ⌈m^{4/3}⌉))` (`RAM.ComputesIn`),
  with output `cs.flatten` for a permutation `cs` of `cycles g 4`;
* **paper forms**: `fourCycles_ram_paper` (`T ≤ C · (min (N² + t, ⌈m^{4/3}⌉ + t) + m + 1)`,
  for every input list `g`, the `m + 1` being the reading of the input) and
  `fourCycles_ram_simple` (for a simple graph given by its edges, each once, smaller end
  first: `T ≤ C' · (1 + min (N² + t, ⌈m^{4/3}⌉ + t))`, since then `m ≤ N²` and
  `m ≤ ⌈m^{4/3}⌉`), with the space bound `labelBound g` plus the time bound. Here `N = numV g`
  (the vertices on an edge), `m = g.length`, `t = (cycles g 4).length`,
  `⌈m^{4/3}⌉ = pow43 m`, `labelBound g = 1 + the largest label` (the dictionary of R0; `N`
  for the labels `0, …, N - 1`).
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo STACS2027.RAM

/-! ### EMIT -/

/-- Write the cycle array: `for i < 4 · gT: write M[gCYC + i]`. -/
def emit : Stmt :=
  .seq (.seq (.add xT4 gT gT) (.add xT4 xT4 xT4)) (forUp xI xT4 (.seq (ld xX gCYC xI) (.write xX)))

section

variable {S : ℕ}

theorem emit_spec (g : Graph) (c₀ : Config) (hSp : c₀.reg rFREE ≤ S) :
    HTB S emit (fun c => EnumPost g c ∧ c = c₀)
      (fun c => c.out = c₀.out ++ (enumOutS g).flatten ∧ c.mem = c₀.mem)
      (28 * (cycles g 4).length + 5) := by
  intro c ⟨hE, hc⟩
  subst hc
  have hlen : (enumOutS g).flatten.length = 4 * (cycles g 4).length := length_flatten_enumOutS g
  have hT := hE.t
  rw [length_enumOutS] at hT
  have hb := hE.below
  rw [length_enumOutS] at hb
  have h₀ : HTB S (.seq (.add xT4 gT gT) (.add xT4 xT4 xT4)) (fun c' => c' = c)
      (fun c' => (c'.mem = c.mem ∧ c'.reg gCYC = c.reg gCYC ∧
        c'.out = c.out ++ (enumOutS g).flatten.take 0) ∧ c'.reg xT4 = 4 * (cycles g 4).length) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c' hc' => by
      subst hc'
      refine ⟨⟨rfl, by simp +decide, by simp⟩, by simp +decide [hT]; ring⟩
  have hl := HTB.forUpC (S := S) (i := xI) (n := xT4) (N := 4 * (cycles g 4).length)
    (body := .seq (ld xX gCYC xI) (.write xX))
    (fun i c' => c'.mem = c.mem ∧ c'.reg gCYC = c.reg gCYC ∧
      c'.out = c.out ++ (enumOutS g).flatten.take i) 3 (by decide) (by decide) (by decide)
    (fun i => (Indep.mem (fun m => m = c.mem)).and ((Indep.reg (W := [xI, rT]) (r := gCYC)
      (by decide) (· = c.reg gCYC)).and (Indep.out (fun o => o = c.out ++
        (enumOutS g).flatten.take i))))
    (fun i hi => HTB.run_le (by decide) (by decide) fun c' ⟨⟨hm, hc, ho⟩, hI, hN⟩ => by
      have hi' : i < (enumOutS g).flatten.length := by omega
      have hget : c'.mem (c'.reg gCYC + c'.reg xI) = (enumOutS g).flatten[i] := by
        rw [hm, hc, hI]; exact hE.cyc.get hi'
      refine ⟨by addr_ok [hc, hI], ⟨by simp [hm], by simp +decide [hc], ?_⟩, by simp +decide [hI],
        by simp +decide [hN]⟩
      simp only [run_seq', run_ld, run_write, emit_out, setReg_reg, ↓reduceIte, setReg_out, ho,
        hget, List.append_assoc]
      rw [List.take_succ_eq_append_getElem hi'])
  obtain ⟨c', t, he, ⟨⟨hm, _, ho⟩, _, _⟩, ht⟩ := (h₀.seq hl) c rfl
  refine ⟨c', t, he, ⟨?_, hm⟩, by omega⟩
  rw [ho, ← hlen, List.take_length]

end

/-! ### The subroutines -/

/-- The four-cycle phases after R0 and R1. -/
def c4Enum : Stmt := .seq peel (.seq orient (.seq sizeP enum))

/-- The four-cycle enumeration after R0: R1 and the four-cycle phases. -/
def c4Sub : Stmt := .seq R1.r1 c4Enum

/-- **The four-cycle machine.** -/
def fourCycles : Stmt := .seq R0.r0 (.seq c4Sub emit)

theorem c4Enum_wregs : ∀ r ∈ wregs c4Enum, r = rT ∨ r = rFREE ∨ (30 ≤ r ∧ r < 50) ∨
    (100 ≤ r ∧ r < 150) := by
  intro r hr
  simp only [c4Enum, wregs_seq, List.mem_append] at hr
  rcases hr with h | h | h | h
  · exact peel_wregs r h
  · rcases orient_wregs r h with h | h | h | h <;> omega
  · rcases size_wregs r h with h | h | h <;> omega
  · rcases enum_wregs r h with h | h | h | h <;> omega

theorem r1_wregs' : ∀ r ∈ wregs R1.r1, r = rT ∨ r = rFREE ∨ (20 ≤ r ∧ r < 30) ∨
    (100 ≤ r ∧ r < 150) := by decide +kernel

theorem c4Sub_wregs : ∀ r ∈ wregs c4Sub, r = rT ∨ r = rFREE ∨ (20 ≤ r ∧ r < 50) ∨
    (100 ≤ r ∧ r < 150) := by
  intro r hr
  simp only [c4Sub, wregs_seq, List.mem_append] at hr
  rcases hr with h | h
  · rcases r1_wregs' r h with h | h | h | h <;> omega
  · rcases c4Enum_wregs r h with h | h | h | h <;> omega

theorem c4Enum_writes : writes c4Enum = false := by
  simp [c4Enum, peel_writes, orient_writes, size_writes, enum_writes]

/-- The memory of the four-cycle phases after R0 and R1: PEEL `6N + 4|E|`, ORIENT `N + 2|E|`,
ENUM `6P + 4N + 1 + 4t` (`P` inserted 2-paths, `t` four-cycles). -/
def c4Size (g : Graph) : ℕ :=
  11 * numV g + 6 * (idEdges g).length + 6 * numPaths g (peelPos g) + 4 * (cycles g 4).length + 1

/-- The constant of `c4Enum`. -/
def C4E : ℕ := 6200

section

variable {S : ℕ}

/-- **The four-cycle phases** (PEEL, ORIENT, SIZE, ENUM) from `C4Base`: the reported cycles
are stored at `gCYC` (`EnumPost g`), within `C4E · (m + 1 + t + min (N², ⌈m^{4/3}⌉))` steps,
without output, storing only at or above the initial `rFREE` `F`, accessing only the addresses
below any `S ≥ F + c4Size g`. -/
theorem c4Enum_spec (g : Graph) (c₀ : Config) (hSp : c₀.reg rFREE + c4Size g ≤ S) :
    HTB S c4Enum (fun c => C4Base g c ∧ c = c₀)
      (fun c => EnumPost g c ∧ c.out = c₀.out ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        c₀.reg rFREE ≤ c.reg rFREE ∧ c.reg rFREE ≤ c₀.reg rFREE + c4Size g)
      (C4E * (g.length + 1 + (cycles g 4).length + min (numV g * numV g) (pow43 g.length))) := by
  intro c ⟨hB, hc⟩
  subst hc
  have h1S : peelEnd g (c.reg rFREE) ≤ S := by unfold peelEnd; unfold c4Size at hSp; omega
  obtain ⟨c₁, t₁, he₁, ⟨hP, ho₁, hS₁, hF₁, hE₁⟩, ht₁⟩ := peel_spec g c h1S c ⟨hB, rfl⟩
  have h2S : orientEnd g (c₁.reg rFREE) ≤ S := by
    unfold orientEnd; unfold peelEnd at hE₁; unfold c4Size at hSp; omega
  obtain ⟨c₂, t₂, he₂, ⟨hO, ho₂, hS₂, hF₂, hE₂⟩, ht₂⟩ := orient_spec g c₁ h2S c₁ ⟨hP, rfl⟩
  obtain ⟨c₃, t₃, he₃, ⟨hZ, ho₃, hm₃, hF₃⟩, ht₃⟩ := size_spec (S := S) g c₂ (by
    unfold orientEnd at hE₂ h2S; omega) c₂ ⟨hO, rfl⟩
  have h4S : enumEnd g (c₃.reg rFREE) ≤ S := by
    rw [enumEnd_eq, hF₃]; unfold orientEnd at hE₂; unfold peelEnd at hE₁; unfold c4Size at hSp
    omega
  obtain ⟨c₄, t₄, he₄, ⟨hE, ho₄, hS₄, hF₄, hE₄⟩, ht₄⟩ := enum_spec g c₃ h4S c₃ ⟨hZ, rfl⟩
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), ExecB.seq he₁ (ExecB.seq he₂ (ExecB.seq he₃ he₄)),
    ⟨hE, by rw [ho₄, ho₃, ho₂, ho₁], ?_, by omega, ?_⟩, ?_⟩
  · have h2 : SameOn (· < c.reg rFREE) c₁.mem c₂.mem := hS₂.mono fun a ha => by
      show a < c₁.reg rFREE; exact lt_of_lt_of_le ha hF₁
    have h4 : SameOn (· < c.reg rFREE) c₂.mem c₄.mem := by
      rw [← hm₃]
      exact hS₄.mono fun a ha => by
        show a < c₃.reg rFREE; rw [hF₃]; exact lt_of_lt_of_le (lt_of_lt_of_le ha hF₁) hF₂
    exact hS₁.trans (h2.trans h4)
  · rw [enumEnd_eq, hF₃] at hE₄; unfold orientEnd at hE₂; unfold peelEnd at hE₁
    unfold c4Size; omega
  · simp only [CP, CO, CS, CE, C4E] at ht₁ ht₂ ht₃ ht₄ ⊢
    have := Nat.zero_le (min (numV g * numV g) (pow43 g.length))
    nlinarith

/-- The constant of `c4Sub`. -/
def CSub : ℕ := 6800

/-- **The four-cycle enumeration as a subroutine** (R1 and the four-cycle phases) from R0's
post: the reported cycles `(enumOutS g).flatten` are stored at `gCYC` (`EnumPost g`), within
`CSub · (m + 1 + t + min (N², ⌈m^{4/3}⌉))` steps, without output, storing only at or above the
initial `rFREE` (so all of R0's memory survives), accessing only the addresses below any
`S ≥ R1.endL g F + c4Size g`; only `rT`, `rFREE`, `20–49` and `100–149` are written
(`c4Sub_wregs`). -/
theorem c4Sub_spec (g : Graph) (c₀ : Config) (hSp : R1.endL g (c₀.reg rFREE) + c4Size g ≤ S) :
    HTB S c4Sub (fun c => R0.R0Post g c ∧ c = c₀)
      (fun c => EnumPost g c ∧ c.out = c₀.out ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        c₀.reg rFREE ≤ c.reg rFREE ∧ c.reg rFREE ≤ R1.endL g (c₀.reg rFREE) + c4Size g)
      (CSub * (g.length + 1 + (cycles g 4).length + min (numV g * numV g) (pow43 g.length))) := by
  intro c ⟨h0, hc⟩
  subst hc
  obtain ⟨c₁, t₁, he₁, ⟨⟨hR1, ho₁, hS₁, hF₁, hE₁⟩, hfr⟩, ht₁⟩ :=
    (R1.r1_spec g c (S := S) (by omega)).withFrame c c ⟨⟨h0.base, rfl⟩, rfl⟩
  have hB : C4Base g c₁ := ⟨hR1⟩
  obtain ⟨c₂, t₂, he₂, ⟨hE, ho₂, hS₂, hF₂, hE₂⟩, ht₂⟩ := c4Enum_spec (S := S) g c₁
    (by rw [hE₁]; exact hSp) c₁ ⟨hB, rfl⟩
  refine ⟨c₂, t₁ + t₂, ExecB.seq he₁ he₂, ⟨hE, by rw [ho₂, ho₁], hS₁.trans (hS₂.mono
    fun a ha => by show a < c₁.reg rFREE; exact lt_of_lt_of_le ha hF₁), by omega,
    by rw [hE₁] at hE₂; exact hE₂⟩, ?_⟩
  simp only [R1.C1, C4E, CSub] at ht₁ ht₂ ⊢
  have := Nat.zero_le (min (numV g * numV g) (pow43 g.length))
  nlinarith

end

/-- `EnumPost` survives a program that writes no register below `50` except `rT` and keeps
the memory. -/
theorem EnumPost.transfer {g : Graph} {c₀ c : Config} (h : EnumPost g c₀)
    (hreg : ∀ r, r < 50 → r ≠ rT → c.reg r = c₀.reg r) (hm : c.mem = c₀.mem) : EnumPost g c := by
  have hF : c.reg rFREE = c₀.reg rFREE := hreg rFREE (by decide) (by decide)
  have hS : SameOn (· < c₀.reg rFREE) c₀.mem c.mem := by rw [hm]; exact SameOn.refl _ _
  have hZ : ZeroFrom c.mem (c.reg rFREE) := by rw [hm, hF]; exact h.base.r1.base.free
  refine ⟨h.base.transfer (fun r hr h1 _ => hreg r (by omega) h1) hS (by omega) hZ, ?_, ?_, ?_⟩
  · rw [hreg gT (by decide) (by decide)]; exact h.t
  · rw [hreg gCYC (by decide) (by decide), hm]; exact h.cyc
  · rw [hreg gCYC (by decide) (by decide), hF]; exact h.below

theorem emit_wregs : ∀ r ∈ wregs emit, r = rT ∨ 100 ≤ r := by decide

/-- The constant of the whole machine. -/
def CF : ℕ := 7200

/-- The memory of the whole machine: R0, R1 and the four-cycle phases. -/
def c4Space (g : Graph) : ℕ := R1.endL g (R0.endR0 g) + c4Size g

/-- The constant of the space bound. -/
def CS4 : ℕ := 160

/-- **The memory is linear** in `labelBound g + m + 1 + t + min (N², ⌈m^{4/3}⌉)`. -/
theorem c4Space_le (g : Graph) :
    c4Space g ≤ CS4 * (labelBound g + g.length + 1 + (cycles g 4).length +
      min (numV g * numV g) (pow43 g.length)) := by
  have h0 := R0.endR0_le g
  have h1 := R1.endL_le g (R0.endR0 g)
  have h2 := numV_le g
  have h3 := length_idEdges_le g
  have h4 := numPaths_le' g
  unfold c4Space c4Size CS4
  omega

/-- **The four-cycle machine**: on `graphInput g` it halts within
`CF · (m + 1 + t + min (N², ⌈m^{4/3}⌉))` steps, accessing only the addresses below any
`S ≥ c4Space g`, with output `(enumOutS g).flatten`, and the cycles are also stored at `gCYC`
(`EnumPost g`). -/
theorem fourCycles_spec (g : Graph) {S : ℕ} (hSp : c4Space g ≤ S) :
    HTB S fourCycles (· = initial (graphInput g))
      (fun c => c.out = (enumOutS g).flatten ∧ EnumPost g c)
      (CF * (g.length + 1 + (cycles g 4).length + min (numV g * numV g) (pow43 g.length))) := by
  intro c hc
  have h0S : R0.endR0 g ≤ S := by
    have := R1.layout_eqs g (R0.endR0 g); unfold c4Space at hSp; omega
  obtain ⟨c₁, t₁, he₁, h0, ht₁⟩ := R0.r0_spec g h0S c hc
  have hfin := h0.fin
  obtain ⟨c₂, t₂, he₂, ⟨hE, ho₂, -, -, hE₂⟩, ht₂⟩ := c4Sub_spec g c₁ (S := S)
    (by rw [hfin]; exact hSp) c₁ ⟨h0, rfl⟩
  obtain ⟨c₃, t₃, he₃, ⟨⟨ho₃, hm₃⟩, hfr⟩, ht₃⟩ := (emit_spec (S := S) g c₂ (by
    rw [hfin] at hE₂; unfold c4Space at hSp; omega)).withFrame c₂ c₂ ⟨⟨hE, rfl⟩, rfl⟩
  refine ⟨c₃, t₁ + (t₂ + t₃), ExecB.seq he₁ (ExecB.seq he₂ he₃), ⟨?_, hE.transfer
    (fun r hr h1 => hfr.reg r fun h => by rcases emit_wregs r h with h | h <;> omega) hm₃⟩, ?_⟩
  · rw [ho₃, ho₂, h0.out, List.nil_append]
  · simp only [R0.C0, CSub, CF] at ht₁ ht₂ ⊢
    have := Nat.zero_le (min (numV g * numV g) (pow43 g.length))
    have : t₃ ≤ 28 * (cycles g 4).length + 5 := ht₃
    nlinarith

/-- **Four-cycle listing on the RAM** (Corollary 3's enumeration step): there are
a program and a constant `C` such that on every graph `g` the machine halts after
`T ≤ C · (m + 1 + t + min (N², ⌈m^{4/3}⌉))` steps (`m = g.length`, `N = numV g`,
`t = (cycles g 4).length`, `⌈m^{4/3}⌉ = pow43 m`), accessing only the memory addresses below
`C · (labelBound g + m + 1 + t + min (N², ⌈m^{4/3}⌉))` (input included), with output
`cs.flatten` for a permutation `cs` of `cycles g 4` (each cycle in its canonical form, labels
of `g`). -/
theorem fourCycles_ram :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ g : Graph,
      ∃ (out : List ℕ) (T : ℕ),
        RAM.ComputesIn prog (RAM.graphInput g) out T
          (C * (labelBound g + g.length + 1 + (cycles g 4).length +
            min (numV g * numV g) (pow43 g.length))) ∧
        T ≤ C * (g.length + 1 + (cycles g 4).length + min (numV g * numV g) (pow43 g.length)) ∧
        ∃ cs : List Cycle, cs.Perm (cycles g 4) ∧ out = cs.flatten := by
  refine ⟨fourCycles, CF + CS4, fun g => ?_⟩
  obtain ⟨out, T, hT, ho, hc⟩ := HTB.computesIn_post (O := fun o => o = (enumOutS g).flatten)
    ((fourCycles_spec g le_rfl).post fun c h => h.1)
  refine ⟨out, T, hc.mono ?_, hT.trans ?_, enumOutS g, enumOutS_perm g, ho⟩
  · exact (c4Space_le g).trans (Nat.mul_le_mul_right _ (by omega))
  · exact Nat.mul_le_mul_right _ (by omega)

/-- **Paper form** (for every input list `g`): `T ≤ C · (min (N² + t, ⌈m^{4/3}⌉ + t) + m + 1)`
steps and the addresses below `C · (labelBound g + min (N² + t, ⌈m^{4/3}⌉ + t) + m + 1)`; the
term `m + 1` is the reading of the input (`g` may repeat edges and contain loops). -/
theorem fourCycles_ram_paper :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ g : Graph,
      ∃ (out : List ℕ) (T : ℕ),
        RAM.ComputesIn prog (RAM.graphInput g) out T
          (C * (labelBound g + min (numV g * numV g + (cycles g 4).length)
            (pow43 g.length + (cycles g 4).length) + g.length + 1)) ∧
        T ≤ C * (min (numV g * numV g + (cycles g 4).length)
          (pow43 g.length + (cycles g 4).length) + g.length + 1) ∧
        ∃ cs : List Cycle, cs.Perm (cycles g 4) ∧ out = cs.flatten := by
  obtain ⟨prog, C, h⟩ := fourCycles_ram
  refine ⟨prog, C, fun g => ?_⟩
  obtain ⟨out, T, hc, hT, hcs⟩ := h g
  refine ⟨out, T, hc.mono (le_of_eq ?_), hT.trans (le_of_eq ?_), hcs⟩
  all_goals rw [Nat.add_min_add_right]; ring

/-- **Paper form for a simple graph** (given by its edges, each once, smaller end first):
`T ≤ C · (1 + min (|V|² + t, ⌈|E|^{4/3}⌉ + t))` steps and the addresses below
`C · (labelBound g + 1 + min (|V|² + t, ⌈|E|^{4/3}⌉ + t))`, with `|V| = numV g`,
`|E| = g.length` (`m ≤ N²` and `m ≤ ⌈m^{4/3}⌉`, `length_le_sq_of_simple`, `le_pow43`). -/
theorem fourCycles_ram_simple :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ g : Graph, g.Nodup → (∀ e ∈ g, e.1 < e.2) →
      ∃ (out : List ℕ) (T : ℕ),
        RAM.ComputesIn prog (RAM.graphInput g) out T
          (C * (labelBound g + 1 + min (numV g * numV g + (cycles g 4).length)
            (pow43 g.length + (cycles g 4).length))) ∧
        T ≤ C * (1 + min (numV g * numV g + (cycles g 4).length)
          (pow43 g.length + (cycles g 4).length)) ∧
        ∃ cs : List Cycle, cs.Perm (cycles g 4) ∧ out = cs.flatten := by
  obtain ⟨prog, C, h⟩ := fourCycles_ram
  refine ⟨prog, 2 * C, fun g hnd hlt => ?_⟩
  obtain ⟨out, T, hc, hT, hcs⟩ := h g
  have h1 := length_le_sq_of_simple g ⟨hnd, hlt⟩
  have h2 := le_pow43 g.length
  have h3 : g.length ≤ min (numV g * numV g) (pow43 g.length) := le_min h1 h2
  rw [Nat.add_min_add_right]
  refine ⟨out, T, hc.mono ?_, hT.trans ?_, hcs⟩
  · have : labelBound g + g.length + 1 + (cycles g 4).length +
        min (numV g * numV g) (pow43 g.length) ≤
        2 * (labelBound g + 1 + (min (numV g * numV g) (pow43 g.length) +
          (cycles g 4).length)) := by omega
    calc C * (labelBound g + g.length + 1 + (cycles g 4).length +
          min (numV g * numV g) (pow43 g.length))
        ≤ C * (2 * (labelBound g + 1 + (min (numV g * numV g) (pow43 g.length) +
          (cycles g 4).length))) := Nat.mul_le_mul_left _ this
      _ = 2 * C * (labelBound g + 1 + (min (numV g * numV g) (pow43 g.length) +
          (cycles g 4).length)) := by ring
  · have : g.length + 1 + (cycles g 4).length + min (numV g * numV g) (pow43 g.length) ≤
        2 * (1 + (min (numV g * numV g) (pow43 g.length) + (cycles g 4).length)) := by omega
    calc C * (g.length + 1 + (cycles g 4).length + min (numV g * numV g) (pow43 g.length))
        ≤ C * (2 * (1 + (min (numV g * numV g) (pow43 g.length) + (cycles g 4).length))) :=
          Nat.mul_le_mul_left _ this
      _ = 2 * C * (1 + (min (numV g * numV g) (pow43 g.length) + (cycles g 4).length)) := by
          ring

end STACS2027.Runtimes.C4
