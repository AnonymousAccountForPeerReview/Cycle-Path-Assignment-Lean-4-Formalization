module

public import Runtimes.ConvexQP.EllMag
public import Runtimes.ConvexQP.RAM.VecLin
public import Runtimes.ZeroCostProg
import Mathlib.Tactic

/-!
# Lemma 16 on the RAM: the interfaces between the phases (fixed)

The machine of Lemma 16 runs on the input `zeroCostInput g k` (the graph, `k`, the number `t` of
enumerated `k`-cycles and their vertices; the same input as Corollary 5) and outputs
`D :: W₀ ++ W₁ ++ ⋯ ++ W_{t−1}`, where `(D, [W₀, …, W_{t−1}]) = solveExact g k opts`
(`opts = (cycles g k).map selectedOptions`). It has three parts, written and proved separately
against the predicates of this file:

1. **Parse and constants** (`ParseSpecRamB`): from the initial configuration either `t = 0`
   (then the output is already `[1]` and `reg qT = 0`), or `QIn I` holds for the instance
   `I = ofOpts g k opts`: the constants of `consts`/`Exact.lean` in the registers `qT … qCD` and
   the overlap matrix `H` of `I` in memory (`HMem`).
2. **Phase E** (`PhaseERamB`): from `QIn I` to `QMid I Xs` for the output `Xs` of `ellRun`
   (`ellRun I (consts I.t I.k) = some Xs`), stored flat at `reg qBX`.
3. **Phases K, M, O** (`PhaseKMORamB`): from `QMid I Xs` with `Xs/2^p ∈ 𝒳` and
   `gap(Xs/2^p) ≤ ε²` to the output `outList (I.exactFrom Xs (2^p))`.

The top level is `seq parse (ifz qT skip (seq phaseE phaseKMO))`.

**Space** (time *and* memory polynomial in the input length, no memory
indexed by a vertex label). The specifications are `HTB S` triples (`Outerplanar/RAM/BoundedHT.lean`:
every load and store below `S`), in the shape of `PolyPhaseB` (`Outerplanar/RAM/PolyIface.lean`):
for every bound `S` leaving room for a polynomial allowance above the initial free address, the
phase runs below `S` and ends with the free address within that allowance. The parser starts from
`initial (zeroCostInput g k)` (free address `0`), so its allowance is `C · (|input| + 2)³` itself;
Phases E and K/M/O get `C · (t k + 2)^10` above `reg rFREE`.

**Registers.** The block `450–549` belongs to Lemma 16: the globals `qT … qBX` are `450–462`
(`463–469` reserved), Phase E's scratch is `470–499`, Phases K/M/O's scratch is `500–539`, the
parser's scratch is `540–549` (the parser may also use Corollary 5's block `250–299` and the
sorting front end's registers, `Runtimes/Sort/`). The arithmetic library writes `rT` and
`400–449` (`Arith.arithW`).

**Step bounds** are stated as `C · (t k + 2)^10` for Phases E and K/M/O and
`C · (|input| + 2)^3` for the parser, with constants `C` chosen by the proofs.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-! ### Registers -/

/-- `t`, the number of cycles. -/
abbrev qT : ℕ := 450
/-- `k`. -/
abbrev qK : ℕ := 451
/-- `t k`. -/
abbrev qKT : ℕ := 452
/-- `n = (k − 1) t` (`nDim`). -/
abbrev qN : ℕ := 453
/-- `d = (k + 1) t` (`dimKKT`). -/
abbrev qD : ℕ := 454
/-- `M = 2t + 3kt` (`nRows`). -/
abbrev qM : ℕ := 455
/-- `N` (`iters`). -/
abbrev qIt : ℕ := 456
/-- `p` (`prec`). -/
abbrev qP : ℕ := 457
/-- `E` (`bigE`). -/
abbrev qE : ℕ := 458
/-- `cN` (`cNum`). -/
abbrev qCN : ℕ := 459
/-- `cD` (`cDen`). -/
abbrev qCD : ℕ := 460
/-- The address of the matrix `H`. -/
abbrev qBH : ℕ := 461
/-- The address of the output `Xs` of Phase E. -/
abbrev qBX : ℕ := 462

/-! ### Flat layouts -/

theorem div_lt_of_lt_tk {t k a : ℕ} (h : a < t * k) : a / k < t :=
  Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h)

theorem mod_lt_of_lt_tk {t k a : ℕ} (h : a < t * k) : a % k < k :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero fun hk => by simp [hk] at h)

/-- `X : Fin t → Fin k → ℤ` flattened (entry `c k + j`; `0` outside). -/
def flat {t k : ℕ} (X : Fin t → Fin k → ℤ) (a : ℕ) : ℤ :=
  if h : a < t * k then X ⟨a / k, div_lt_of_lt_tk h⟩ ⟨a % k, mod_lt_of_lt_tk h⟩ else 0

/-- The overlap matrix `H` of `I` on flat indices: `H(ck + j, c'k + j') = |P_{c,j} ∩ P_{c',j'}|`
(`0` outside). -/
def Hflat (I : Inst) (a b : ℕ) : ℤ :=
  if h : a < I.t * I.k ∧ b < I.t * I.k then
    (I.H ⟨a / I.k, div_lt_of_lt_tk h.1⟩ ⟨a % I.k, mod_lt_of_lt_tk h.1⟩
      ⟨b / I.k, div_lt_of_lt_tk h.2⟩ ⟨b % I.k, mod_lt_of_lt_tk h.2⟩ : ℤ)
  else 0

/-- `H` in memory at `b`: a row-major `tk × tk` matrix of signed entries (two cells each), row `a`
at `b + a · 2tk`. -/
def HMem (I : Inst) (m : ℕ → ℕ) (b : ℕ) : Prop :=
  ∀ a < I.t * I.k, SArr m (b + a * (2 * (I.t * I.k))) 2 (I.t * I.k) (Hflat I a)

/-- The size of the block of `H` in cells. -/
def hCells (I : Inst) : ℕ := I.t * I.k * (2 * (I.t * I.k))

/-! ### Flat indices -/

theorem flat_apply {t k : ℕ} (X : Fin t → Fin k → ℤ) (c : Fin t) (j : Fin k) :
    flat X (c * k + j) = X c j := by
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) j.2
  have hlt : (c : ℕ) * k + j < t * k := by
    have := c.2; have := j.2; nlinarith
  have h1 : ((c : ℕ) * k + j) / k = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt j.2, Nat.zero_add]
  have h2 : ((c : ℕ) * k + j) % k = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]
  unfold flat
  rw [dite_eq_left_of_eq_true (eq_true hlt)]
  congr 1 <;> exact Fin.ext (by simp [h1, h2])

theorem Hflat_apply (I : Inst) (c : Fin I.t) (j : Fin I.k) (c' : Fin I.t) (j' : Fin I.k) :
    Hflat I (c * I.k + j) (c' * I.k + j') = I.H c j c' j' := by
  have hk : 0 < I.k := Nat.lt_of_le_of_lt (Nat.zero_le _) j.2
  have hlt : ∀ (c : Fin I.t) (j : Fin I.k), (c : ℕ) * I.k + j < I.t * I.k := fun c j => by
    have := c.2; have := j.2; nlinarith
  have h1 : ∀ (c : Fin I.t) (j : Fin I.k), ((c : ℕ) * I.k + j) / I.k = c := fun c j => by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt j.2, Nat.zero_add]
  have h2 : ∀ (c : Fin I.t) (j : Fin I.k), ((c : ℕ) * I.k + j) % I.k = j := fun c j => by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]
  unfold Hflat
  rw [dite_eq_left_of_eq_true (eq_true ⟨hlt c j, hlt c' j'⟩)]
  congr 2 <;> exact Fin.ext (by simp [h1, h2])

/-- A sum over the flat indices `a < t k` is the double sum over cycles and options. -/
theorem sum_range_flat {t k : ℕ} (f : Fin t → Fin k → ℤ) :
    ∑ a ∈ Finset.range (t * k), flat f a = ∑ c, ∑ j, f c j := by
  rw [Finset.sum_range (fun a => flat f a), ← Fintype.sum_prod_type',
    ← (finProdFinEquiv : Fin t × Fin k ≃ Fin (t * k)).sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  have : ((finProdFinEquiv p : Fin (t * k)) : ℕ) = p.1 * k + p.2 := by
    simp [finProdFinEquiv]; ring
  rw [this, flat_apply]

/-- `H · x` on the flat indices is the path-load vector `L(x)` (`L_eq_H`): the matrix–vector
product of `Vec.lean` with `M = Hflat I`, `x = flat x`. -/
theorem mulVec_Hflat (I : Inst) (x : Fin I.t → Fin I.k → ℤ) (c : Fin I.t) (j : Fin I.k) :
    mulVec (Hflat I) (flat x) (I.t * I.k) (c * I.k + j) = I.L x c j := by
  rw [Inst.L_eq_H, mulVec]
  rw [show (∑ b ∈ Finset.range (I.t * I.k), Hflat I (c * I.k + j) b * flat x b) =
      ∑ b ∈ Finset.range (I.t * I.k), flat (fun c' j' => (I.H c j c' j' : ℤ) * x c' j') b from
    Finset.sum_congr rfl fun b hb => ?_]
  · exact sum_range_flat _
  · have hb' : b < I.t * I.k := Finset.mem_range.mp hb
    have hk : 0 < I.k := Nat.pos_of_ne_zero fun h => by simp [h] at hb'
    have hb2 : b = (b / I.k) * I.k + b % I.k := (Nat.div_add_mod' b I.k).symm
    obtain ⟨c', hc'⟩ : ∃ c' : Fin I.t, (c' : ℕ) = b / I.k := ⟨⟨_, div_lt_of_lt_tk hb'⟩, rfl⟩
    obtain ⟨j', hj'⟩ : ∃ j' : Fin I.k, (j' : ℕ) = b % I.k := ⟨⟨_, Nat.mod_lt _ hk⟩, rfl⟩
    rw [hb2, ← hc', ← hj', flat_apply, flat_apply, Hflat_apply]

/-! ### The states between the phases -/

/-- The constants in the registers `qT … qCD`. -/
def QRegs (I : Inst) (c : Config) : Prop :=
  c.reg qT = I.t ∧ c.reg qK = I.k ∧ c.reg qKT = I.t * I.k ∧ c.reg qN = nDim I.t I.k ∧
    c.reg qD = dimKKT I.t I.k ∧ c.reg qM = nRows I.t I.k ∧ c.reg qIt = iters I.t I.k ∧
    c.reg qP = prec I.t I.k ∧ c.reg qE = bigE I.t I.k ∧ c.reg qCN = cNum I.t I.k ∧
    c.reg qCD = cDen I.t I.k

/-- **Before Phase E**: the constants, `H` at `reg qBH` below the free memory, all memory from
`reg rFREE` on zero, nothing written yet. -/
def QIn (I : Inst) (c : Config) : Prop :=
  QRegs I c ∧ HMem I c.mem (c.reg qBH) ∧ c.reg qBH + hCells I ≤ c.reg rFREE ∧
    ZeroFrom c.mem (c.reg rFREE) ∧ c.out = []

/-- **After Phase E**: as `QIn`, and `Xs` flat (`t k` signed entries, contiguous) at `reg qBX`,
below the free memory. -/
def QMid (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) (c : Config) : Prop :=
  QRegs I c ∧ HMem I c.mem (c.reg qBH) ∧ c.reg qBH + hCells I ≤ c.reg rFREE ∧
    SArr c.mem (c.reg qBX) 2 (I.t * I.k) (flat Xs) ∧
    c.reg qBX + I.t * I.k * 2 ≤ c.reg rFREE ∧
    ZeroFrom c.mem (c.reg rFREE) ∧ c.out = []

/-- The output of the machine for the solution `(D, W)`: `D`, then the weights cycle by cycle. -/
def outList {t k : ℕ} (s : ℕ × (Fin t → Fin k → ℕ)) : List ℕ :=
  s.1 :: (wlists s.2).flatten

/-- The instance of Lemma 16 on the graph `g`. -/
abbrev instOf (g : Graph) (k : ℕ) : Inst := ofOpts g k ((cycles g k).map selectedOptions)

/-! ### The specifications of the three parts (time and space) -/

/-- **The parser within polynomial space** (with the constants): on `zeroCostInput g k` for a
duplicate-free `g`, either there is no cycle and the output is `[1]`, or `QIn (instOf g k)`,
within `C · (|input| + 2)³` steps, by a run that accesses only the addresses below any bound
`S ≥ C · (|input| + 2)³` (the input included), ending with the free address
`reg rFREE ≤ C · (|input| + 2)³`. -/
def ParseSpecRamB (prog : Stmt) : Prop :=
  ∃ C : ℕ, ∀ (g : Graph) (k : ℕ), g.Nodup → ∀ S : ℕ,
    C * ((ZeroCost.zeroCostInput g k).length + 2) ^ 3 ≤ S →
    HTB S prog (fun c => c = initial (ZeroCost.zeroCostInput g k))
      (fun c => (((cycles g k).length = 0 ∧ c.reg qT = 0 ∧ c.out = [1]) ∨
          (0 < (cycles g k).length ∧ QIn (instOf g k) c)) ∧
        c.reg rFREE ≤ C * ((ZeroCost.zeroCostInput g k).length + 2) ^ 3)
      (C * ((ZeroCost.zeroCostInput g k).length + 2) ^ 3)

/-- **Phase E within polynomial space**: it reproduces `ellRun` exactly. From every
`c₀` with `QIn I c₀` and every bound `S`
leaving `C · (t k + 2)^10` cells above `reg rFREE`, Phase E reaches `QMid I Xs` by a run
accessing only addresses below `S`, within `C · (t k + 2)^10` steps, and the free address moves
up by at most `C · (t k + 2)^10`. -/
def PhaseERamB (prog : Stmt) : Prop :=
  ∃ C : ℕ, ∀ (I : Inst), I.Valid → 0 < I.t → ∀ Xs : Fin I.t → Fin I.k → ℤ,
    ellRun I (consts I.t I.k) = some Xs → ∀ (S : ℕ) (c₀ : Config), QIn I c₀ →
    c₀.reg rFREE + C * (I.t * I.k + 2) ^ 10 ≤ S →
    HTB S prog (· = c₀)
      (fun c => QMid I Xs c ∧ c.reg rFREE ≤ c₀.reg rFREE + C * (I.t * I.k + 2) ^ 10)
      (C * (I.t * I.k + 2) ^ 10)

/-- **Phases K, M, O within polynomial space**: they reproduce `Inst.exactFrom`
exactly and write its result. From every `c₀` with `QMid I Xs c₀` and every
bound `S` leaving `C · (t k + 2)^10` cells above `reg rFREE`, the phases write
`outList (I.exactFrom Xs 2^p)` by a run accessing only addresses below `S`, within
`C · (t k + 2)^10` steps, and the free address moves up by at most `C · (t k + 2)^10`. -/
def PhaseKMORamB (prog : Stmt) : Prop :=
  ∃ C : ℕ, ∀ (I : Inst), I.Valid → 0 < I.t → ∀ Xs : Fin I.t → Fin I.k → ℤ,
    I.InX (ptOf Xs (2 ^ prec I.t I.k)) → I.gap (ptOf Xs (2 ^ prec I.t I.k)) ≤ eps I.t I.k ^ 2 →
    ∀ (S : ℕ) (c₀ : Config), QMid I Xs c₀ → c₀.reg rFREE + C * (I.t * I.k + 2) ^ 10 ≤ S →
    HTB S prog (· = c₀)
      (fun c => c.out = outList (I.exactFrom Xs (2 ^ prec I.t I.k)) ∧
        c.reg rFREE ≤ c₀.reg rFREE + C * (I.t * I.k + 2) ^ 10)
      (C * (I.t * I.k + 2) ^ 10)

end STACS2027.Runtimes.QPRam
