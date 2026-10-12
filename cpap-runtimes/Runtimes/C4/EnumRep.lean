module

public import Runtimes.C4.EnumLoops
public import Outerplanar.RAM.Poly1Sort
import Mathlib.Tactic

/-!
# Phase ENUM, part 3: representation of the report walk, memory steps, the report block

After the generation (`EnumLoops.lean`) and the counting sort of the indices by the first key
component (`EnumScan.lean`), the report walk starts in a configuration `c₁` satisfying
`ScanPre g c₁`: the triples of `l = ins g (peelPos g)` at `gTX`, `gTY`, `gTZ` and the sorted
indices `srtIdx g = P1.bucketIdx (l.map (·.1.1)) N` at `gSRT`, below `F₁ = c₁.reg rFREE`.
Reading the triples through the sorted indices gives `insS g = sortX N l` (`read_srt`, from
`P1.map_bucketIdx`). The walk allocates from `F₁`: the time stamps `STP` (`N` cells at `F₁`),
the list heads `HDS` (`N` cells at `bHDS = F₁ + N`), the node pool `POOL` (`2P` cells at
`bPOOL`; node `i` at `POOL + 2i` holds a centre and the next node) and the cycle array `CYC` (at
`bCYC = POOL + 2P`, four cells per reported cycle, growing with `rFREE`, up to `scanEnd`). There
is no table indexed by key pairs.

* `ERep g c₁ L xc R c`: the 2-paths `L` (a prefix of `insS g`) are inserted, all with first
  component at most `xc`; for every `y < N` with `STP[y] = xc + 1` the list from `HDS[y]` is
  `bucket L (xc, y)` (newest first), and for the other `y` this bucket is empty; the reports
  `R` are stored: `CYC` holds `(R.map (phi g)).flatten`, `gT = |R|`, `rFREE = CYC + 4 |R|`,
  free memory from `rFREE`.
* Memory steps: `EMem.advance` (a larger first component: every stamp is stale),
  `EMem.stamp` (validate the empty list of `y`), `EMem.node` (a new node at the end of the pool
  heads the list of its key), `EMem.emit` (four stores of a canonical cycle).
* The canonical form: `canonP` computes `canon4 a b c d` of the registers `xLa xLb xLc xLd`
  into `xO0 … xO3` by a decision tree mirroring `canon4` (`canonP_outs`); `emit4` stores them
  at `rFREE`.
* The report block `reportB`: with the endpoints `x = xX`, `y = xY`, the centre `z = xZ` and the
  walker node `q = xQ` (centre `z' = M[q]`), it loads the four labels, canonicalizes and
  appends `phi g ((x, y), z, z')` (`reportB_run`, with its address bound).
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo STACS2027.RAM Finset

/-! ### The sorted insertions -/

/-- The first key components of the insertions: the keys of the counting sort. -/
def keysX (g : Graph) : List ℕ := (ins g (peelPos g)).map (·.1.1)

/-- The indices of the insertions sorted stably by the first key component. -/
def srtIdx (g : Graph) : List ℕ := P1.bucketIdx (keysX g) (numV g)

theorem keysX_lt (g : Graph) : ∀ x ∈ keysX g, x < numV g := by
  intro x hx
  simp only [keysX, List.mem_map] at hx
  obtain ⟨e, he, rfl⟩ := hx
  exact lt_of_mem_ins' he

theorem length_keysX (g : Graph) : (keysX g).length = numPaths g (peelPos g) := by
  simp [keysX, numPaths]

theorem length_srtIdx (g : Graph) : (srtIdx g).length = numPaths g (peelPos g) := by
  rw [srtIdx, P1.length_bucketIdx _ _ (keysX_lt g), length_keysX]

/-- Reading a component of the insertions through the sorted indices gives `insS g`. -/
theorem read_srt (g : Graph) (f : (ℕ × ℕ) × ℕ → ℕ) {t : ℕ} (ht : t < numPaths g (peelPos g)) :
    ((ins g (peelPos g)).map f).getD ((srtIdx g).getD t 0) 0 =
      f ((insS g).getD t ((0, 0), 0)) := by
  have h := P1.map_bucketIdx (ins g (peelPos g)) ((0, 0), 0) (·.1.1) f (numV g)
  have h2 := congrArg (fun l => l[t]?) h
  have ht1 : t < (srtIdx g).length := by rw [length_srtIdx]; exact ht
  have ht2 : t < (insS g).length := by rw [length_insS]; exact ht
  simp only [List.getElem?_map] at h2
  change Option.map _ (srtIdx g)[t]? = Option.map f (insS g)[t]? at h2
  rw [List.getElem?_eq_getElem ht1, List.getElem?_eq_getElem ht2] at h2
  simp only [Option.map_some, Option.some.injEq] at h2
  rw [P1.getD_of_lt ht1, P1.getD_of_lt ht2, h2]

theorem srtIdx_lt (g : Graph) {t : ℕ} (ht : t < numPaths g (peelPos g)) :
    (srtIdx g).getD t 0 < numPaths g (peelPos g) := by
  have ht1 : t < (srtIdx g).length := by rw [length_srtIdx]; exact ht
  rw [← length_keysX, P1.getD_of_lt ht1]
  exact P1.lt_of_mem_bucketIdx (List.getElem_mem ht1)

/-- The state at the start of the report walk (after the sort). -/
structure ScanPre (g : Graph) (c : Config) : Prop where
  base : C4Base g c
  n : c.reg gN = numV g
  p : c.reg gP = numPaths g (peelPos g)
  tx : Arr c.mem (c.reg gTX) ((ins g (peelPos g)).map (·.1.1))
  ty : Arr c.mem (c.reg gTY) ((ins g (peelPos g)).map (·.1.2))
  tz : Arr c.mem (c.reg gTZ) ((ins g (peelPos g)).map (·.2))
  srt : Arr c.mem (c.reg gSRT) (srtIdx g)
  below : c.reg gTX + numPaths g (peelPos g) ≤ c.reg rFREE ∧
    c.reg gTY + numPaths g (peelPos g) ≤ c.reg rFREE ∧
    c.reg gTZ + numPaths g (peelPos g) ≤ c.reg rFREE ∧
    c.reg gSRT + numPaths g (peelPos g) ≤ c.reg rFREE

/-! ### Layout and representation -/

section layout

variable (g : Graph) (F : ℕ)

/-- The list heads (`N` cells); the stamps are at `F`. -/
def bHDS : ℕ := F + numV g
/-- The node pool (`2P` cells). -/
def bPOOL : ℕ := F + 2 * numV g
/-- The cycle array. -/
def bCYC : ℕ := bPOOL g F + 2 * numPaths g (peelPos g)
/-- The end of the walk's memory: four cells per four-cycle. -/
def scanEnd : ℕ := bCYC g F + 4 * (cycles g 4).length

theorem scan_layout : bHDS g F = F + numV g ∧ bPOOL g F = F + 2 * numV g ∧
    bCYC g F = bPOOL g F + 2 * numPaths g (peelPos g) ∧
    scanEnd g F = bCYC g F + 4 * (cycles g 4).length := ⟨rfl, rfl, rfl, rfl⟩

end layout

/-- A report `((x, y), z, z')`. -/
abbrev Rpt := (ℕ × ℕ) × ℕ × ℕ

/-- The registers fixed during the report walk (after the allocation). -/
@[mk_iff] structure EGlob (g : Graph) (c₁ c : Config) : Prop where
  n : c.reg gN = numV g
  lb : c.reg gLB = c₁.reg gLB
  tx : c.reg gTX = c₁.reg gTX
  ty : c.reg gTY = c₁.reg gTY
  tz : c.reg gTZ = c₁.reg gTZ
  srt : c.reg gSRT = c₁.reg gSRT
  p : c.reg gP = numPaths g (peelPos g)
  stp : c.reg gSTP = c₁.reg rFREE
  hds : c.reg gHDS = bHDS g (c₁.reg rFREE)
  pool : c.reg gPOOL = bPOOL g (c₁.reg rFREE)
  cyc : c.reg gCYC = bCYC g (c₁.reg rFREE)

/-- The scratch registers of the walk. -/
def WE : List ℕ := [rT, xI, xJ, xA, xB, xV, xW, xX, xY, xZ, xH, xQ, xD, xS, xP, xK, xOv, xDv,
  xOj, xDj, xC, xA1, xLa, xLb, xLc, xLd, xO0, xO1, xO2, xO3, xT4]

theorem EGlob.regIndep (g : Graph) (c₁ : Config) :
    RegIndep (rFREE :: gT :: gNP :: WE) (EGlob g c₁) := by
  indep [eGlob_iff, WE]

/-- The memory during the walk: the inserted 2-paths `L` (first components at most `xc`), the
reports `R`. -/
structure EMem (g : Graph) (c₁ : Config) (L : Ins) (xc : ℕ) (R : List Rpt) (m : ℕ → ℕ) :
    Prop where
  same : SameOn (· < c₁.reg rFREE) c₁.mem m
  len : L.length ≤ numPaths g (peelPos g)
  stp : ∀ y < numV g, m (c₁.reg rFREE + y) ≤ xc + 1
  hd : ∀ y < numV g, m (c₁.reg rFREE + y) = xc + 1 →
    LL m (bPOOL g (c₁.reg rFREE)) (bPOOL g (c₁.reg rFREE) + 2 * L.length)
      (m (bHDS g (c₁.reg rFREE) + y)) (bucket L (xc, y))
  nil : ∀ y < numV g, m (c₁.reg rFREE + y) ≠ xc + 1 → bucket L (xc, y) = []
  le : ∀ e ∈ L, e.1.1 ≤ xc
  cyc : Arr m (bCYC g (c₁.reg rFREE)) (R.map (phi g)).flatten
  zero : ZeroFrom m (bCYC g (c₁.reg rFREE) + 4 * R.length)

/-- The machine has inserted `L` and stored the reports `R`. -/
@[mk_iff] structure ERep (g : Graph) (c₁ : Config) (L : Ins) (xc : ℕ) (R : List Rpt)
    (c : Config) : Prop where
  glob : EGlob g c₁ c
  np : c.reg gNP = 2 * L.length
  t : c.reg gT = R.length
  free : c.reg rFREE = bCYC g (c₁.reg rFREE) + 4 * R.length
  pre : L <+: insS g
  mem : EMem g c₁ L xc R c.mem

theorem ERep.indep (g : Graph) (c₁ : Config) (L : Ins) (xc : ℕ) (R : List Rpt) :
    Indep WE (ERep g c₁ L xc R) := by
  indep [eRep_iff, eGlob_iff, WE]

theorem length_flatten_phi (g : Graph) (R : List Rpt) :
    ((R.map (phi g)).flatten).length = 4 * R.length := by
  induction R with
  | nil => rfl
  | cons r R ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, length_phi, ih,
      List.length_cons]
    ring

/-! ### Memory steps -/

section mem

variable {g : Graph} {c₁ : Config} {L : Ins} {xc : ℕ} {R : List Rpt} {m : ℕ → ℕ}

/-- **Advance** to a larger first component: the stamps of the smaller one are stale, and no
inserted 2-path has the new first component. -/
theorem EMem.advance (h : EMem g c₁ L xc R m) {x : ℕ} (hx : xc ≤ x) : EMem g c₁ L x R m := by
  rcases Nat.eq_or_lt_of_le hx with rfl | hlt
  · exact h
  refine ⟨h.same, h.len, fun y hy => by have := h.stp y hy; omega, fun y hy he => ?_,
    fun y _ _ => ?_, fun e he => by have := h.le e he; omega, h.cyc, h.zero⟩
  · have := h.stp y hy; omega
  · rw [bucket_eq_nil]
    intro z hz
    have := h.le _ hz
    simp only at this
    omega

/-- **Stamp**: the list of `y` (empty for the current first component) becomes valid. -/
theorem EMem.stamp (h : EMem g c₁ L xc R m) {y : ℕ} (hy : y < numV g)
    (hst : m (c₁.reg rFREE + y) ≠ xc + 1) :
    EMem g c₁ L xc R (RAM.upd (RAM.upd m (c₁.reg rFREE + y) (xc + 1))
      (bHDS g (c₁.reg rFREE) + y) 0) := by
  have hL := scan_layout g (c₁.reg rFREE)
  have hlen := h.len
  have hfl := length_flatten_phi g R
  have hb0 := h.nil y hy hst
  refine ⟨(h.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _, hlen, fun y' hy' => ?_,
    fun y' hy' he => ?_, fun y' hy' hne => ?_, h.le, ?_, ?_⟩
  · rw [upd_ne _ _ (by omega)]
    by_cases hyy : y' = y
    · subst hyy; simp
    · rw [upd_ne _ _ (by omega)]; exact h.stp y' hy'
  · rw [upd_ne _ _ (by omega)] at he
    by_cases hyy : y' = y
    · subst hyy
      rw [upd_same, hb0]
      rfl
    · rw [upd_ne _ _ (by omega)] at he
      rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega)]
      exact (((h.hd y' hy' he).upd (by omega)).upd (by omega))
  · rw [upd_ne _ _ (by omega)] at hne
    by_cases hyy : y' = y
    · subst hyy; simp at hne
    · rw [upd_ne _ _ (by omega)] at hne
      exact h.nil y' hy' hne
  · exact (h.cyc.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)
  · exact (h.zero.upd (by omega)).upd (by omega)

/-- **A new node** at the end of the pool (centre `z`, successor the old head) heads the
list of `y` (whose stamp is current). -/
theorem EMem.node (h : EMem g c₁ L xc R m) {y z : ℕ} (hy : y < numV g)
    (hst : m (c₁.reg rFREE + y) = xc + 1) (hlt : L.length < numPaths g (peelPos g)) :
    EMem g c₁ (L ++ [((xc, y), z)]) xc R
      (RAM.upd (RAM.upd (RAM.upd m (bPOOL g (c₁.reg rFREE) + 2 * L.length) z)
        (bPOOL g (c₁.reg rFREE) + 2 * L.length + 1) (m (bHDS g (c₁.reg rFREE) + y)))
        (bHDS g (c₁.reg rFREE) + y) (bPOOL g (c₁.reg rFREE) + 2 * L.length)) := by
  have hL := scan_layout g (c₁.reg rFREE)
  have hfl := length_flatten_phi g R
  have hlen := h.len
  have hm : ∀ q, bPOOL g (c₁.reg rFREE) ≤ q → q < bPOOL g (c₁.reg rFREE) + 2 * L.length →
      RAM.upd (RAM.upd (RAM.upd m (bPOOL g (c₁.reg rFREE) + 2 * L.length) z)
        (bPOOL g (c₁.reg rFREE) + 2 * L.length + 1) (m (bHDS g (c₁.reg rFREE) + y)))
        (bHDS g (c₁.reg rFREE) + y) (bPOOL g (c₁.reg rFREE) + 2 * L.length) q = m q := by
    intro q h1 h2
    rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega), upd_ne _ _ (by omega)]
  have hst' : ∀ y', y' < numV g → RAM.upd (RAM.upd (RAM.upd m (bPOOL g (c₁.reg rFREE) +
      2 * L.length) z) (bPOOL g (c₁.reg rFREE) + 2 * L.length + 1)
      (m (bHDS g (c₁.reg rFREE) + y))) (bHDS g (c₁.reg rFREE) + y)
      (bPOOL g (c₁.reg rFREE) + 2 * L.length) (c₁.reg rFREE + y') = m (c₁.reg rFREE + y') := by
    intro y' hy'
    rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega), upd_ne _ _ (by omega)]
  refine ⟨((h.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _).upd_of_ge (by omega) _,
    by simp; omega, fun y' hy' => by rw [hst' y' hy']; exact h.stp y' hy',
    fun y' hy' he => ?_, fun y' hy' hne => ?_, ?_, ?_, ?_⟩
  · rw [hst' y' hy'] at he
    rw [bucket_snoc, List.length_append, List.length_singleton]
    by_cases hk : y = y'
    · subst hk
      simp only [↓reduceIte, upd_same]
      refine LL.push (h.hd y hy hst) (by omega) hm ?_ ?_ |>.mono (by omega)
      · rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega), upd_same]
      · rw [upd_ne _ _ (by omega), upd_same]
    · have hk' : ((xc, y) : ℕ × ℕ) ≠ (xc, y') := fun e => hk (Prod.mk.inj e).2
      simp only [hk', ↓reduceIte]
      rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega), upd_ne _ _ (by omega)]
      exact ((h.hd y' hy' he).congr hm).mono (by omega)
  · rw [hst' y' hy'] at hne
    have hk : y ≠ y' := fun e => hne (e ▸ hst)
    have hk' : ((xc, y) : ℕ × ℕ) ≠ (xc, y') := fun e => hk (Prod.mk.inj e).2
    rw [bucket_snoc]
    simp only [hk', ↓reduceIte]
    exact h.nil y' hy' hne
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact h.le e he
    · simp only [List.mem_singleton] at he; subst he; exact le_rfl
  · exact ((h.cyc.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)).upd_of_disjoint
      (by omega)
  · exact ((h.zero.upd (by omega)).upd (by omega)).upd (by omega)

/-- Storing a canonical cycle (four cells at `CYC + 4 |R|`). -/
theorem EMem.emit (h : EMem g c₁ L xc R m) (r : Rpt) {o0 o1 o2 o3 : ℕ}
    (ho : phi g r = [o0, o1, o2, o3]) :
    EMem g c₁ L xc (R ++ [r])
      (RAM.upd (RAM.upd (RAM.upd (RAM.upd m (bCYC g (c₁.reg rFREE) + 4 * R.length) o0)
        (bCYC g (c₁.reg rFREE) + 4 * R.length + 1) o1)
        (bCYC g (c₁.reg rFREE) + 4 * R.length + 2) o2)
        (bCYC g (c₁.reg rFREE) + 4 * R.length + 3) o3) := by
  have hL := scan_layout g (c₁.reg rFREE)
  have hlen := h.len
  have hfl := length_flatten_phi g R
  have hst : ∀ y, y < numV g → RAM.upd (RAM.upd (RAM.upd (RAM.upd m
      (bCYC g (c₁.reg rFREE) + 4 * R.length) o0) (bCYC g (c₁.reg rFREE) + 4 * R.length + 1) o1)
      (bCYC g (c₁.reg rFREE) + 4 * R.length + 2) o2) (bCYC g (c₁.reg rFREE) + 4 * R.length + 3) o3
      (c₁.reg rFREE + y) = m (c₁.reg rFREE + y) := by
    intro y hy
    rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega), upd_ne _ _ (by omega),
      upd_ne _ _ (by omega)]
  refine ⟨(((h.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _).upd_of_ge (by omega) _).upd_of_ge
    (by omega) _, hlen, fun y hy => by rw [hst y hy]; exact h.stp y hy, fun y hy he => ?_,
    fun y hy hne => h.nil y hy (by rwa [hst y hy] at hne), h.le, ?_, ?_⟩
  · rw [hst y hy] at he
    rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega), upd_ne _ _ (by omega),
      upd_ne _ _ (by omega)]
    exact ((((h.hd y hy he).upd (by omega)).upd (by omega)).upd (by omega)).upd (by omega)
  · rw [List.map_append, List.flatten_append, List.map_singleton, List.flatten_singleton, ho]
    have h1 := h.cyc.upd_snoc (x := o0) (a := bCYC g (c₁.reg rFREE) + 4 * R.length) (by omega)
    have h2 := h1.upd_snoc (x := o1) (a := bCYC g (c₁.reg rFREE) + 4 * R.length + 1)
      (by simp only [List.length_append, List.length_singleton, hfl]; omega)
    have h3 := h2.upd_snoc (x := o2) (a := bCYC g (c₁.reg rFREE) + 4 * R.length + 2)
      (by simp only [List.length_append, List.length_singleton, hfl]; omega)
    have h4 := h3.upd_snoc (x := o3) (a := bCYC g (c₁.reg rFREE) + 4 * R.length + 3)
      (by simp only [List.length_append, List.length_singleton, hfl]; omega)
    simpa using h4
  · rw [List.length_append, List.length_singleton]
    exact (((((h.zero.mono (by omega)).upd (by omega)).upd (by omega)).upd (by omega)).upd
      (by omega))

end mem

/-! ### The canonical form -/

/-- `xO0 … xO3 := p, q, r, s`. -/
def leaf (p q r s : ℕ) : Stmt :=
  .seq (mov xO0 p) (.seq (mov xO1 q) (.seq (mov xO2 r) (mov xO3 s)))
/-- `a` is the least: order the neighbours `b`, `d`. -/
def cA : Stmt := ifLt xLb xLd (leaf xLa xLb xLc xLd) (leaf xLa xLd xLc xLb)
/-- `b` is the least. -/
def cB : Stmt := ifLt xLa xLc (leaf xLb xLa xLd xLc) (leaf xLb xLc xLd xLa)
/-- `c` is the least. -/
def cC : Stmt := ifLt xLb xLd (leaf xLc xLb xLa xLd) (leaf xLc xLd xLa xLb)
/-- `d` is the least. -/
def cD : Stmt := ifLt xLa xLc (leaf xLd xLa xLb xLc) (leaf xLd xLc xLb xLa)
/-- `c` or `d` is the least. -/
def c34 : Stmt := ifLt xLc xLd cC cD
/-- `a` is not the least. -/
def c234 : Stmt := ifLt xLb xLc (ifLt xLb xLd cB c34) c34
/-- `canon4` of the registers `xLa xLb xLc xLd`, into `xO0 … xO3`. -/
def canonP : Stmt := ifLt xLa xLb (ifLt xLa xLc (ifLt xLa xLd cA c234) c234) c234

theorem canonP_loopFree : LoopFree canonP := by decide +kernel

theorem canonP_wregs : ∀ r ∈ wregs canonP, r ∈ [rT, xO0, xO1, xO2, xO3] := by decide +kernel

theorem canonP_stores : stores canonP = false := by decide +kernel

theorem canonP_writes : writes canonP = false := by decide +kernel

/-- The four output registers. -/
def outs (c : Config) : List ℕ := [c.reg xO0, c.reg xO1, c.reg xO2, c.reg xO3]

theorem leaf_outs {p q r s : ℕ} (hp : p ∈ [xLa, xLb, xLc, xLd]) (hq : q ∈ [xLa, xLb, xLc, xLd])
    (hr : r ∈ [xLa, xLb, xLc, xLd]) (hs : s ∈ [xLa, xLb, xLc, xLd]) (c : Config) :
    outs (run (leaf p q r s) c) = [c.reg p, c.reg q, c.reg r, c.reg s] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq hr hs
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl | rfl <;>
    simp +decide [leaf, run_mov, outs]

theorem outs_ifLt (a b : ℕ) (s u : Stmt) (c : Config) :
    outs (run (ifLt a b s u) c) =
      if c.reg a < c.reg b then outs (run s (c.setReg rT (c.reg b - c.reg a)))
      else outs (run u (c.setReg rT (c.reg b - c.reg a))) := by
  rw [run_ifLt]; split <;> rfl

section canon

variable (c : Config)

theorem cA_outs : outs (run cA c) = if c.reg xLb < c.reg xLd then
    [c.reg xLa, c.reg xLb, c.reg xLc, c.reg xLd] else
    [c.reg xLa, c.reg xLd, c.reg xLc, c.reg xLb] := by
  rw [cA, outs_ifLt, leaf_outs (by decide) (by decide) (by decide) (by decide),
    leaf_outs (by decide) (by decide) (by decide) (by decide)]
  simp +decide

theorem cB_outs : outs (run cB c) = if c.reg xLa < c.reg xLc then
    [c.reg xLb, c.reg xLa, c.reg xLd, c.reg xLc] else
    [c.reg xLb, c.reg xLc, c.reg xLd, c.reg xLa] := by
  rw [cB, outs_ifLt, leaf_outs (by decide) (by decide) (by decide) (by decide),
    leaf_outs (by decide) (by decide) (by decide) (by decide)]
  simp +decide

theorem cC_outs : outs (run cC c) = if c.reg xLb < c.reg xLd then
    [c.reg xLc, c.reg xLb, c.reg xLa, c.reg xLd] else
    [c.reg xLc, c.reg xLd, c.reg xLa, c.reg xLb] := by
  rw [cC, outs_ifLt, leaf_outs (by decide) (by decide) (by decide) (by decide),
    leaf_outs (by decide) (by decide) (by decide) (by decide)]
  simp +decide

theorem cD_outs : outs (run cD c) = if c.reg xLa < c.reg xLc then
    [c.reg xLd, c.reg xLa, c.reg xLb, c.reg xLc] else
    [c.reg xLd, c.reg xLc, c.reg xLb, c.reg xLa] := by
  rw [cD, outs_ifLt, leaf_outs (by decide) (by decide) (by decide) (by decide),
    leaf_outs (by decide) (by decide) (by decide) (by decide)]
  simp +decide

theorem c34_outs : outs (run c34 c) = if c.reg xLc < c.reg xLd then
    (if c.reg xLb < c.reg xLd then [c.reg xLc, c.reg xLb, c.reg xLa, c.reg xLd] else
      [c.reg xLc, c.reg xLd, c.reg xLa, c.reg xLb]) else
    (if c.reg xLa < c.reg xLc then [c.reg xLd, c.reg xLa, c.reg xLb, c.reg xLc] else
      [c.reg xLd, c.reg xLc, c.reg xLb, c.reg xLa]) := by
  rw [c34, outs_ifLt, cC_outs, cD_outs]
  simp +decide

theorem c234_outs : outs (run c234 c) =
    if c.reg xLb < c.reg xLc ∧ c.reg xLb < c.reg xLd then
      (if c.reg xLa < c.reg xLc then [c.reg xLb, c.reg xLa, c.reg xLd, c.reg xLc] else
        [c.reg xLb, c.reg xLc, c.reg xLd, c.reg xLa])
    else if c.reg xLc < c.reg xLd then
      (if c.reg xLb < c.reg xLd then [c.reg xLc, c.reg xLb, c.reg xLa, c.reg xLd] else
        [c.reg xLc, c.reg xLd, c.reg xLa, c.reg xLb])
    else (if c.reg xLa < c.reg xLc then [c.reg xLd, c.reg xLa, c.reg xLb, c.reg xLc] else
      [c.reg xLd, c.reg xLc, c.reg xLb, c.reg xLa]) := by
  rw [c234, outs_ifLt, outs_ifLt, cB_outs, c34_outs, c34_outs, ite_and]
  simp +decide

/-- **The canonical form** computed by `canonP`. -/
theorem canonP_outs :
    outs (run canonP c) = canon4 (c.reg xLa) (c.reg xLb) (c.reg xLc) (c.reg xLd) := by
  rw [canonP, outs_ifLt, outs_ifLt, outs_ifLt, cA_outs, c234_outs, c234_outs, c234_outs]
  simp +decide only [canon4, ite_and, setReg_reg, ↓reduceIte]

end canon

/-! ### The report block -/

/-- Store `xO0 … xO3` at `rFREE`, `rFREE += 4`. -/
def emit4 : Stmt :=
  .seq (.store rFREE xO0) (.seq (inc rFREE) (.seq (.store rFREE xO1) (.seq (inc rFREE)
    (.seq (.store rFREE xO2) (.seq (inc rFREE) (.seq (.store rFREE xO3) (inc rFREE)))))))

/-- The labels of `x = xX`, `z = xZ`, `y = xY` and of the centre `z' = M[xQ]` (into `xW`). -/
def rload : Stmt :=
  .seq (.load xW xQ) (.seq (ld xLa gLB xX) (.seq (ld xLb gLB xZ) (.seq (ld xLc gLB xY)
    (ld xLd gLB xW))))

/-- **Report** the cycle `x – z – y – z'`. -/
def reportB : Stmt := .seq rload (.seq canonP (.seq emit4 (inc gT)))

theorem emit4_run (c : Config) :
    (run emit4 c).mem = RAM.upd (RAM.upd (RAM.upd (RAM.upd c.mem (c.reg rFREE) (c.reg xO0))
      (c.reg rFREE + 1) (c.reg xO1)) (c.reg rFREE + 2) (c.reg xO2)) (c.reg rFREE + 3)
        (c.reg xO3) ∧
      (run emit4 c).reg rFREE = c.reg rFREE + 4 ∧
      ∀ r, r ≠ rT → r ≠ rFREE → (run emit4 c).reg r = c.reg r := by
  refine ⟨?_, ?_, fun r h1 h2 => run_reg_of_not_mem (by decide) (by simp [emit4, wregs, h1, h2]) c⟩
  · simp +decide [emit4, run_inc]
  · simp +decide [emit4, run_inc]

section report

variable {g : Graph} {c₁ : Config} {S : ℕ}

/-- **The report block**: appends `phi g ((x, y), z, z')`, `z' = M[q]`; its addresses are the
node `q`, four labels and four cells at `rFREE`. -/
theorem reportB_run (hP : ScanPre g c₁) (hSp : c₁.reg rFREE ≤ S) {L : Ins} {xc : ℕ}
    {R : List Rpt} {c : Config} (hR : ERep g c₁ L xc R c) {x y z q z' : ℕ} (hx : x < numV g)
    (hy : y < numV g) (hz : z < numV g) (hz' : z' < numV g) (hX : c.reg xX = x)
    (hY : c.reg xY = y) (hZ : c.reg xZ = z) (hQ : c.reg xQ = q) (hq : c.mem q = z')
    (hqS : q < S) (hfr : c.reg rFREE + 4 ≤ S) :
    ERep g c₁ L xc (R ++ [((x, y), z, z')]) (run reportB c) ∧
      (∀ r, r ∉ [rT, rFREE, gT, xW, xLa, xLb, xLc, xLd, xO0, xO1, xO2, xO3] →
        (run reportB c).reg r = c.reg r) ∧
      (∀ a, a < c.reg rFREE → (run reportB c).mem a = c.mem a) ∧ AddrOK S reportB c := by
  have hG := hR.glob
  have hB := hP.base
  have hSm := hR.mem.same
  have hlx := hB.labR hSm hx
  have hly := hB.labR hSm hy
  have hlz := hB.labR hSm hz
  have hlz' := hB.labR hSm hz'
  have hb := hB.bounds
  have hAr : AddrOK S rload c := by addr_ok [rload, hG.lb, hX, hY, hZ, hQ, hq]
  have hF₂ : (run canonP (run rload c)).reg rFREE = c.reg rFREE := by
    rw [run_reg_of_not_mem canonP_loopFree (by decide), run_reg_of_not_mem (by decide) (by decide)]
  have hAe : AddrOK S emit4 (run canonP (run rload c)) := by addr_ok [emit4, hF₂]
  have hAd : AddrOK S reportB c :=
    hAr.seq ((AddrOK.of_memFree rfl).seq (hAe.seq (AddrOK.of_memFree rfl)))
  have hrun : run reportB c = run (inc gT) (run emit4 (run canonP (run rload c))) := by
    simp [reportB]
  have hA₁ := agree_run (W := [xW, xLa, xLb, xLc, xLd]) (s := rload) (by decide) rfl rfl
    (by decide) c
  have hla : (run rload c).reg xLa = labelOf g x := by simp +decide [rload, hG.lb, hX, hlx]
  have hlb : (run rload c).reg xLb = labelOf g z := by simp +decide [rload, hG.lb, hZ, hlz]
  have hlc : (run rload c).reg xLc = labelOf g y := by simp +decide [rload, hG.lb, hY, hly]
  have hld : (run rload c).reg xLd = labelOf g z' := by simp +decide [rload, hG.lb, hQ, hq, hlz']
  generalize run rload c = c₂ at hA₁ hla hlb hlc hld hrun hF₂
  have hR₁ : ERep g c₁ L xc R c₂ := (ERep.indep g c₁ L xc R).mono (by decide) c c₂ hA₁ hR
  have hA₂ := agree_run (W := [rT, xO0, xO1, xO2, xO3]) (s := canonP) canonP_loopFree
    canonP_stores canonP_writes canonP_wregs c₂
  have houts : phi g ((x, y), z, z') = outs (run canonP c₂) := by
    rw [canonP_outs, hla, hlb, hlc, hld]; rfl
  generalize run canonP c₂ = c₃ at hA₂ houts hrun hF₂
  have hR₂ : ERep g c₁ L xc R c₃ := (ERep.indep g c₁ L xc R).mono (by decide) c₂ c₃ hA₂ hR₁
  obtain ⟨hm₃, hF₃, hr₃⟩ := emit4_run c₃
  have hG₃ : EGlob g c₁ (run emit4 c₃) :=
    (EGlob.regIndep g c₁).run_of_sub (by decide) (by decide) hR₂.glob
  generalize run emit4 c₃ = c₄ at hm₃ hF₃ hr₃ hG₃ hrun
  rw [hrun, run_inc (by decide)]
  refine ⟨⟨(EGlob.regIndep g c₁).setReg (by decide) _ ((EGlob.regIndep g c₁).setReg (by decide) _
      hG₃), ?_, ?_, ?_, hR.pre, ?_⟩, fun r hr => ?_, fun a ha => ?_, hAd⟩
  · simp +decide only [setReg_reg, ↓reduceIte]
    rw [hr₃ _ (by decide) (by decide), hR₂.np]
  · simp +decide only [setReg_reg, ↓reduceIte, List.length_append, List.length_singleton]
    rw [hr₃ _ (by decide) (by decide), hR₂.t]
  · simp +decide only [setReg_reg, ↓reduceIte, List.length_append, List.length_singleton]
    rw [hF₃, hR₂.free]
    ring
  · simp only [setReg_mem, hm₃, hR₂.free]
    exact hR₂.mem.emit _ houts
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [setReg_reg, hr.1, hr.2.2.1, ↓reduceIte]
    rw [hr₃ r hr.1 hr.2.1, hA₂.reg r (by simp [hr.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2]),
      hA₁.reg r (by simp [hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1])]
  · have hF₂' : c₃.reg rFREE = c.reg rFREE := by
      rw [hA₂.reg rFREE (by decide), hA₁.reg rFREE (by decide)]
    simp only [setReg_mem, hm₃, hF₂', upd_apply, hA₂.mem, hA₁.mem]
    split_ifs <;> omega

end report

end STACS2027.Runtimes.C4
