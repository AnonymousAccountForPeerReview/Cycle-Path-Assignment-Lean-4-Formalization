module

public import Runtimes.C4.EnumInsert
import Mathlib.Tactic

/-!
# Phase ENUM: the sort, the report walk and the main triple

The program `enum = gen ; srt ; scan` (no table indexed by key pairs):

1. `gen` (`EnumLoops.lean`): the triples `(x, y, z)` of the inserted 2-paths `ins g (peelPos g)`
   at `gTX`, `gTY`, `gTZ` (`P` cells each);
2. `srt`: the stable counting sort `P1.csort` of the indices by the first key component `x`
   (keys `< N`), the sorted indices `srtIdx g` at `gSRT` (`P` cells, after the sort's `2N + 1`
   cells of counters);
3. `scan`: allocate the stamps `STP` and the list heads `HDS` (`N` cells each), the node pool
   (`2P`) and the cycle array; then for every position `t < P` of the sorted order
   (`forUp xI gP scanBody`): read the triple `(insS g)[t]` through `srtIdx g` (`readT`,
   `read_srt`) and insert it (`insertP`), reporting the pairs with the 2-paths already in the
   list of its key. Since the first components are monotone along `insS g` (`sortX_mono`), the
   lists of the previous first component are stale (`EMem.advance`) and the walk reports
   exactly `reports (insS g)` (`scan_spec`).

**`enum_spec`**: from `SizePost g`, `enum` reaches `EnumPost g` (the cycles
`(enumOutS g).flatten` at `gCYC`, a permutation of the four-cycles, `enumOutS_perm`) within
`CE · (m + 1 + t + min (N², ⌈m^{4/3}⌉))` steps (`numPaths_le'`), without output, storing only at
or above the initial `rFREE` `F`, accessing only the addresses below any `S ≥ enumEnd g F`
(`F + 6P + 4N + 1 + 4t`).
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo STACS2027.RAM Finset

/-! ### The program -/

/-- The arguments of the sort: the keys `X`, `P` keys below `N`. -/
def srtArgs : Stmt := .seq (mov P1.rKB gTX) (.seq (mov P1.rKL gP) (mov P1.rKN gN))
/-- **ENUM, part 2: the sort** of the indices by the first key component. -/
def srt : Stmt := .seq srtArgs (.seq P1.csort (mov gSRT P1.rKO))
/-- The allocation of the walk: `STP`, `HDS` (`N` cells), `POOL` (`2P`), `CYC` (growing). -/
def scanAlloc : Stmt :=
  .seq (alloc gSTP gN) (.seq (alloc gHDS gN) (.seq (.add xA gP gP) (.seq (alloc gPOOL xA)
    (.seq (mov gCYC rFREE) (.seq (.const gT 0) (.const gNP 0))))))
/-- Read the `t`-th triple of the sorted order (`t = xI`). -/
def readT : Stmt :=
  .seq (ld xQ gSRT xI) (.seq (ld xX gTX xQ) (.seq (ld xY gTY xQ) (ld xZ gTZ xQ)))
/-- One position of the sorted order. -/
def scanBody : Stmt := .seq readT insertP
/-- **ENUM, part 3: the report walk.** -/
def scan : Stmt := .seq scanAlloc (forUp xI gP scanBody)
/-- **Phase ENUM.** -/
def enum : Stmt := .seq gen (.seq srt scan)

/-- The registers written by the insertion. -/
def WIS : List ℕ := [rT, rFREE, gT, gNP, xX, xY, xC, xH, xQ, xW, xD, xS, xLa, xLb, xLc, xLd, xO0,
  xO1, xO2, xO3]

theorem insertP_wregs : ∀ r ∈ wregs insertP, r ∈ WIS := by decide +kernel

/-- The constant per inserted 2-path of the weight of the walk. -/
def KI : ℕ := 50

/-! ### The walk -/

/-- The first component of the previous position (`0` at the start). -/
def xprev (g : Graph) (t : ℕ) : ℕ := if t = 0 then 0 else ((insS g).getD (t - 1) ((0, 0), 0)).1.1

/-- The invariant of the walk: the first `t` positions are inserted. -/
def SInv (g : Graph) (c₁ : Config) (t : ℕ) (c : Config) : Prop :=
  ERep g c₁ ((insS g).take t) (xprev g t) (reports ((insS g).take t)) c

section

variable {g : Graph} {c₁ : Config} {S : ℕ}

theorem ERep.advance {L : Ins} {xc x : ℕ} {R : List Rpt} {c : Config} (h : ERep g c₁ L xc R c)
    (hx : xc ≤ x) : ERep g c₁ L x R c :=
  ⟨h.glob, h.np, h.t, h.free, h.pre, h.mem.advance hx⟩

theorem xprev_le {t : ℕ} (ht : t < (insS g).length) :
    xprev g t ≤ ((insS g).getD t ((0, 0), 0)).1.1 := by
  unfold xprev
  split_ifs with h0
  · exact Nat.zero_le _
  · rw [P1.getD_of_lt (by omega), P1.getD_of_lt ht]
    have := sortX_mono (N := numV g) (l := ins g (peelPos g)) (t := t - 1)
      (by rw [show t - 1 + 1 = t by omega]; exact ht)
    simpa [insS, show t - 1 + 1 = t by omega] using this

theorem scanBody_spec (hP : ScanPre g c₁) (hSp : scanEnd g (c₁.reg rFREE) ≤ S) {t : ℕ}
    (ht : t < numPaths g (peelPos g)) :
    HTB S scanBody (fun c => SInv g c₁ t c ∧ c.reg xI = t ∧ c.reg gP = numPaths g (peelPos g))
      (fun c => SInv g c₁ (t + 1) c ∧ c.reg xI = t ∧ c.reg gP = numPaths g (peelPos g))
      (wt KW KI ((insS g).take (t + 1)) - wt KW KI ((insS g).take t) - 4) := by
  set e := (insS g).getD t ((0, 0), 0) with he
  have ht' : t < (insS g).length := by rw [length_insS]; exact ht
  have hem : e ∈ insS g := by rw [he, P1.getD_of_lt ht']; exact List.getElem_mem _
  obtain ⟨hxy, hyN, hzN⟩ := lt_of_mem_insS hem
  have hxN : e.1.1 < numV g := by omega
  have htake : (insS g).take (t + 1) = (insS g).take t ++ [((e.1.1, e.1.2), e.2)] := by
    rw [List.take_succ_eq_append_getElem ht', ← P1.getD_of_lt ht' ((0, 0), 0)]
  have hpre : (insS g).take t ++ [((e.1.1, e.1.2), e.2)] <+: insS g := by
    rw [← htake]; exact List.take_prefix _ _
  have hxp : xprev g (t + 1) = e.1.1 := by simp [xprev, he]
  have hL := scan_layout g (c₁.reg rFREE)
  have hpb := hP.below
  -- the read
  have h₁ : HTB S readT (fun c => SInv g c₁ t c ∧ c.reg xI = t ∧ c.reg gP = numPaths g (peelPos g))
      (fun c => (ERep g c₁ ((insS g).take t) e.1.1 (reports ((insS g).take t)) c ∧
        c.reg xX = e.1.1 ∧ c.reg xZ = e.2 ∧ c.reg xY = e.1.2) ∧
        c.reg xI = t ∧ c.reg gP = numPaths g (peelPos g)) 8 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hR, hI, hPr⟩ => ?_
    have hG := hR.glob
    have hsm := hR.mem.same
    have hi := srtIdx_lt g ht
    set i := (srtIdx g).getD t 0 with hi_def
    have hri : c.mem (c₁.reg gSRT + t) = i :=
      ((hP.srt.of_below hsm (by rw [length_srtIdx]; omega)).getD
        (by rw [length_srtIdx]; exact ht))
    have hil : i < (ins g (peelPos g)).length := hi
    have hrx : c.mem (c₁.reg gTX + i) = e.1.1 := by
      rw [(hP.tx.of_below hsm (by simp; unfold numPaths at hpb; omega)).getD (by simpa using hil),
        read_srt g (·.1.1) ht]
    have hry : c.mem (c₁.reg gTY + i) = e.1.2 := by
      rw [(hP.ty.of_below hsm (by simp; unfold numPaths at hpb; omega)).getD (by simpa using hil),
        read_srt g (·.1.2) ht]
    have hrz : c.mem (c₁.reg gTZ + i) = e.2 := by
      rw [(hP.tz.of_below hsm (by simp; unfold numPaths at hpb; omega)).getD (by simpa using hil),
        read_srt g (·.2) ht]
    have hSc : c₁.reg rFREE ≤ S := by unfold scanEnd bCYC bPOOL at hSp; omega
    refine ⟨by addr_ok [readT, hG.srt, hG.tx, hG.ty, hG.tz, hI, hri], ?_⟩
    refine ⟨⟨((ERep.indep g c₁ _ _ _).mono (W' := [xQ, xX, xY, xZ]) (by decide) c _
      (agree_run (by decide) rfl rfl (by decide) c) hR).advance (xprev_le ht'), ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp +decide [readT, hG.srt, hG.tx, hI, hri, hrx]
    · simp +decide [readT, hG.srt, hG.tz, hI, hri, hrz]
    · simp +decide [readT, hG.srt, hG.ty, hI, hri, hry]
    · simp +decide [readT, hI]
    · simp +decide [readT, hPr]
  have h₂ := (insert_spec hP hSp hxN hyN hzN hpre).frameReg
    (F := fun c => c.reg xI = t ∧ c.reg gP = numPaths g (peelPos g))
    ((by indep : RegIndep WIS _).mono insertP_wregs)
  refine (h₁.seq h₂).mono (fun c h => h) (fun c ⟨hR, hI, hPr⟩ =>
    ⟨by unfold SInv; rw [htake, hxp]; exact hR, hI, hPr⟩) ?_
  rw [htake, wt_snoc]
  simp only [KW, KI]
  omega

theorem scanAlloc_spec (hP : ScanPre g c₁) :
    HTB S scanAlloc (fun c => c = c₁) (fun c => SInv g c₁ 0 c ∧ c.reg gP = numPaths g (peelPos g))
      14 := by
  refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => ?_
  subst hc
  have hZ := hP.base.r1.base.free
  have hn := hP.n
  have hp := hP.p
  have hL := scan_layout g (c.reg rFREE)
  simp only [scanAlloc, run_seq', run_alloc (show gN ≠ rT by decide) (show gSTP ≠ gN by decide),
    run_alloc (show gN ≠ rT by decide) (show gHDS ≠ gN by decide), run_add,
    run_alloc (show xA ≠ rT by decide) (show gPOOL ≠ xA by decide),
    run_mov (show rFREE ≠ rT by decide), run_const]
  unfold SInv xprev
  simp only [List.take_zero, reports_nil, ↓reduceIte]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, List.nil_prefix, ?_⟩, ?_⟩
  any_goals (simp +decide [hn, hp, bHDS, bPOOL, bCYC] <;> omega)
  simp only [setReg_mem]
  refine ⟨SameOn.refl _ _, Nat.zero_le _, fun y hy => by rw [hZ.get (by omega)]; omega,
    fun y hy he => by rw [hZ.get (by omega)] at he; omega, fun _ _ _ => rfl,
    fun _ he => absurd he (List.not_mem_nil), arr_nil _ _, hZ.mono (by omega)⟩

theorem scan_spec (hP : ScanPre g c₁) (hSp : scanEnd g (c₁.reg rFREE) ≤ S) :
    HTB S scan (fun c => c = c₁) (SInv g c₁ (numPaths g (peelPos g)))
      (14 + (wt KW KI (insS g) + 3)) := by
  have hl := HTB.forUpTele (S := S) (i := xI) (n := gP) (N := numPaths g (peelPos g))
    (body := scanBody) (SInv g c₁) (fun t => wt KW KI ((insS g).take t)) (by decide) (by decide)
    (by decide) (fun t => (ERep.indep g c₁ _ _ _).mono (by decide))
    (fun t ht => by
      have ht' : t < (insS g).length := by rw [length_insS]; exact ht
      rw [List.take_succ_eq_append_getElem ht', ← (insS g)[t].eta, wt_snoc]
      simp only [KI]
      omega)
    (fun t ht => scanBody_spec hP hSp ht)
  refine ((scanAlloc_spec hP).seq (hl.post fun c ⟨h, _, _⟩ => h)).weaken (le_of_eq ?_)
  have h0 : wt KW KI ((insS g).take 0) = 0 := by simp [wt]
  have hP' : (insS g).take (numPaths g (peelPos g)) = insS g := by
    rw [← length_insS, List.take_length]
  rw [h0, hP']
  omega

/-! ### The sort -/

/-- The end of the sort's memory (after the triples): `OFF` (`N + 1`), `PTR` (`N`), the sorted
indices (`P`). -/
def sortEnd (g : Graph) (F : ℕ) : ℕ := genEnd g F + (numV g + 1) + numV g + numPaths g (peelPos g)

/-- The end of ENUM's memory. -/
def enumEnd (g : Graph) (F : ℕ) : ℕ := scanEnd g (sortEnd g F)

theorem enumEnd_eq (g : Graph) (F : ℕ) :
    enumEnd g F = F + 6 * numPaths g (peelPos g) + 4 * numV g + 1 + 4 * (cycles g 4).length := by
  simp only [enumEnd, scanEnd, bCYC, bPOOL, sortEnd, genEnd]
  ring

theorem srt_wregs : ∀ r ∈ wregs srt, r = rT ∨ r = rFREE ∨ 36 ≤ r := by
  decide +kernel

/-- **The sort**: from the triples of all inserted 2-paths, the sorted indices `srtIdx g` at
`gSRT`; the configuration is a `ScanPre`. -/
theorem srt_spec {c₀ c₂ : Config} (hS : SizePost g c₀) (hG : GRep g c₀ (ins g (peelPos g)) c₂)
    (hreg : ∀ r, r < 36 → r ≠ rT → r ≠ rFREE → c₂.reg r = c₀.reg r)
    (hSp : sortEnd g (c₀.reg rFREE) ≤ S) :
    HTB S srt (fun c => c = c₂)
      (fun c => ScanPre g c ∧ c.reg rFREE = sortEnd g (c₀.reg rFREE) ∧
        SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        (∀ r, r < 36 → r ≠ rT → r ≠ rFREE → c.reg r = c₀.reg r) ∧ c.out = c₂.out)
      (6 + ((28 * numPaths g (peelPos g) + 15 * numV g + 20) + 2)) := by
  show HTB S (.seq srtArgs (.seq P1.csort (mov gSRT P1.rKO))) _ _ _
  have hGG := hG.glob
  have hGM := hG.mem
  have hlen : (keysX g).length = numPaths g (peelPos g) := length_keysX g
  have h₁ : HTB S srtArgs (fun c => c = c₂)
      (fun c => P1.CsIn (keysX g) (numV g) c ∧ c.reg rFREE = genEnd g (c₀.reg rFREE) ∧
        c.mem = c₂.mem) 6 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => ?_
    subst hc
    have hz := hGM.zero
    rw [← hGG.free] at hz
    refine ⟨⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
    · simp +decide [srtArgs, run_mov, hGG.p, hlen]
    · simp +decide [srtArgs, run_mov, hGG.n]
    · simpa +decide [srtArgs, run_mov, hGG.tx, keysX] using hGM.tx
    · simp +decide [srtArgs, run_mov, hGG.tx, hGG.free, hlen, genEnd]; omega
    · simpa +decide [srtArgs, run_mov] using hz
    · simp +decide [srtArgs, run_mov, hGG.free]
    · simp +decide [srtArgs, run_mov]
  have h₂ := P1.csort_specB (S := S) (keysX g) (numV g) (keysX_lt g) (genEnd g (c₀.reg rFREE))
    c₂.mem (by rw [hlen]; exact hSp)
  have h₃ : HTB S (mov gSRT P1.rKO)
      (fun c => (P1.CsOut (keysX g) (numV g) c ∧ ZeroFrom c.mem (c.reg rFREE)) ∧
        SameOn (· < genEnd g (c₀.reg rFREE)) c₂.mem c.mem ∧
        c.reg rFREE = genEnd g (c₀.reg rFREE) + (numV g + 1) + numV g + (keysX g).length ∧
        c.reg P1.rKF = genEnd g (c₀.reg rFREE) ∧
        c.reg P1.rKO = genEnd g (c₀.reg rFREE) + (numV g + 1) + numV g)
      (fun c => Arr c.mem (c.reg gSRT) (srtIdx g) ∧
        c.reg gSRT = genEnd g (c₀.reg rFREE) + (numV g + 1) + numV g ∧
        ZeroFrom c.mem (c.reg rFREE) ∧ SameOn (· < genEnd g (c₀.reg rFREE)) c₂.mem c.mem ∧
        c.reg rFREE = sortEnd g (c₀.reg rFREE)) 2 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨⟨⟨⟨hO, _⟩, _⟩, hZ⟩, hsame, hF, _, hko⟩ => ?_
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa +decide [run_mov, srtIdx] using hO
    · simp +decide [run_mov, hko]
    · simpa +decide [run_mov] using hZ
    · simpa +decide [run_mov] using hsame
    · simp +decide [run_mov, hF, hlen, sortEnd]
  have h := (h₁.seq (h₂.seq h₃)).withFrame c₂
  rw [hlen] at h
  refine (h.pre fun c hc => ⟨hc, hc⟩).post fun c ⟨⟨hA, hsr, hZ, hsame, hF⟩, hfr⟩ => ?_
  have hr : ∀ r, r ∉ wregs srt → c.reg r = c₂.reg r := hfr.reg
  have hgen : c₀.reg rFREE ≤ genEnd g (c₀.reg rFREE) := by unfold genEnd; omega
  have hsame₀ : SameOn (· < c₀.reg rFREE) c₀.mem c.mem :=
    hGM.same.trans (hsame.mono fun a ha => by show a < genEnd g (c₀.reg rFREE); omega)
  have hreg' : ∀ r, r < 36 → r ≠ rT → r ≠ rFREE → c.reg r = c₀.reg r := fun r hr1 hr2 hr3 => by
    rw [hr r fun hm => by rcases srt_wregs r hm with h | h | h <;> omega, hreg r hr1 hr2 hr3]
  have hP := hGG.p
  refine ⟨⟨hS.orient.peel.base.transfer (fun r hr1 hr2 hr3 => hreg' r (by omega) hr2 hr3) hsame₀
      (by rw [hF]; unfold sortEnd; omega) hZ, ?_, ?_, ?_, ?_, ?_, hA, ?_⟩, hF, hsame₀, hreg',
    hfr.out (by decide)⟩
  · rw [hr gN (by decide)]; exact hGG.n
  · rw [hr gP (by decide)]; exact hGG.p
  · rw [hr gTX (by decide), hGG.tx]
    exact hGM.tx.of_below hsame (by simp [genEnd, numPaths]; omega)
  · rw [hr gTY (by decide), hGG.ty]
    exact hGM.ty.of_below hsame (by simp [genEnd, numPaths]; omega)
  · rw [hr gTZ (by decide), hGG.tz]
    exact hGM.tz.of_below hsame (by simp [genEnd, numPaths]; omega)
  · rw [hr gTX (by decide), hr gTY (by decide), hr gTZ (by decide), hGG.tx, hGG.ty, hGG.tz, hF,
      hsr]
    unfold sortEnd genEnd
    omega

/-! ### The main triple -/

theorem enum_wregs : ∀ r ∈ wregs enum, r = rT ∨ r = rFREE ∨ (36 ≤ r ∧ r < 50) ∨
    (100 ≤ r ∧ r < 150) := by decide +kernel

theorem enum_writes : writes enum = false := by decide +kernel

theorem scan_wregs : ∀ r ∈ wregs scan, r = rT ∨ r = rFREE ∨ 36 ≤ r := by decide +kernel

/-- The constant of the running time of ENUM. -/
def CE : ℕ := 4000

/-- **Phase ENUM**: from a `SizePost g` configuration, `enum` stores the reported cycles
`(enumOutS g).flatten` (in labels, four entries per cycle; a permutation of the four-cycles)
at `gCYC` and their number in `gT` (`EnumPost g`), within
`CE · (m + 1 + t + min (N², ⌈m^{4/3}⌉))` steps, without output, storing only at or above the
initial `rFREE` `F`, accessing only the addresses below any `S ≥ enumEnd g F`, and ending with
`rFREE = enumEnd g F`. -/
theorem enum_spec (g : Graph) (c₀ : Config) (hSp : enumEnd g (c₀.reg rFREE) ≤ S) :
    HTB S enum (fun c => SizePost g c ∧ c = c₀)
      (fun c => EnumPost g c ∧ c.out = c₀.out ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        c₀.reg rFREE ≤ c.reg rFREE ∧ c.reg rFREE ≤ enumEnd g (c₀.reg rFREE))
      (CE * (g.length + 1 + (cycles g 4).length + min (numV g * numV g) (pow43 g.length))) := by
  intro c ⟨hS, hc⟩
  subst hc
  have hE := enumEnd_eq g (c.reg rFREE)
  have hgS : genEnd g (c.reg rFREE) ≤ S := by unfold genEnd; omega
  obtain ⟨c₂, t₂, he₂, ⟨hG, hfr₂⟩, ht₂⟩ := gen_spec g c hgS c ⟨hS, rfl⟩
  have hreg₂ : ∀ r, r < 36 → r ≠ rT → r ≠ rFREE → c₂.reg r = c.reg r := fun r hr h1 h2 =>
    hfr₂.reg r fun hm => by rcases gen_wregs r hm with h | h | h | h <;> omega
  have hsS : sortEnd g (c.reg rFREE) ≤ S := by
    simp only [enumEnd, scanEnd, bCYC, bPOOL] at hSp; omega
  obtain ⟨c₃, t₃, he₃, ⟨hP, hF₃, hsame₃, hreg₃, hout₃⟩, ht₃⟩ := srt_spec hS hG hreg₂ hsS c₂ rfl
  have hscS : scanEnd g (c₃.reg rFREE) ≤ S := by rw [hF₃]; exact hSp
  obtain ⟨c₄, t₄, he₄, ⟨hR, hfr₄⟩, ht₄⟩ := ((scan_spec hP hscS).withFrame c₃) c₃ ⟨rfl, rfl⟩
  have hfull : (insS g).take (numPaths g (peelPos g)) = insS g := by
    rw [← length_insS, List.take_length]
  unfold SInv at hR
  rw [hfull] at hR
  have hlen : (enumOutS g).length = (reports (insS g)).length := by simp [enumOutS]
  have hfree := hR.free
  have hL := scan_layout g (c₃.reg rFREE)
  have hrl := length_reports_insS g
  have hreg₄ : ∀ r, r < 36 → r ≠ rT → r ≠ rFREE → c₄.reg r = c.reg r := fun r hr h1 h2 => by
    rw [hfr₄.reg r fun hm => by rcases scan_wregs r hm with h | h | h <;> omega, hreg₃ r hr h1 h2]
  have hc₃ : c.reg rFREE ≤ c₃.reg rFREE := by rw [hF₃]; unfold sortEnd genEnd; omega
  have hsame : SameOn (· < c.reg rFREE) c.mem c₄.mem :=
    hsame₃.trans (hR.mem.same.mono fun a ha => by show a < c₃.reg rFREE; omega)
  have hF4 : c₄.reg rFREE = enumEnd g (c.reg rFREE) - 4 * ((cycles g 4).length -
      (reports (insS g)).length) := by
    rw [hfree, enumEnd, ← hF₃]; simp only [scanEnd]; omega
  refine ⟨c₄, t₂ + (t₃ + t₄), ExecB.seq he₂ (ExecB.seq he₃ he₄), ⟨⟨?_, ?_, ?_, ?_⟩, ?_, hsame,
    by omega, by omega⟩, ?_⟩
  · exact hS.orient.peel.base.transfer (fun r hr h1 h2 => hreg₄ r (by omega) h1 h2) hsame
      (by omega) (by rw [hfree]; exact hR.mem.zero)
  · rw [hR.t, hlen]
  · rw [hR.glob.cyc]; exact hR.mem.cyc
  · rw [hR.glob.cyc, hfree, hlen]
  · rw [hfr₄.out (by decide), hout₃, hfr₂.out gen_writes]
  · -- the bound
    have h4 := numPaths_le' g
    have h1 := numV_le g
    rw [show wt KW KI (insS g) = KW * (reports (insS g)).length + KI * (insS g).length from rfl,
      length_insS, hrl] at ht₄
    simp only [CG, KW, KI, CE] at ht₂ ht₃ ht₄ h4 ⊢
    have := Nat.zero_le (min (numV g * numV g) (pow43 g.length))
    nlinarith

end

end STACS2027.Runtimes.C4
