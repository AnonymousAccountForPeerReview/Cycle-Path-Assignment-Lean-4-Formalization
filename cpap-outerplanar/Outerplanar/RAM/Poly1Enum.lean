module

public import Outerplanar.RAM.Poly1Csr
import Mathlib.Tactic

/-!
# Phase P1 of the polygon solver, stage B: the enumeration of the segments

Stage B (`stageB`) scans the sorted neighbour lists (stage A): for each position `a` and each
neighbour `b` of `a` with `a + 2 ≤ b` it appends the segment `(a, b)` to four arrays: its ends
(`rSEA`, `rSEB`), the face vertex after `a` (`predOf`, `rSEP`: the previous neighbour of `a`,
`predNb_getElem`) and its size `b - a` (`rSEK`). It also stores, for every position `x`, its
largest neighbour `lastNb x` (`rLAST`) and the enumeration id of the pair `(x, lastNb x)`
(`rLSEG`: the number of segments so far if it is a segment, `enumId_last`, else `0`). The
enumeration order is `segEnum` (`enumPre`: the segments found so far).

Layout from the free address `F₀`: `SEA`, `SEB`, `SEP`, `SEK` (`|pg|` cells each), `LAST`,
`LSEG` (`n` cells each); the stage ends at `F₀ + 4 |pg| + 2 n` (`enEnd`). Cost `O(n + |pg|)`
(`stageB_spec`).
-/

@[expose] public section

namespace STACS2027.RAM.P1

open STACS2027.Poly

/-! ### Registers and program -/

/-- Base of the first ends of the enumerated segments. -/
abbrev rSEA : ℕ := 91
/-- Base of the second ends of the enumerated segments. -/
abbrev rSEB : ℕ := 92
/-- Base of the face vertices after the first ends. -/
abbrev rSEP : ℕ := 93
/-- Base of the enumeration ids of the pairs `(x, lastNb x)` (`n` cells). -/
abbrev rLSEG : ℕ := 94
/-- Base of the sizes `b - a`. -/
abbrev rSEK : ℕ := 95
/-- Base of the largest neighbours (`n` cells). -/
abbrev rLAST : ℕ := 96
/-- The current position `a`. -/
abbrev rEA : ℕ := 124
/-- The start of the neighbour list of `a`. -/
abbrev rELo : ℕ := 125
/-- The end of the neighbour list of `a`. -/
abbrev rEHi : ℕ := 126
/-- The previous neighbour of `a` (or `a`). -/
abbrev rEPrev : ℕ := 127
/-- `a + 2`. -/
abbrev rEA2 : ℕ := 128
/-- The position in the neighbour lists. -/
abbrev rEJ : ℕ := 129
/-- The current neighbour `b`. -/
abbrev rEB : ℕ := 130
/-- Temporary. -/
abbrev rEX : ℕ := 131
/-- `a + 1`. -/
abbrev rEA1 : ℕ := 133

/-- Allocation of the four segment arrays (`|pg|` cells each), `LAST` and `LSEG` (`n` cells
each). -/
def enAlloc : Stmt :=
  .seq (alloc rSEA gPE) (.seq (alloc rSEB gPE) (.seq (alloc rSEP gPE) (.seq (alloc rSEK gPE)
    (.seq (alloc rLAST gPN) (.seq (alloc rLSEG gPN) (.const gNS 0))))))
/-- Append the segment `(a, b)`. -/
def enPush : Stmt :=
  .seq (st rSEA gNS rEA) (.seq (st rSEB gNS rEB) (.seq (st rSEP gNS rEPrev)
    (.seq (.sub rEX rEB rEA) (.seq (st rSEK gNS rEX) (inc gNS)))))
/-- One neighbour `b` of `a`. -/
def enInner : Stmt := .seq (ld rEB rNB rEJ) (.seq (ifLe rEA2 rEB enPush .skip) (mov rEPrev rEB))
/-- Before the neighbours of `a`. -/
def enPre : Stmt :=
  .seq (ld rELo rOFF rEA) (.seq (addc rEA1 rEA 1) (.seq (ld rEHi rOFF rEA1)
    (.seq (mov rEPrev rEA) (addc rEA2 rEA 2))))
/-- The enumeration id of `(a, prev)`: the number of segments so far if `a + 2 ≤ prev`. -/
def enLseg : Stmt := ifLe rEA2 rEPrev (mov rEX gNS) (.const rEX 0)
/-- After the neighbours of `a`: `LAST[a] := prev`, `LSEG[a] :=` the id of `(a, prev)`. -/
def enPost : Stmt := .seq (st rLAST rEA rEPrev) (.seq enLseg (st rLSEG rEA rEX))
/-- One position `a`. -/
def enOuter : Stmt := .seq enPre (.seq (forRange rEJ rELo rEHi enInner) enPost)
/-- **Stage B**: the enumeration. -/
def stageB : Stmt := .seq enAlloc (forUp rEA gPN enOuter)

/-- The end of the arrays of stage B, from the free address `F₀`. -/
def enEnd (pg : Graph) (n F₀ : ℕ) : ℕ := F₀ + 4 * pg.length + 2 * n

/-- The registers written by stage B. -/
abbrev WB : List ℕ := wregs stageB

/-- **The enumerated segments** (the result of stage B). -/
def EnumSt (pg : Graph) (n : ℕ) (c : Config) : Prop :=
  c.reg gNS = (segEnum pg n).length ∧
    ArrAt rSEA ((segEnum pg n).map Prod.fst) c ∧ ArrAt rSEB ((segEnum pg n).map Prod.snd) c ∧
    ArrAt rSEP ((segEnum pg n).map (predOf pg n)) c ∧ ArrAt rSEK ((segEnum pg n).map sizeOf) c ∧
    TabAt rLAST n (lastNb pg n) c ∧ TabAt rLSEG n (fun x => enumId pg n (x, lastNb pg n x)) c

theorem stable_enumSt {pg : Graph} {n : ℕ} {W : List ℕ}
    (h : gNS ∉ W ∧ rSEA ∉ W ∧ rSEB ∉ W ∧ rSEP ∉ W ∧ rSEK ∉ W ∧ rLAST ∉ W ∧ rLSEG ∉ W) :
    Stable W (EnumSt pg n) :=
  (Stable.regEq h.1 _).and ((Stable.arrAt h.2.1 _).and ((Stable.arrAt h.2.2.1 _).and
    ((Stable.arrAt h.2.2.2.1 _).and ((Stable.arrAt h.2.2.2.2.1 _).and
    ((Stable.tabAt h.2.2.2.2.2.1 _).and (Stable.tabAt h.2.2.2.2.2.2 _))))))

variable {pg : Graph} {n : ℕ} {S : ℕ}

/-! ### The state of the enumeration -/

/-- The registers fixed during the scan (layout: the four arrays, then `LAST` and `LSEG`, from
`F₀`). -/
@[mk_iff] structure EnGlob (pg : Graph) (n F₀ : ℕ) (c : Config) : Prop where
  pn : c.reg gPN = n
  pe : c.reg gPE = pg.length
  sea : c.reg rSEA = F₀
  seb : c.reg rSEB = F₀ + pg.length
  sep : c.reg rSEP = F₀ + 2 * pg.length
  sek : c.reg rSEK = F₀ + 3 * pg.length
  last : c.reg rLAST = F₀ + 4 * pg.length
  lseg : c.reg rLSEG = F₀ + 4 * pg.length + n
  free : c.reg rFREE = F₀ + 4 * pg.length + 2 * n
  bnb : c.reg rNB + (nbCat pg n).length ≤ F₀
  boff : c.reg rOFF + (n + 1) ≤ F₀

/-- The memory during the scan, after the segments `E` and the positions below `a`. -/
structure EnMem (pg : Graph) (n F₀ : ℕ) (m₀ : ℕ → ℕ) (nb off : ℕ) (E : List (ℕ × ℕ)) (a : ℕ)
    (m : ℕ → ℕ) : Prop where
  nbc : Arr m nb (nbCat pg n)
  offs : Tab m off (n + 1) (nbOff pg n)
  sa : Arr m F₀ (E.map Prod.fst)
  sb : Arr m (F₀ + pg.length) (E.map Prod.snd)
  sp : Arr m (F₀ + 2 * pg.length) (E.map (predOf pg n))
  sk : Arr m (F₀ + 3 * pg.length) (E.map sizeOf)
  last : Tab m (F₀ + 4 * pg.length) a (lastNb pg n)
  lseg : Tab m (F₀ + 4 * pg.length + n) a (fun x => enumId pg n (x, lastNb pg n x))
  zero : ZeroFrom m (F₀ + 4 * pg.length + 2 * n)
  same : SameOn (· < F₀) m₀ m

/-- The state of the scan. -/
def EnSt (pg : Graph) (n F₀ : ℕ) (m₀ : ℕ → ℕ) (E : List (ℕ × ℕ)) (a : ℕ) (c : Config) : Prop :=
  EnGlob pg n F₀ c ∧ EnMem pg n F₀ m₀ (c.reg rNB) (c.reg rOFF) E a c.mem ∧
    c.reg gNS = E.length

/-- Appending a segment: four stores. -/
theorem EnMem.push {F₀ : ℕ} {m₀ : ℕ → ℕ} {nb off : ℕ} {E : List (ℕ × ℕ)} {a : ℕ} {m : ℕ → ℕ}
    (h : EnMem pg n F₀ m₀ nb off E a m) (hnb : nb + (nbCat pg n).length ≤ F₀)
    (hoff : off + (n + 1) ≤ F₀) (hlen : E.length < pg.length) (s : ℕ × ℕ) :
    EnMem pg n F₀ m₀ nb off (E ++ [s]) a
      (upd (upd (upd (upd m (F₀ + E.length) s.1) (F₀ + pg.length + E.length) s.2)
        (F₀ + 2 * pg.length + E.length) (predOf pg n s)) (F₀ + 3 * pg.length + E.length)
        (sizeOf s)) := by
  have hl : ∀ f : ℕ × ℕ → ℕ, (E.map f).length = E.length := fun f => List.length_map _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((h.nbc.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)).upd_of_disjoint
      (by omega)).upd_of_disjoint (by omega)
  · exact (((h.offs.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)).upd_of_disjoint
      (by omega)).upd_of_disjoint (by omega)
  · rw [List.map_append, List.map_singleton]
    exact (((h.sa.upd_snoc (by rw [hl])).upd_of_disjoint (by simp; omega)).upd_of_disjoint
      (by simp; omega)).upd_of_disjoint (by simp; omega)
  · rw [List.map_append, List.map_singleton]
    exact (((h.sb.upd_of_disjoint (by rw [hl]; omega)).upd_snoc (by rw [hl])).upd_of_disjoint
      (by simp; omega)).upd_of_disjoint (by simp; omega)
  · rw [List.map_append, List.map_singleton]
    exact (((h.sp.upd_of_disjoint (by rw [hl]; omega)).upd_of_disjoint (by rw [hl]; omega)).upd_snoc
      (by rw [hl])).upd_of_disjoint (by simp; omega)
  · rw [List.map_append, List.map_singleton]
    exact (((h.sk.upd_of_disjoint (by rw [hl]; omega)).upd_of_disjoint (by rw [hl]; omega)).upd_of_disjoint
      (by rw [hl]; omega)).upd_snoc (by rw [hl])
  · exact (((h.last.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)).upd_of_disjoint
      (by omega)).upd_of_disjoint (by omega)
  · exact (((h.lseg.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)).upd_of_disjoint
      (by omega)).upd_of_disjoint (by omega)
  · exact (((h.zero.upd (by omega)).upd (by omega)).upd (by omega)).upd (by omega)
  · exact (((h.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _).upd_of_ge (by omega) _).upd_of_ge
      (by omega) _

theorem EnSt.indep (F₀ : ℕ) (m₀ : ℕ → ℕ) (E : List (ℕ × ℕ)) (a : ℕ) :
    Indep [rT, rEA, rELo, rEHi, rEPrev, rEA2, rEJ, rEB, rEX, rEA1] (EnSt pg n F₀ m₀ E a) := by
  indep [EnSt, enGlob_iff]

/-- Appending the segment `(a, b)`. -/
theorem enPush_run {F₀ : ℕ} {m₀ : ℕ → ℕ} {E : List (ℕ × ℕ)} {a b : ℕ} {c : Config}
    (hS : EnSt pg n F₀ m₀ E a c) (hA : c.reg rEA = a) (hB : c.reg rEB = b)
    (hP : c.reg rEPrev = predNb pg n a b) (hlen : E.length < pg.length) :
    EnSt pg n F₀ m₀ (E ++ [(a, b)]) a (RAM.run enPush c) ∧
      ∀ r, r ∉ wregs enPush → (RAM.run enPush c).reg r = c.reg r := by
  obtain ⟨hG, hM, hns⟩ := hS
  have hrr : ∀ r, r ∉ wregs enPush → (RAM.run enPush c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) hr c
  have hmem : (RAM.run enPush c).mem =
      upd (upd (upd (upd c.mem (F₀ + E.length) a) (F₀ + pg.length + E.length) b)
        (F₀ + 2 * pg.length + E.length) (predOf pg n (a, b))) (F₀ + 3 * pg.length + E.length)
        (sizeOf (a, b)) := by
    simp +decide only [enPush, run_seq', run_sub, run_inc (show gNS ≠ rT by decide),
      run_st (show rEA ≠ rT by decide), run_st (show rEB ≠ rT by decide),
      run_st (show rEPrev ≠ rT by decide), run_st (show rEX ≠ rT by decide), setReg_reg,
      ↓reduceIte, setReg_mem, setMem_reg, setMem_mem_upd, hA, hB, hP, hns, hG.sea, hG.seb,
      hG.sep, hG.sek, predOf, sizeOf]
  refine ⟨⟨(show RegIndep (wregs enPush) (EnGlob pg n F₀) by indep [enGlob_iff]).run (by decide) hG,
    ?_, ?_⟩, hrr⟩
  · rw [hrr rNB (by decide), hrr rOFF (by decide), hmem]
    exact hM.push hG.bnb hG.boff hlen (a, b)
  · simp +decide [enPush, run_inc, run_st, hns]

/-! ### The scan of the neighbours of `a` -/

/-- The invariant of the scan of the neighbours of `a`, at the position `j` of `nbCat`. -/
def InInv (pg : Graph) (n F₀ : ℕ) (m₀ : ℕ → ℕ) (a j : ℕ) (c : Config) : Prop :=
  EnSt pg n F₀ m₀ (enumPre pg n a ((nbP pg n a).take (j - nbOff pg n a))) a c ∧
    c.reg rEA = a ∧ c.reg rEA2 = a + 2 ∧
    c.reg rEPrev = ((nbP pg n a).take (j - nbOff pg n a)).getLastD a

/-- The neighbour list of `a` in `nbCat`. -/
theorem arr_nbP {m : ℕ → ℕ} {nb : ℕ} (h : Arr m nb (nbCat pg n)) {a : ℕ} (ha : a < n) :
    Arr m (nb + nbOff pg n a) (nbP pg n a) :=
  arr_flatMap_get (nbP pg n) n h a ha

/-- The scan so far is shorter than the edge list when one more segment comes. -/
theorem length_enumPre_lt {a i : ℕ} (ha : a < n) (hi : i < (nbP pg n a).length)
    (hab : a + 2 ≤ (nbP pg n a)[i]) :
    (enumPre pg n a ((nbP pg n a).take i)).length < pg.length := by
  have hpre := enumPre_prefix (pg := pg) ha (List.take_prefix (i + 1) (nbP pg n a))
  have h1 := hpre.length_le
  have h2 := length_segEnum_le (pg := pg) (n := n)
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, enumPre_snoc] at h1
  simp only [hab, ↓reduceIte, List.length_append, List.length_singleton] at h1
  omega

theorem nbOff_mono {p q : ℕ} (h : p ≤ q) : nbOff pg n p ≤ nbOff pg n q := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [nbOff_succ]; omega

theorem enInner_spec (F₀ : ℕ) (m₀ : ℕ → ℕ) (hS : enEnd pg n F₀ ≤ S) (a : ℕ) (ha : a < n) (j : ℕ)
    (hj1 : nbOff pg n a ≤ j) (hj2 : j < nbOff pg n (a + 1)) :
    HTB S enInner (fun c => InInv pg n F₀ m₀ a j c ∧ c.reg rEJ = j ∧
        c.reg rEHi = nbOff pg n (a + 1))
      (fun c => InInv pg n F₀ m₀ a (j + 1) c ∧ c.reg rEJ = j ∧
        c.reg rEHi = nbOff pg n (a + 1)) 21 := by
  refine HTB.run_le (by decide) (by decide) fun c hc => ?_
  obtain ⟨⟨hS, hA, hA2, hprev⟩, hj, hhi⟩ := hc
  have hi : j - nbOff pg n a < (nbP pg n a).length := by rw [nbOff_succ] at hj2; omega
  have hb : c.mem (c.reg rNB + j) = (nbP pg n a)[j - nbOff pg n a] := by
    rw [← (arr_nbP hS.2.1.nbc ha).get hi]; congr 1; omega
  have htake : (nbP pg n a).take (j + 1 - nbOff pg n a) =
      (nbP pg n a).take (j - nbOff pg n a) ++ [(nbP pg n a)[j - nbOff pg n a]] := by
    rw [show j + 1 - nbOff pg n a = j - nbOff pg n a + 1 by omega, List.take_add_one,
      List.getElem?_eq_getElem hi]; rfl
  have hpred := predNb_getElem (pg := pg) (n := n) a hi
  have hlen : a + 2 ≤ (nbP pg n a)[j - nbOff pg n a] →
      (enumPre pg n a ((nbP pg n a).take (j - nbOff pg n a))).length < pg.length :=
    length_enumPre_lt ha hi
  generalize (nbP pg n a)[j - nbOff pg n a] = b at hb htake hpred hlen
  refine ⟨?_, ?_⟩
  · obtain ⟨hG, -, hns⟩ := hS
    have := hG.bnb
    have := nbOff_mono (pg := pg) (n := n) (show a + 1 ≤ n by omega)
    rw [nbOff_eq] at this
    unfold enEnd at hS
    addr_ok [enInner, enPush, hj, hb, hA, hA2, hG.sea, hG.seb, hG.sep, hG.sek, hns]
  have hlast : ((nbP pg n a).take (j - nbOff pg n a) ++ [b]).getLastD a = b := by
    simp [List.getLastD_eq_getLast?]
  have hc1 : RAM.run (ld rEB rNB rEJ) c = c.setReg rEB b := by rw [run_ld, hj, hb]
  have hind := EnSt.indep (pg := pg) (n := n) F₀ m₀
    (enumPre pg n a ((nbP pg n a).take (j - nbOff pg n a))) a
  have hS1 := hind.setReg (d := rEB) (by decide) b hS
  rw [show enInner = .seq (ld rEB rNB rEJ) (.seq (ifLe rEA2 rEB enPush .skip) (mov rEPrev rEB))
    from rfl, run_seq', run_seq', hc1, run_ifLe]
  simp +decide only [setReg_reg, ↓reduceIte, hA2]
  unfold InInv
  rw [htake, enumPre_snoc, hlast]
  have hS2 := hind.setReg (d := rT) (by decide) (a + 2 - b) hS1
  by_cases hab : a + 2 ≤ b
  · simp only [hab, ↓reduceIte]
    obtain ⟨hS3, hrr⟩ := enPush_run (a := a) (b := b) hS2 (by simp +decide [hA]) (by simp +decide)
      (by simp +decide [hprev, hpred]) (hlen hab)
    have hind' := EnSt.indep (pg := pg) (n := n) F₀ m₀
      (enumPre pg n a ((nbP pg n a).take (j - nbOff pg n a)) ++ [(a, b)]) a
    rw [run_mov (by decide)]
    refine ⟨⟨hind'.setReg (d := rEPrev) (by decide) _ (hind'.setReg (d := rT) (by decide) _ hS3),
      ?_, ?_, ?_⟩, ?_, ?_⟩
    all_goals simp +decide only [setReg_reg, ↓reduceIte]
    all_goals rw [hrr _ (by decide)]
    all_goals simp +decide [hA, hA2, hj, hhi]
  · simp only [hab, ↓reduceIte, List.append_nil, run_skip]
    rw [run_mov (by decide)]
    refine ⟨⟨hind.setReg (d := rEPrev) (by decide) _ (hind.setReg (d := rT) (by decide) _ hS2),
      ?_, ?_, ?_⟩, ?_, ?_⟩
    all_goals simp +decide [hA, hA2, hj, hhi]

/-- The invariant of the scan before the position `a`. -/
def OutInv (pg : Graph) (n F₀ : ℕ) (m₀ : ℕ → ℕ) (a : ℕ) (c : Config) : Prop :=
  EnSt pg n F₀ m₀ (enumPre pg n a []) a c

theorem nbOff_le_succ (a : ℕ) : nbOff pg n a ≤ nbOff pg n (a + 1) := by
  rw [nbOff_succ]; omega

theorem enOuter_spec (F₀ : ℕ) (m₀ : ℕ → ℕ) (hS : enEnd pg n F₀ ≤ S) (a : ℕ) (ha : a < n) :
    HTB S enOuter (fun c => OutInv pg n F₀ m₀ a c ∧ c.reg rEA = a ∧ c.reg gPN = n)
      (fun c => OutInv pg n F₀ m₀ (a + 1) c ∧ c.reg rEA = a ∧ c.reg gPN = n)
      (25 * (nbP pg n a).length + 24) := by
  have h₁ : HTB S enPre (fun c => OutInv pg n F₀ m₀ a c ∧ c.reg rEA = a ∧ c.reg gPN = n)
      (fun c => InInv pg n F₀ m₀ a (nbOff pg n a) c ∧ c.reg rELo = nbOff pg n a ∧
        c.reg rEHi = nbOff pg n (a + 1) ∧ nbOff pg n a ≤ nbOff pg n (a + 1)) 10 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hS', hA, hN⟩ => ?_
    have hlo : c.mem (c.reg rOFF + a) = nbOff pg n a := hS'.2.1.offs.get (by omega)
    have hhi : c.mem (c.reg rOFF + (a + 1)) = nbOff pg n (a + 1) := hS'.2.1.offs.get (by omega)
    refine ⟨by have := hS'.1.boff; unfold enEnd at hS; addr_ok [enPre, hA], ?_⟩
    have hind := EnSt.indep (pg := pg) (n := n) F₀ m₀ (enumPre pg n a []) a
    have hag : Agree [rT, rEA, rELo, rEHi, rEPrev, rEA2, rEJ, rEB, rEX, rEA1] c (RAM.run enPre c) :=
      agree_run (by decide) rfl rfl (by decide) c
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, nbOff_le_succ a⟩
    · rw [Nat.sub_self, List.take_zero]; exact hind c _ hag hS'
    all_goals simp +decide [enPre, run_ld, run_addc, run_mov, hA, hlo, hhi]
  have h₂ := HTB.forRange (i := rEJ) (a := rELo) (n := rEHi) (A := nbOff pg n a)
    (N := nbOff pg n (a + 1)) (body := enInner) (InInv pg n F₀ m₀ a) (fun _ => 21)
    (by decide) (by decide) (by decide) (by decide) (fun j => by indep [InInv, EnSt, enGlob_iff])
    (fun j hj1 hj2 => enInner_spec F₀ m₀ hS a ha j hj1 hj2)
  have h₃ : HTB S enPost (fun c => InInv pg n F₀ m₀ a (nbOff pg n (a + 1)) c ∧
        c.reg rEJ = nbOff pg n (a + 1) ∧ c.reg rEHi = nbOff pg n (a + 1))
      (fun c => OutInv pg n F₀ m₀ (a + 1) c ∧ c.reg rEA = a ∧ c.reg gPN = n) 10 := by
    refine HTB.run_le (by decide) (by decide) fun c hc => ?_
    obtain ⟨⟨⟨hG, hM, hns⟩, hA, hA2, hprev⟩, -, -⟩ := hc
    refine ⟨by unfold enEnd at hS; addr_ok [enPost, enLseg, hA, hG.last, hG.lseg], ?_⟩
    have hfull : nbOff pg n (a + 1) - nbOff pg n a = (nbP pg n a).length := by
      rw [nbOff_succ]; omega
    rw [hfull, List.take_length] at hprev hM hns
    have hprev' : c.reg rEPrev = lastNb pg n a := hprev
    have hrr : ∀ r, r ∉ wregs enPost → (RAM.run enPost c).reg r = c.reg r :=
      fun r hr => run_reg_of_not_mem (by decide) hr c
    have hmem : (RAM.run enPost c).mem = upd (upd c.mem (F₀ + 4 * pg.length + a) (lastNb pg n a))
        (F₀ + 4 * pg.length + n + a) (enumId pg n (a, lastNb pg n a)) := by
      rw [enumId_last ha]
      by_cases hle : a + 2 ≤ lastNb pg n a
      · simp +decide only [enPost, enLseg, run_seq', run_ifLe, run_st (show rEPrev ≠ rT by decide),
          run_st (show rEX ≠ rT by decide), run_mov (show gNS ≠ rT by decide), setReg_reg,
          ↓reduceIte, setReg_mem, setMem_mem_upd, setMem_reg, hA, hA2, hG.last, hG.lseg, hprev',
          hle, hns]
      · simp +decide only [enPost, enLseg, run_seq', run_ifLe, run_st (show rEPrev ≠ rT by decide),
          run_st (show rEX ≠ rT by decide), run_const, setReg_reg, ↓reduceIte, setReg_mem,
          setMem_mem_upd, setMem_reg, hA, hA2, hG.last, hG.lseg, hprev', hle]
    unfold OutInv
    rw [enumPre_succ]
    have hf := hG.free
    have hb := hG.bnb
    have ho := hG.boff
    have hE := (enumPre_prefix (pg := pg) ha (List.prefix_refl (nbP pg n a))).length_le
    have hS := length_segEnum_le (pg := pg) (n := n)
    refine ⟨⟨(show RegIndep (wregs enPost) (EnGlob pg n F₀) by indep [enGlob_iff]).run
      (by decide) hG, ?_, ?_⟩, ?_, ?_⟩
    · rw [hrr rNB (by decide), hrr rOFF (by decide), hmem]
      refine ⟨(hM.nbc.upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
        (hM.offs.upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
        (hM.sa.upd_of_disjoint (by simp; omega)).upd_of_disjoint (by simp; omega),
        (hM.sb.upd_of_disjoint (by simp; omega)).upd_of_disjoint (by simp; omega),
        (hM.sp.upd_of_disjoint (by simp; omega)).upd_of_disjoint (by simp; omega),
        (hM.sk.upd_of_disjoint (by simp; omega)).upd_of_disjoint (by simp; omega),
        ((hM.last.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)).snoc
          (by rw [upd_ne _ _ (by omega), upd_same]),
        ((hM.lseg.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)).snoc (by rw [upd_same]),
        (hM.zero.upd (by omega)).upd (by omega),
        (hM.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _⟩
    · rw [hrr gNS (by decide), hns]
    · rw [hrr rEA (by decide), hA]
    · rw [hrr gPN (by decide), hG.pn]
  refine (h₁.seq (h₂.seq h₃)).weaken ?_
  simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
  rw [nbOff_succ]; omega

/-! ### Stage B -/

theorem enAlloc_spec (F₀ : ℕ) (m₀ : ℕ → ℕ) :
    HT enAlloc (fun c => ((Csr pg n c ∧ Zf c) ∧ c.reg gPN = n ∧ c.reg gPE = pg.length) ∧
        c.reg rFREE = F₀ ∧ c.mem = m₀)
      (fun c => OutInv pg n F₀ m₀ 0 c ∧ c.reg gPN = n) 22 := by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hC, hZ⟩, hN, hE⟩, hF, hm⟩ => ?_
  simp only [enAlloc, run_seq', run_alloc (show gPE ≠ rT by decide) (show rSEA ≠ gPE by decide),
    run_alloc (show gPE ≠ rT by decide) (show rSEB ≠ gPE by decide),
    run_alloc (show gPE ≠ rT by decide) (show rSEP ≠ gPE by decide),
    run_alloc (show gPE ≠ rT by decide) (show rSEK ≠ gPE by decide),
    run_alloc (show gPN ≠ rT by decide) (show rLAST ≠ gPN by decide),
    run_alloc (show gPN ≠ rT by decide) (show rLSEG ≠ gPN by decide), run_const]
  have h1 := hC.1.2
  have h2 := hC.2.2
  unfold OutInv EnSt
  rw [enumPre_zero]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_⟩, ?_⟩
  all_goals simp +decide only [setReg_reg, ↓reduceIte, setReg_mem, hF, hN, hE, List.map_nil,
    arr_nil, tab_zero, List.length_nil]
  all_goals try omega
  · exact hC.1.1
  · exact hC.2.1
  · unfold Zf at hZ; rw [hF] at hZ; exact hZ.mono (by omega)
  · rw [hm]; exact SameOn.refl _ _

/-- **Stage B**: the enumeration of the segments, in `O(n + |pg|)` steps; from the free address
`F₀`, it ends at `enEnd pg n F₀`. -/
theorem stageB_core (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2) (hnd : pg.Nodup)
    (F₀ : ℕ) (m₀ : ℕ → ℕ) (hS : enEnd pg n F₀ ≤ S) :
    HTB S stageB (fun c => ((Csr pg n c ∧ Zf c) ∧ c.reg gPN = n ∧ c.reg gPE = pg.length) ∧
        c.reg rFREE = F₀ ∧ c.mem = m₀)
      (fun c => (EnumSt pg n c ∧ Zf c) ∧ SameOn (· < F₀) m₀ c.mem ∧ F₀ ≤ c.reg rFREE ∧
        c.reg rFREE = enEnd pg n F₀) (50 * pg.length + 28 * n + 25) := by
  have hl := HTB.forUp (i := rEA) (n := gPN) (N := n) (body := enOuter) (OutInv pg n F₀ m₀)
    (fun a => 25 * (nbP pg n a).length + 24) (by decide) (by decide) (by decide)
    (fun a => by indep [OutInv, EnSt, enGlob_iff]) (fun a ha => enOuter_spec F₀ m₀ hS a ha)
  refine ((HTB.of_HT rfl (enAlloc_spec F₀ m₀)).seq hl).mono (fun _ h => h) ?_ ?_
  · rintro c ⟨⟨hG, hM, hns⟩, -, -⟩
    rw [enumPre_full] at hM hns
    have hS := length_segEnum_le (pg := pg) (n := n)
    have hf := hG.free
    refine ⟨⟨⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩, ?_, ?_, ?_⟩
    all_goals try simp +decide only [List.length_map, hns, hG.sea, hG.seb, hG.sep, hG.sek, hG.last,
      hG.lseg, hG.free, enEnd]
    all_goals try omega
    · exact hM.sa
    · exact hM.sb
    · exact hM.sp
    · exact hM.sk
    · exact hM.last
    · exact hM.lseg
    · unfold Zf; simpa +decide [hG.free] using hM.zero
    · exact hM.same
  · have hsum : ∑ a ∈ Finset.range n, (25 * (nbP pg n a).length + 24 + 4) =
        25 * (2 * pg.length) + 28 * n := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_range_eq]
      have : ((List.range n).map fun a => (nbP pg n a).length).sum = 2 * pg.length := by
        rw [← length_nbCat hP hlt hnd, ← nbOff_eq]; rfl
      rw [this]; simp; ring
    rw [hsum]; omega

/-- **Stage B** (growth triple). -/
theorem stageB_spec (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2) (hnd : pg.Nodup) :
    HGMB S stageB WB (fun c => (Csr pg n c ∧ Zf c) ∧ c.reg gPN = n ∧ c.reg gPE = pg.length)
      (fun c => EnumSt pg n c ∧ Zf c) (50 * pg.length + 28 * n + 25) (4 * pg.length + 2 * n) :=
  HGMB.ofGhost (by decide) (fun _ h => h) fun F₀ m₀ hS =>
    (stageB_core hP hlt hnd F₀ m₀ (by unfold enEnd; omega)).post
      fun _ h => ⟨h.1, h.2.1, h.2.2.1, by rw [h.2.2.2, enEnd]; omega⟩

end STACS2027.RAM.P1
