module

public import Outerplanar.RAM.Poly1Order
import Mathlib.Tactic

/-!
# Phase P1 of the polygon solver, stage E: the faces

Stage E (`stageE`) writes the face vertices of the segments, in the order `segOrder`, to a
growing array `gFV` at the free pointer (each vertex is pushed at `rFREE`, which then grows by
one), and the start of each face in `gFOFF` (`fOff`). The face of `s = (a, b)` is walked as in
`faceWalk` (`faceWalk_eq`): `a`, then the stored face vertex after `a` (`predOf`), then by the
stored largest neighbours (`lastNb`) until `b` (`walk_step`, `walk_done`). The walks cost
`O(|faceCat|) = O(|pg|)` steps (`length_faceCat_le`), so stage E runs in `O(|pg|)` steps
(`stageE_spec`).
-/

@[expose] public section

namespace STACS2027.RAM.P1

open STACS2027.Poly

/-! ### Registers and program -/

/-- The index `t` of the segment in `segOrder`. -/
abbrev rFT : ℕ := 140
/-- The first end `a`. -/
abbrev rFA : ℕ := 141
/-- The second end `b`. -/
abbrev rFB : ℕ := 142
/-- The current face vertex `x` of the walk. -/
abbrev rFX : ℕ := 143
/-- Temporary. -/
abbrev rFI : ℕ := 144
/-- Temporary. -/
abbrev rFD : ℕ := 145
/-- `NS + 1`. -/
abbrev rFN1 : ℕ := 146

/-- Push the register `v` at the free pointer. -/
def push (v : ℕ) : Stmt := .seq (.store rFREE v) (inc rFREE)

@[simp] theorem addrOK_push {S : ℕ} (v : ℕ) (c : Config) :
    AddrOK S (push v) c ↔ c.reg rFREE < S := by
  simp [push, AddrOK]
/-- Allocate the face offsets (`NS + 1` cells); the face vertices start at the free pointer. -/
def faInit : Stmt := .seq (addc rFN1 gNS 1) (.seq (alloc gFOFF rFN1) (mov gFV rFREE))
/-- Read the segment `t`: `a`, `b` and the face vertex after `a`. -/
def faRd : Stmt :=
  .seq (ld rFA gSA rFT) (.seq (ld rFB gSB rFT) (.seq (ld rFI rORD3 rFT) (ld rFX rSEP rFI)))
/-- Store the face offset of the segment `t`. -/
def faOff : Stmt := .seq (.sub rFI rFREE gFV) (st gFOFF rFT rFI)
/-- Read the segment `t`, store its face offset, push `a`. -/
def faPre : Stmt := .seq faRd (.seq faOff (push rFA))
/-- The test of the walk: `rT := |x - b|`. -/
def faCond : Stmt := .seq (.sub rT rFX rFB) (.seq (.sub rFD rFB rFX) (.add rT rT rFD))
/-- One step of the walk: push `x`, `x := LAST[x]`. -/
def faStep : Stmt := .seq (push rFX) (ld rFX rLAST rFX)
/-- One face. -/
def faBody : Stmt := .seq faPre (.seq (whileC faCond faStep) (push rFB))
/-- The last face offset. -/
def faFin : Stmt := .seq (.sub rFI rFREE gFV) (st gFOFF gNS rFI)
/-- **Stage E**: the faces. -/
def stageE : Stmt := .seq faInit (.seq (forUp rFT gNS faBody) faFin)

/-- The registers written by stage E. -/
abbrev WE : List ℕ := wregs stageE

/-- The result of stage E. -/
def FaceSt (pg : Graph) (n : ℕ) (c : Config) : Prop :=
  ArrAt gFOFF (faceOffs pg n) c ∧ ArrAt gFV (faceCat pg n) c

theorem stable_faceSt {pg : Graph} {n : ℕ} {W : List ℕ} (h : gFOFF ∉ W ∧ gFV ∉ W) :
    Stable W (FaceSt pg n) :=
  (Stable.arrAt h.1 _).and (Stable.arrAt h.2 _)

variable {pg : Graph} {n : ℕ} {S : ℕ}

/-! ### The walk -/

/-- The walk ends with `b`. -/
theorem walkTo_self (b f : ℕ) : walkTo pg n b f b = [b] := by
  cases f <;> simp [walkTo]

/-- The walk from the first end. -/
theorem walk_start (hP : IsPolygon pg n) {s : ℕ × ℕ} (hs : s ∈ IsPolygon.segs pg n) :
    [s.1] ++ walkTo pg n s.2 n (predOf pg n s) = faceVerts pg n s := by
  rw [← faceWalk_eq hP hs]; rfl

/-- One step of the walk at a vertex `x ≠ b`. -/
theorem walk_step {s : ℕ × ℕ} (hs : s.1 ≤ s.2) {cur : List ℕ} {f x : ℕ}
    (h : cur ++ walkTo pg n s.2 f x = faceVerts pg n s) (hx : x ≠ s.2) :
    ∃ f', (cur ++ [x]) ++ walkTo pg n s.2 f' (lastNb pg n x) = faceVerts pg n s := by
  cases f with
  | zero =>
    exfalso
    have hl := faceVerts_getLast? (g := pg) (n := n) hs
    rw [← h] at hl
    simp [walkTo] at hl
    exact hx hl
  | succ f =>
    refine ⟨f, ?_⟩
    rw [← h, walkTo]
    simp [hx]

theorem walk_done {s : ℕ × ℕ} {cur : List ℕ} {f : ℕ}
    (h : cur ++ walkTo pg n s.2 f s.2 = faceVerts pg n s) : cur ++ [s.2] = faceVerts pg n s := by
  rw [← h, walkTo_self]

theorem walk_mem {s : ℕ × ℕ} {cur : List ℕ} {f x : ℕ}
    (h : cur ++ walkTo pg n s.2 f x = faceVerts pg n s) : x ∈ faceVerts pg n s := by
  rw [← h]
  cases f <;> simp [walkTo]
  split <;> simp

theorem length_walk_lt {s : ℕ × ℕ} {cur : List ℕ} {f x : ℕ}
    (h : cur ++ walkTo pg n s.2 f x = faceVerts pg n s) : cur.length < (faceVerts pg n s).length := by
  rw [← h, List.length_append]
  have : (walkTo pg n s.2 f x).length ≠ 0 := by cases f <;> simp [walkTo]; split <;> simp
  omega

/-! ### The state -/

/-- The faces of the first `t` segments. -/
abbrev doneOf (pg : Graph) (n t : ℕ) : List ℕ := ((segOrder pg n).take t).flatMap (faceVerts pg n)

theorem length_doneOf (t : ℕ) : (doneOf pg n t).length = fOff pg n t := rfl

theorem doneOf_succ {t : ℕ} (ht : t < (segOrder pg n).length) :
    doneOf pg n (t + 1) = doneOf pg n t ++ faceVerts pg n (segOrder pg n)[t] := by
  rw [doneOf, take_succ_segOrder ht, List.flatMap_append, List.flatMap_singleton]

/-- The state of stage E with `k` face offsets and the face vertices `done`. -/
@[mk_iff] structure FaSt (pg : Graph) (n F₀ : ℕ) (m₀ : ℕ → ℕ) (k : ℕ) (done : List ℕ)
    (c : Config) : Prop where
  foff : c.reg gFOFF = F₀
  fv : c.reg gFV = F₀ + ((segOrder pg n).length + 1)
  free : c.reg rFREE = F₀ + ((segOrder pg n).length + 1) + done.length
  ns : c.reg gNS = (segOrder pg n).length
  sa : Arr c.mem (c.reg gSA) ((segOrder pg n).map Prod.fst)
  bsa : c.reg gSA + (segOrder pg n).length ≤ F₀
  sb : Arr c.mem (c.reg gSB) ((segOrder pg n).map Prod.snd)
  bsb : c.reg gSB + (segOrder pg n).length ≤ F₀
  ord : Arr c.mem (c.reg rORD3) (ord3 pg n)
  bord : c.reg rORD3 + (ord3 pg n).length ≤ F₀
  sep : Arr c.mem (c.reg rSEP) ((segEnum pg n).map (predOf pg n))
  bsep : c.reg rSEP + (segEnum pg n).length ≤ F₀
  last : Tab c.mem (c.reg rLAST) n (lastNb pg n)
  blast : c.reg rLAST + n ≤ F₀
  offs : Tab c.mem F₀ k (fOff pg n)
  fvs : Arr c.mem (F₀ + ((segOrder pg n).length + 1)) done
  zero : ZeroFrom c.mem (c.reg rFREE)
  same : SameOn (· < F₀) m₀ c.mem

theorem FaSt.indep (F₀ : ℕ) (m₀ : ℕ → ℕ) (k : ℕ) (done : List ℕ) :
    Indep [rT, rFT, rFA, rFB, rFX, rFI, rFD] (FaSt pg n F₀ m₀ k done) := by
  indep [faSt_iff]

/-- Pushing a value. -/
theorem push_run {F₀ : ℕ} {m₀ : ℕ → ℕ} {k : ℕ} {done : List ℕ} {c : Config} {v : ℕ}
    (h : FaSt pg n F₀ m₀ k done c) (hk : k ≤ (segOrder pg n).length + 1) :
    FaSt pg n F₀ m₀ k (done ++ [c.reg v]) (RAM.run (push v) c) ∧
      ∀ r, r ≠ rT → r ≠ rFREE → (RAM.run (push v) c).reg r = c.reg r := by
  have hrun : RAM.run (push v) c =
      ((c.setMem (c.reg rFREE) (c.reg v)).setReg rT 1).setReg rFREE (c.reg rFREE + 1) := by
    simp [push, run_inc]
  have hfr := h.free
  refine ⟨?_, fun r h1 h2 => by rw [hrun]; simp [h1, h2]⟩
  rw [hrun]
  have hA := h.bsa
  have hB := h.bsb
  have hO := h.bord
  have hS := h.bsep
  have hL := h.blast
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp +decide only [setReg_reg, ↓reduceIte, setReg_mem, setMem_reg, setMem_mem_upd]
  · exact h.foff
  · exact h.fv
  · rw [h.free, List.length_append, List.length_singleton]; omega
  · exact h.ns
  · exact h.sa.upd_of_disjoint (by simp; omega)
  · exact h.bsa
  · exact h.sb.upd_of_disjoint (by simp; omega)
  · exact h.bsb
  · exact h.ord.upd_of_disjoint (by omega)
  · exact h.bord
  · exact h.sep.upd_of_disjoint (by simp; omega)
  · exact h.bsep
  · exact h.last.upd_of_disjoint (by omega)
  · exact h.blast
  · exact h.offs.upd_of_disjoint (by omega)
  · exact h.fvs.upd_snoc (by omega)
  · exact (h.zero.mono (by omega)).upd (by omega)
  · exact h.same.upd_of_ge (by omega) _

/-! ### One face -/

/-- The bound of stage E: the face offsets and the face vertices above `F₀`. -/
def faEnd (pg : Graph) (n F₀ : ℕ) : ℕ :=
  F₀ + ((segOrder pg n).length + 1) + (faceCat pg n).length

theorem faPre_spec (hP : IsPolygon pg n) (F₀ : ℕ) (m₀ : ℕ → ℕ) (hS : faEnd pg n F₀ ≤ S) (t : ℕ)
    (ht : t < (segOrder pg n).length) :
    HTB S faPre (fun c => FaSt pg n F₀ m₀ t (doneOf pg n t) c ∧ c.reg rFT = t)
      (fun c => FaSt pg n F₀ m₀ (t + 1) (doneOf pg n t ++ [(segOrder pg n)[t].1]) c ∧
        c.reg rFX = predOf pg n (segOrder pg n)[t] ∧ c.reg rFB = (segOrder pg n)[t].2 ∧
        c.reg rFT = t) 14 := by
  unfold faEnd at hS
  have h₁ : HTB S faRd (fun c => FaSt pg n F₀ m₀ t (doneOf pg n t) c ∧ c.reg rFT = t)
      (fun c => FaSt pg n F₀ m₀ t (doneOf pg n t) c ∧ c.reg rFT = t ∧
        c.reg rFA = (segOrder pg n)[t].1 ∧ c.reg rFX = predOf pg n (segOrder pg n)[t] ∧
        c.reg rFB = (segOrder pg n)[t].2) 8 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hS, hT⟩ => ?_
    have hag : Agree [rT, rFT, rFA, rFB, rFX, rFI, rFD] c (RAM.run faRd c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hl : t < (ord3 pg n).length := by rw [length_ord3]; exact ht
    have ha : c.mem (c.reg gSA + t) = (segOrder pg n)[t].1 := by
      rw [hS.sa.get (by simpa using ht)]; simp
    have hb : c.mem (c.reg gSB + t) = (segOrder pg n)[t].2 := by
      rw [hS.sb.get (by simpa using ht)]; simp
    have hi : c.mem (c.reg rORD3 + t) = (ord3 pg n).getD t 0 := hS.ord.getD hl
    have hilt : (ord3 pg n).getD t 0 < (segEnum pg n).length := by
      apply lt_of_mem_ord3
      rw [getD_of_lt hl]
      exact List.getElem_mem _
    have hx : c.mem (c.reg rSEP + (ord3 pg n).getD t 0) = predOf pg n (segOrder pg n)[t] := by
      rw [hS.sep.getD (by rw [List.length_map]; exact hilt), getD_ord3 _ ht]
    refine ⟨by
      have := hS.bsa; have := hS.bsb; have := hS.bord; have := hS.bsep
      rw [length_ord3] at *
      addr_ok [faRd, hT, hi], (FaSt.indep F₀ m₀ t _) c _ hag hS, ?_, ?_, ?_, ?_⟩
    all_goals simp +decide only [faRd, run_seq', run_ld, setReg_reg, ↓reduceIte, setReg_mem, hT,
      ha, hb, hi, hx]
  have h₂ : HTB S faOff (fun c => FaSt pg n F₀ m₀ t (doneOf pg n t) c ∧ c.reg rFT = t ∧
        c.reg rFA = (segOrder pg n)[t].1 ∧ c.reg rFX = predOf pg n (segOrder pg n)[t] ∧
        c.reg rFB = (segOrder pg n)[t].2)
      (fun c => FaSt pg n F₀ m₀ (t + 1) (doneOf pg n t) c ∧ c.reg rFT = t ∧
        c.reg rFA = (segOrder pg n)[t].1 ∧ c.reg rFX = predOf pg n (segOrder pg n)[t] ∧
        c.reg rFB = (segOrder pg n)[t].2) 3 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hS, hT, hA, hX, hB⟩ => ?_
    refine ⟨by addr_ok [faOff, hT, hS.foff], ?_⟩
    have hrr : ∀ r, r ∉ wregs faOff → (RAM.run faOff c).reg r = c.reg r :=
      fun r hr => run_reg_of_not_mem (by decide) hr c
    have hmem : (RAM.run faOff c).mem = upd c.mem (F₀ + t) (fOff pg n t) := by
      simp +decide only [faOff, run_seq', run_sub, run_st (show rFI ≠ rT by decide), setReg_reg,
        ↓reduceIte, setReg_mem, setMem_mem_upd, hT, hS.foff, hS.free, hS.fv, length_doneOf]
      congr 1; omega
    have hA' := hS.bsa
    have hB' := hS.bsb
    have hO := hS.bord
    have hP := hS.bsep
    have hL := hS.blast
    have hF := hS.free
    rw [length_doneOf] at hF
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    all_goals try rw [hrr _ (by decide)]
    all_goals try rw [hmem]
    · exact hS.foff
    · exact hS.fv
    · exact hS.free
    · exact hS.ns
    · exact hS.sa.upd_of_disjoint (by simp; omega)
    · exact hS.bsa
    · exact hS.sb.upd_of_disjoint (by simp; omega)
    · exact hS.bsb
    · exact hS.ord.upd_of_disjoint (by omega)
    · exact hS.bord
    · exact hS.sep.upd_of_disjoint (by simp; omega)
    · exact hS.bsep
    · exact hS.last.upd_of_disjoint (by omega)
    · exact hS.blast
    · exact (hS.offs.upd_of_disjoint (by omega)).snoc (by simp)
    · exact hS.fvs.upd_of_disjoint (by omega)
    · exact hS.zero.upd (by omega)
    · exact hS.same.upd_of_ge (by omega) _
    · exact hT
    · exact hA
    · exact hX
    · exact hB
  have h₃ : HTB S (push rFA) (fun c => FaSt pg n F₀ m₀ (t + 1) (doneOf pg n t) c ∧ c.reg rFT = t ∧
        c.reg rFA = (segOrder pg n)[t].1 ∧ c.reg rFX = predOf pg n (segOrder pg n)[t] ∧
        c.reg rFB = (segOrder pg n)[t].2)
      (fun c => FaSt pg n F₀ m₀ (t + 1) (doneOf pg n t ++ [(segOrder pg n)[t].1]) c ∧
        c.reg rFX = predOf pg n (segOrder pg n)[t] ∧ c.reg rFB = (segOrder pg n)[t].2 ∧
        c.reg rFT = t) 3 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hS, hT, hA, hX, hB⟩ => ?_
    refine ⟨?_, ?_⟩
    · have h3 := hP.three_le_length_faceVerts (mem_segOrder.mp (List.getElem_mem ht))
      have := fOff_succ (pg := pg) (n := n) ht
      have := fOff_le_faceCat (pg := pg) (n := n) (t + 1)
      rw [addrOK_push, hS.free, length_doneOf]; omega
    obtain ⟨hS', hrr⟩ := push_run (v := rFA) hS (by omega)
    rw [hA] at hS'
    refine ⟨hS', ?_, ?_, ?_⟩
    · rw [hrr _ (by decide) (by decide), hX]
    · rw [hrr _ (by decide) (by decide), hB]
    · rw [hrr _ (by decide) (by decide), hT]
  exact (h₁.seq (h₂.seq h₃)).weaken (by omega)

/-- The invariant of the walk along the face of `s`, the segment `t`. -/
def WInv (pg : Graph) (n F₀ : ℕ) (m₀ : ℕ → ℕ) (t : ℕ) (s : ℕ × ℕ) (c : Config) : Prop :=
  ∃ cur f, FaSt pg n F₀ m₀ (t + 1) (doneOf pg n t ++ cur) c ∧
    cur ++ walkTo pg n s.2 f (c.reg rFX) = faceVerts pg n s ∧ c.reg rFB = s.2 ∧ c.reg rFT = t ∧
    (c.reg rT = 0 ↔ c.reg rFX = s.2)

/-- The walk's measure: the face vertices still to push. -/
def wMu (pg : Graph) (n F₀ t : ℕ) (s : ℕ × ℕ) (c : Config) : ℕ :=
  F₀ + ((segOrder pg n).length + 1) + fOff pg n t + (faceVerts pg n s).length - c.reg rFREE

theorem faCond_run (c : Config) :
    (RAM.run faCond c).reg rT = (c.reg rFX - c.reg rFB) + (c.reg rFB - c.reg rFX) ∧
      Agree [rT, rFD] c (RAM.run faCond c) :=
  ⟨by simp +decide [faCond], agree_run (by decide) rfl rfl (by decide) c⟩

theorem walk_spec (hP : IsPolygon pg n) (F₀ : ℕ) (m₀ : ℕ → ℕ) (hS : faEnd pg n F₀ ≤ S) (t : ℕ)
    (ht : t < (segOrder pg n).length) :
    HTB S (whileC faCond faStep)
      (fun c => FaSt pg n F₀ m₀ (t + 1) (doneOf pg n t ++ [(segOrder pg n)[t].1]) c ∧
        c.reg rFX = predOf pg n (segOrder pg n)[t] ∧ c.reg rFB = (segOrder pg n)[t].2 ∧
        c.reg rFT = t)
      (fun c => WInv pg n F₀ m₀ t (segOrder pg n)[t] c ∧ c.reg rT = 0)
      (3 + ((faceVerts pg n (segOrder pg n)[t]).length * (8 + 1) + 1)) := by
  set s := (segOrder pg n)[t] with hsdef
  have hs : s ∈ IsPolygon.segs pg n := mem_segOrder.mp (List.getElem_mem ht)
  have hs2 := lt_of_mem_segOrder (List.getElem_mem ht)
  rw [← hsdef] at hs2
  unfold faEnd at hS
  refine HTB.whileC (wMu pg n F₀ t s) ?_ fun v => ?_
  · refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hS, hX, hB, hT⟩ => ?_
    obtain ⟨hrT, hag⟩ := faCond_run c
    have hS' := (FaSt.indep F₀ m₀ (t + 1) _) c _ (hag.mono (by decide)) hS
    refine ⟨⟨[s.1], n, hS', ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hag.reg rFX (by decide), hX]; exact walk_start hP hs
    · rw [hag.reg rFB (by decide), hB]
    · rw [hag.reg rFT (by decide), hT]
    · rw [hrT, hag.reg rFX (by decide), hB]; omega
    · unfold wMu
      rw [hS'.free, List.length_append, length_doneOf, List.length_singleton]
      omega
  · refine HTB.run_le (by decide) (by decide) fun c ⟨⟨cur, f, hS, hW, hB, hT, hiff⟩, hne, hv⟩ => ?_
    have hxb : c.reg rFX ≠ s.2 := fun h => hne (hiff.mpr h)
    obtain ⟨f', hW'⟩ := walk_step (by omega) hW hxb
    have hxn : c.reg rFX < n := by
      have := (mem_faceVerts.mp (walk_mem hW)).2.1; omega
    have hlen := length_walk_lt hW
    refine ⟨?_, ?_⟩
    · have hlen' := length_walk_lt hW'
      have hfs := fOff_succ (pg := pg) (n := n) ht
      rw [← hsdef] at hfs
      have := fOff_le_faceCat (pg := pg) (n := n) (t + 1)
      have := hS.blast
      have hfr := hS.free
      simp only [List.length_append, List.length_singleton, length_doneOf] at hfr hlen'
      have hpr : (RAM.run (push rFX) c).reg rLAST = c.reg rLAST := push_run (v := rFX) hS (by omega)
        |>.2 rLAST (by decide) (by decide)
      have hpx : (RAM.run (push rFX) c).reg rFX = c.reg rFX := push_run (v := rFX) hS (by omega)
        |>.2 rFX (by decide) (by decide)
      refine AddrOK.seq (AddrOK.seq ((addrOK_push _ _).mpr (by omega))
        (by rw [addrOK_ld, hpr, hpx]; omega)) (AddrOK.of_memFree rfl)
    obtain ⟨hS₁, hrr₁⟩ := push_run (v := rFX) hS (by omega)
    have hld : RAM.run (ld rFX rLAST rFX) (RAM.run (push rFX) c) =
        (RAM.run (push rFX) c).setReg rFX (lastNb pg n (c.reg rFX)) := by
      rw [run_ld, hrr₁ rFX (by decide) (by decide), hS₁.last.get hxn]
    have hS₂ := (FaSt.indep F₀ m₀ (t + 1) _).setReg (d := rFX) (by decide)
      (lastNb pg n (c.reg rFX)) hS₁
    rw [show RAM.run (.seq faStep faCond) c =
      RAM.run faCond (RAM.run (ld rFX rLAST rFX) (RAM.run (push rFX) c)) from rfl, hld]
    obtain ⟨hrT, hag⟩ := faCond_run ((RAM.run (push rFX) c).setReg rFX (lastNb pg n (c.reg rFX)))
    have hS₃ := (FaSt.indep F₀ m₀ (t + 1) _) _ _ (hag.mono (by decide)) hS₂
    have hrFX : (RAM.run faCond ((RAM.run (push rFX) c).setReg rFX
        (lastNb pg n (c.reg rFX)))).reg rFX = lastNb pg n (c.reg rFX) := by
      rw [hag.reg rFX (by decide)]; simp
    have hrFB : (RAM.run faCond ((RAM.run (push rFX) c).setReg rFX
        (lastNb pg n (c.reg rFX)))).reg rFB = s.2 := by
      rw [hag.reg rFB (by decide)]; simp +decide [hrr₁ rFB (by decide) (by decide), hB]
    refine ⟨⟨cur ++ [c.reg rFX], f', by rw [← List.append_assoc]; exact hS₃, ?_, hrFB, ?_, ?_⟩, ?_⟩
    · rw [hrFX]; exact hW'
    · rw [hag.reg rFT (by decide)]; simp +decide [hrr₁ rFT (by decide) (by decide), hT]
    · rw [hrT, hrFX]
      simp +decide [hrr₁ rFB (by decide) (by decide), hB]; omega
    · rw [← hv]
      unfold wMu
      rw [hS₃.free, hS.free]
      simp only [List.length_append, List.length_singleton, length_doneOf]
      omega

theorem faBody_spec (hP : IsPolygon pg n) (F₀ : ℕ) (m₀ : ℕ → ℕ) (hS : faEnd pg n F₀ ≤ S) (t : ℕ)
    (ht : t < (segOrder pg n).length) :
    HTB S faBody (fun c => FaSt pg n F₀ m₀ t (doneOf pg n t) c ∧ c.reg rFT = t ∧
        c.reg gNS = (segOrder pg n).length)
      (fun c => FaSt pg n F₀ m₀ (t + 1) (doneOf pg n (t + 1)) c ∧ c.reg rFT = t ∧
        c.reg gNS = (segOrder pg n).length)
      (9 * (faceVerts pg n ((segOrder pg n).getD t (0, 0))).length + 21) := by
  have h₁ := (faPre_spec hP F₀ m₀ hS t ht).pre (P' := fun c => FaSt pg n F₀ m₀ t (doneOf pg n t) c ∧
    c.reg rFT = t ∧ c.reg gNS = (segOrder pg n).length) fun c h => ⟨h.1, h.2.1⟩
  have h₃ : HTB S (push rFB) (fun c => WInv pg n F₀ m₀ t (segOrder pg n)[t] c ∧ c.reg rT = 0)
      (fun c => FaSt pg n F₀ m₀ (t + 1) (doneOf pg n (t + 1)) c ∧ c.reg rFT = t ∧
        c.reg gNS = (segOrder pg n).length) 3 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨cur, f, hS', hW, hB, hT, hiff⟩, h0⟩ => ?_
    have hx := hiff.mp h0
    rw [hx] at hW
    have hface := walk_done hW
    refine ⟨?_, ?_⟩
    · have := congrArg List.length hface
      have := fOff_succ (pg := pg) (n := n) ht
      have := fOff_le_faceCat (pg := pg) (n := n) (t + 1)
      have hfr := hS'.free
      unfold faEnd at hS
      simp only [List.length_append, List.length_singleton, length_doneOf] at *
      rw [addrOK_push]; omega
    have hS := hS'
    obtain ⟨hS', hrr⟩ := push_run (v := rFB) hS (by omega)
    rw [hB, List.append_assoc, hface, ← doneOf_succ ht] at hS'
    refine ⟨hS', ?_, ?_⟩
    · rw [hrr _ (by decide) (by decide), hT]
    · rw [hrr _ (by decide) (by decide), hS.ns]
  refine (h₁.seq ((walk_spec hP F₀ m₀ hS t ht).seq h₃)).weaken ?_
  rw [getD_of_lt ht]; omega

/-- The state before the faces. -/
def FaIn (pg : Graph) (n : ℕ) (c : Config) : Prop := Zf c ∧ OrdSt pg n c ∧ EnumSt pg n c

theorem faInit_spec (F₀ : ℕ) (m₀ : ℕ → ℕ) :
    HT faInit (fun c => FaIn pg n c ∧ c.reg rFREE = F₀ ∧ c.mem = m₀)
      (fun c => FaSt pg n F₀ m₀ 0 (doneOf pg n 0) c ∧ c.reg gNS = (segOrder pg n).length) 7 := by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hZ, hO, hE⟩, hF, hm⟩ => ?_
  simp only [faInit, run_seq', run_addc (show gNS ≠ rT by decide),
    run_alloc (show rFN1 ≠ rT by decide) (show gFOFF ≠ rFN1 by decide),
    run_mov (show rFREE ≠ rT by decide)]
  have hns : c.reg gNS = (segOrder pg n).length := by rw [hE.1, length_segOrder]
  have h1 := hO.1.2
  have h2 := hO.2.1.2
  have h3 := hO.2.2.2
  have h4 := hE.2.2.2.1.2
  have h5 := hE.2.2.2.2.2.1.2
  simp only [List.length_map, length_ord3] at h1 h2 h3 h4
  unfold Zf at hZ
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals simp +decide only [setReg_reg, ↓reduceIte, setReg_mem, hF, hns, doneOf,
    List.take_zero, List.flatMap_nil, List.length_nil, tab_zero, arr_nil, length_ord3]
  all_goals try omega
  · exact hO.2.1.1
  · exact hO.2.2.1
  · exact hO.1.1
  · exact hE.2.2.2.1.1
  · exact hE.2.2.2.2.2.1.1
  · rw [hF] at hZ; exact hZ.mono (by omega)
  · rw [hm]; exact SameOn.refl _ _

/-- **Stage E**: the faces, in `O(|pg|)` steps. -/
theorem stageE_spec (hP : IsPolygon pg n) :
    HGMB S stageE WE (FaIn pg n) (fun c => FaceSt pg n c ∧ Zf c)
      (18 * pg.length + 25 * pg.length + 20) (3 * pg.length + 1) := by
  refine HGMB.ofGhost (by decide) (fun _ h => h) fun F₀ m₀ hS => ?_
  have hE : faEnd pg n F₀ ≤ S := by
    have := length_faceCat_le hP
    have := length_segOrder (pg := pg) (n := n)
    have := length_segEnum_le (pg := pg) (n := n)
    unfold faEnd; omega
  have hl := HTB.forUp (i := rFT) (n := gNS) (N := (segOrder pg n).length) (body := faBody)
    (fun t => FaSt pg n F₀ m₀ t (doneOf pg n t))
    (fun t => 9 * (faceVerts pg n ((segOrder pg n).getD t (0, 0))).length + 21)
    (by decide) (by decide) (by decide) (fun t => FaSt.indep F₀ m₀ t _ |>.mono (by decide))
    (fun t ht => faBody_spec hP F₀ m₀ hE t ht)
  have h₃ : HTB S faFin (fun c => FaSt pg n F₀ m₀ (segOrder pg n).length
        (doneOf pg n (segOrder pg n).length) c ∧ c.reg rFT = (segOrder pg n).length ∧
        c.reg gNS = (segOrder pg n).length)
      (fun c => (FaceSt pg n c ∧ Zf c) ∧ SameOn (· < F₀) m₀ c.mem ∧ F₀ ≤ c.reg rFREE ∧
        c.reg rFREE ≤ F₀ + (3 * pg.length + 1)) 3 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hS, _, hN⟩ => ?_
    refine ⟨by unfold faEnd at hE; addr_ok [faFin, hN, hS.foff], ?_⟩
    have hrr : ∀ r, r ∉ wregs faFin → (RAM.run faFin c).reg r = c.reg r :=
      fun r hr => run_reg_of_not_mem (by decide) hr c
    have hmem : (RAM.run faFin c).mem =
        upd c.mem (F₀ + (segOrder pg n).length) (fOff pg n (segOrder pg n).length) := by
      simp +decide only [faFin, run_seq', run_sub, run_st (show rFI ≠ rT by decide), setReg_reg,
        ↓reduceIte, setReg_mem, setMem_mem_upd, hN, hS.foff, hS.free, hS.fv, length_doneOf]
      congr 1; omega
    have hF := hS.free
    have hdone : doneOf pg n (segOrder pg n).length = faceCat pg n := by
      rw [doneOf, List.take_length]; rfl
    rw [hdone] at hF
    have hfv := hS.fvs
    rw [hdone] at hfv
    have hoffs := (hS.offs.upd_of_disjoint (a := F₀ + (segOrder pg n).length)
      (v := fOff pg n (segOrder pg n).length) (by omega)).snoc (by simp)
    have hrF : (RAM.run faFin c).reg rFREE = c.reg rFREE := hrr _ (by decide)
    have hrO : (RAM.run faFin c).reg gFOFF = c.reg gFOFF := hrr _ (by decide)
    have hrV : (RAM.run faFin c).reg gFV = c.reg gFV := hrr _ (by decide)
    refine ⟨⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩, ?_, ?_, ?_⟩
    all_goals try simp only [hrF, hrO, hrV, hmem, hS.foff, hS.fv, hF]
    · rw [← map_fOff]; exact hoffs.toArr
    · rw [faceOffs, prefixSums, List.length_map, List.length_range, List.length_map]
      omega
    · exact hfv.upd_of_disjoint (by omega)
    · omega
    · unfold Zf; rw [hrF, hmem]; exact hS.zero.upd (by rw [hS.free]; omega)
    · exact hS.same.upd_of_ge (by omega) _
    · omega
    · have := length_faceCat_le hP
      have := length_segOrder (pg := pg) (n := n)
      have := length_segEnum_le (pg := pg) (n := n)
      omega
  refine ((HTB.of_HT rfl (faInit_spec F₀ m₀)).seq (hl.seq h₃)).weaken ?_
  have hsum := sum_range_getD (fun s => (faceVerts pg n s).length) (0, 0) (segOrder pg n)
  have hcat : ((segOrder pg n).map fun s => (faceVerts pg n s).length).sum = (faceCat pg n).length := by
    rw [faceCat, List.length_flatMap]
  have h1 := length_faceCat_le hP
  have h2 := length_segOrder (pg := pg) (n := n)
  have h3 := length_segEnum_le (pg := pg) (n := n)
  have : ∑ j ∈ Finset.range (segOrder pg n).length,
      (9 * (faceVerts pg n ((segOrder pg n).getD j (0, 0))).length + 21 + 4) =
      9 * (faceCat pg n).length + 25 * (segOrder pg n).length := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, hcat]
    simp; ring
  rw [this]; omega

end STACS2027.RAM.P1
