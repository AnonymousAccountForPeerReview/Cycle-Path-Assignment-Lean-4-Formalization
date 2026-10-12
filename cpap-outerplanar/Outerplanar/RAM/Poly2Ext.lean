module

public import Outerplanar.RAM.Poly2Lib
import Mathlib.Tactic

/-!
# Phase P2 of the polygon solver: extending a partial path through a slot

The step of the fold of `rpF` through a slot `(x, y)` (`extendParts_eq`) extends every partial
path `pe` (a record `[pe.2, pe.1…]` at `rPP`) by `extPe k pe y cf`, where `cf` are the final
partial paths of the child segment `(x, y)` (records at `rCB`, `rCN` of them; none for a side):

* `em2`: the path through the slot itself, `pe.1 ++ [y]` (if `pe.2 < k`);
* for `l = 0, …, k - pe.2 - 2` (`lBody`), a scan of the child's records (`cBody`): a record
  `r` with `l + 2` edges gives `pe.1 ++ r.1.tail` (`emC`).

The new records are pushed onto the stream at `q` and counted in `rQN`. `peBody_spec`: one
partial path within `TPe k` steps. All triples are bounded (`HGB S`): each takes the hypothesis
that the stream, once extended, ends at or below `S` (the loads read below the free pointer).
-/

@[expose] public section

namespace STACS2027.RAM.P2

open P1

/-! ### Registers -/

/-- `k`. -/
abbrev rK : ℕ := 84
/-- Base of the table of the addresses of the final partial paths, per segment. -/
abbrev rFB : ℕ := 86
/-- Base of the table of the numbers of final partial paths, per segment. -/
abbrev rFC : ℕ := 87
/-- `k - 1`. -/
abbrev rKm1 : ℕ := 88
/-- The second end `y` of the slot. -/
abbrev rY : ℕ := 120
/-- Address of the child's records. -/
abbrev rCB : ℕ := 121
/-- Number of the child's records. -/
abbrev rCN : ℕ := 122
/-- Number of new records. -/
abbrev rQN : ℕ := 123
/-- Address of the current record. -/
abbrev rPP : ℕ := 124
/-- Edges of the current record. -/
abbrev rE : ℕ := 125
/-- Number of rounds `l`. -/
abbrev rLN : ℕ := 126
/-- The round `l`. -/
abbrev rL : ℕ := 127
/-- Address of the current child record. -/
abbrev rCP : ℕ := 128
/-- Counter of the child records. -/
abbrev rCJ2 : ℕ := 129
/-- Edges of the current child record. -/
abbrev rER : ℕ := 130
/-- Temporary. -/
abbrev rW : ℕ := 131
/-- `l + 2`. -/
abbrev rW2 : ℕ := 132
/-- Temporary. -/
abbrev rW3 : ℕ := 133
/-- Counter of the records. -/
abbrev rPJ : ℕ := 134
/-- Number of records. -/
abbrev rPN : ℕ := 139

/-! ### Programs -/

/-- Prepare copying the entries `pe.1` of the current record. -/
def prepCp : Stmt := .seq (addc rCS rPP 1) (addc rCL rE 1)
/-- Push `e + er`; prepare copying `pe.1`. -/
def emCa : Stmt := .seq (.add rW rE rER) (.seq (push rW) prepCp)
/-- Prepare copying the child's entries after the first. -/
def emCb : Stmt := .seq (addc rCS rCP 2) (mov rCL rER)
/-- Emit `(pe.1 ++ r.1.tail, pe.2 + r.2)`. -/
def emC : Stmt := .seq emCa (.seq copy (.seq emCb (.seq copy (inc rQN))))
/-- Read the child record and compare its edges with `l + 2`. -/
def cTest : Stmt :=
  .seq (.load rER rCP) (.seq (.sub rW rER rW2) (.seq (.sub rW3 rW2 rER) (.add rW rW rW3)))
/-- Advance to the next child record. -/
def cAdv : Stmt := .seq (.add rCP rCP rER) (addc rCP rCP 2)
/-- One child record. -/
def cBody : Stmt := .seq cTest (.seq (.ifz rW emC .skip) cAdv)
/-- The scan of the child records. -/
def cLoop : Stmt := forUp rCJ2 rCN cBody
/-- Start a round. -/
def lInit : Stmt := .seq (mov rCP rCB) (addc rW2 rL 2)
/-- One round `l`. -/
def lBody : Stmt := .seq lInit cLoop
/-- The rounds. -/
def lLoop : Stmt := forUp rL rLN lBody
/-- Push `e + 1`; prepare copying `pe.1`. -/
def em2a : Stmt := .seq (addc rW rE 1) (.seq (push rW) prepCp)
/-- Push `y`, count. -/
def em2b : Stmt := .seq (push rY) (inc rQN)
/-- Emit `(pe.1 ++ [y], pe.2 + 1)`. -/
def em2 : Stmt := .seq em2a (.seq copy em2b)
/-- Read the edges; `rW := k - e`. -/
def peHead : Stmt := .seq (.load rE rPP) (.sub rW rK rE)
/-- `rLN := k - e - 1`. -/
def peMid : Stmt := .seq (.sub rLN rK rE) (subc rLN rLN 1)
/-- Advance to the next record. -/
def peAdv : Stmt := .seq (.add rPP rPP rE) (addc rPP rPP 2)
/-- **One partial path.** -/
def peBody : Stmt := .seq peHead (.seq (.ifz rW .skip em2) (.seq peMid (.seq lLoop peAdv)))
/-- **All partial paths** of the current list. -/
def peLoop : Stmt := forUp rPJ rPN peBody

/-! ### Bounds -/

/-- Steps for one child record. -/
def TC (k : ℕ) : ℕ := 18 * k + 37
/-- Steps for one round. -/
def TL (k : ℕ) : ℕ := Poly.partsBound k * (TC k + 4) + 7
/-- Steps for one partial path. -/
def TPe (k : ℕ) : ℕ := k * (TL k + 4) + 9 * k + 38
/-- Steps for all partial paths of a list. -/
def TPL (k : ℕ) : ℕ := Poly.partsBound k * (TPe k + 4) + 3

/-! ### Contexts -/

/-- The context of a slot step: `k`, the slot's second end `y`, the child records `cf` at
`cb`. -/
@[mk_iff] structure SCtx (k y cb : ℕ) (cf : List (List ℕ × ℕ)) (c : Config) : Prop where
  rk : c.reg rK = k
  ry : c.reg rY = y
  rcb : c.reg rCB = cb
  rcn : c.reg rCN = cf.length
  bchl : Bel cb (enc cf) c

theorem SCtx.stable {W : List ℕ} (h : rK ∉ W ∧ rY ∉ W ∧ rCB ∉ W ∧ rCN ∉ W) (k y cb : ℕ)
    (cf : List (List ℕ × ℕ)) : Stable W (SCtx k y cb cf) := fun c c' hc hg =>
  ⟨(hg.reg _ h.1).trans hc.rk, (hg.reg _ h.2.1).trans hc.ry, (hg.reg _ h.2.2.1).trans hc.rcb,
    (hg.reg _ h.2.2.2).trans hc.rcn, stable_bel W _ _ c c' hc.bchl hg⟩

/-- The context of the extension of the partial path `pe`, its record at `pp`. -/
def PCtx (k y cb : ℕ) (cf : List (List ℕ × ℕ)) (pp : ℕ) (pe : List ℕ × ℕ) (c : Config) : Prop :=
  SCtx k y cb cf c ∧ c.reg rE = pe.2 ∧ c.reg rPP = pp ∧ Bel pp (pe.2 :: pe.1) c

theorem PCtx.stable {W : List ℕ} (h : rK ∉ W ∧ rY ∉ W ∧ rCB ∉ W ∧ rCN ∉ W ∧ rE ∉ W ∧ rPP ∉ W)
    (k y cb : ℕ) (cf : List (List ℕ × ℕ)) (pp : ℕ) (pe : List ℕ × ℕ) :
    Stable W (PCtx k y cb cf pp pe) := fun c c' hc hg =>
  ⟨SCtx.stable ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩ k y cb cf c c' hc.1 hg,
    (hg.reg _ h.2.2.2.2.1).trans hc.2.1, (hg.reg _ h.2.2.2.2.2).trans hc.2.2.1,
    stable_bel W _ _ c c' hc.2.2.2 hg⟩

/-- The record `j` of the partial paths `l` at `b`. -/
theorem Bel.rec {b : ℕ} {l : List (List ℕ × ℕ)} {c : Config} (h : Bel b (enc l) c) {j : ℕ}
    (hj : j < l.length) : Bel (b + encOff l j) (l[j].2 :: l[j].1) c := by
  have he : enc l = enc (l.take j) ++ (l[j].2 :: l[j].1) ++ enc (l.drop (j + 1)) := by
    rw [← enc_take_succ hj, ← enc_append, List.take_append_drop]
  rw [he] at h
  exact h.sub

/-- The entries of a record after the first two. -/
theorem Bel.tail {b x : ℕ} {l : List ℕ} {c : Config} (h : Bel b (x :: l) c) (hl : l ≠ []) :
    Bel (b + 2) l.tail c := by
  obtain ⟨-, h⟩ := h.cons
  cases l with
  | nil => exact absurd rfl hl
  | cons y l => simpa [Nat.add_assoc] using h.cons.2

/-- The new records of a prefix of a list of items. -/
theorem enc_flatMap_take_le {α : Type*} (M : List α) (f : α → List (List ℕ × ℕ)) {i j : ℕ}
    (hij : i ≤ j) : (enc ((M.take i).flatMap f)).length ≤ (enc ((M.take j).flatMap f)).length := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [List.take_add, List.flatMap_append, enc_append, List.length_append]
  omega

/-! ### Pushing a value and preparing a copy -/

/-- A store-free block `pre` computing `rW`, a push of `rW`, and the preparation of the copy of
the current record's entries. -/
theorem pushPrep_run {pre : Stmt} (hpre : LoopFree pre) (hst : stores pre = false)
    (hw : writes pre = false) (hW : ∀ r ∈ wregs pre, r ∈ [rT, rW]) {q : ℕ} {out : List ℕ}
    {c : Config} (hS : Strm q out c) :
    Strm q (out ++ [(RAM.run pre c).reg rW]) (RAM.run (.seq pre (.seq (push rW) prepCp)) c) ∧
      (RAM.run (.seq pre (.seq (push rW) prepCp)) c).reg rCS = c.reg rPP + 1 ∧
      (RAM.run (.seq pre (.seq (push rW) prepCp)) c).reg rCL = c.reg rE + 1 ∧
      Grow [rT, rW, rFREE, rCS, rCL] c (RAM.run (.seq pre (.seq (push rW) prepCp)) c) := by
  set c₁ := RAM.run pre c with hc₁
  have hA1 : Agree [rT, rW] c c₁ := agree_run hpre hst hw hW c
  have h1 : Strm q out c₁ := strm_agree hA1 (by decide) hS
  have h2 := push_strm h1 rW
  have hg2 := push_grow rW c₁
  set c₂ := RAM.run (push rW) c₁ with hc₂
  have hA3 : Agree [rT, rCS, rCL] c₂ (RAM.run prepCp c₂) :=
    agree_run (by decide) rfl rfl (by decide) c₂
  have hrun : RAM.run (.seq pre (.seq (push rW) prepCp)) c = RAM.run prepCp c₂ := rfl
  have hpp : c₂.reg rPP = c.reg rPP := by
    rw [hc₂, push_reg _ _ (by decide) (by decide), hA1.reg _ (by decide)]
  have he : c₂.reg rE = c.reg rE := by
    rw [hc₂, push_reg _ _ (by decide) (by decide), hA1.reg _ (by decide)]
  rw [hrun]
  refine ⟨strm_agree hA3 (by decide) h2, ?_, ?_, ?_⟩
  · simp +decide [prepCp, run_addc, hpp]
  · simp +decide [prepCp, run_addc, he]
  · exact (grow_of_agree hA1 (by decide) (by decide)).trans
      ((hg2.mono (by decide)).trans (grow_of_agree hA3 (by decide) (by decide)))

/-! ### Emitting through a child record -/

theorem emC_spec {S : ℕ} (q : ℕ) (out : List ℕ) (pe r : List ℕ × ℕ) (pp cp cnt : ℕ)
    (hpe : pe.1.length = pe.2 + 1) (hr : r.1.length = r.2 + 1)
    (hSz : q + (out ++ enc [(pe.1 ++ r.1.tail, pe.2 + r.2)]).length ≤ S) :
    HGB S emC (wregs emC)
      (fun c => Strm q out c ∧ c.reg rQN = cnt ∧ c.reg rE = pe.2 ∧ c.reg rER = r.2 ∧
        c.reg rPP = pp ∧ c.reg rCP = cp ∧ Bel (pp + 1) pe.1 c ∧ Bel (cp + 2) r.1.tail c)
      (fun c => Strm q (out ++ enc [(pe.1 ++ r.1.tail, pe.2 + r.2)]) c ∧ c.reg rQN = cnt + 1)
      (9 * pe.2 + 9 * r.2 + 29) := by
  have htl : r.1.tail.length = r.2 := by rw [List.length_tail, hr]; omega
  simp only [List.length_append, enc_singleton, List.length_cons] at hSz
  have h₁ : HGB S emCa (wregs emC)
      (fun c => Strm q out c ∧ c.reg rQN = cnt ∧ c.reg rE = pe.2 ∧ c.reg rER = r.2 ∧
        c.reg rPP = pp ∧ c.reg rCP = cp ∧ Bel (pp + 1) pe.1 c ∧ Bel (cp + 2) r.1.tail c)
      (fun c => (Strm q (out ++ [pe.2 + r.2]) c ∧ Bel (pp + 1) pe.1 c ∧ c.reg rCS = pp + 1 ∧
        c.reg rCL = pe.1.length) ∧ (c.reg rQN = cnt ∧ c.reg rER = r.2 ∧ c.reg rCP = cp ∧
        Bel (cp + 2) r.1.tail c)) 8 := by
    refine HGB.run (by decide) (by decide) fun c hc => ?_
    obtain ⟨hS, hn, he, her, hpp, hcp, hb1, hb2⟩ := hc
    have hfr := hS.2.1
    refine ⟨by addr_ok [emCa, push, prepCp], ?_⟩
    rw [show RAM.run emCa c = RAM.run (.seq (.add rW rE rER) (.seq (push rW) prepCp)) c from rfl]
    obtain ⟨hS', hcs, hcl, hg⟩ := pushPrep_run (pre := .add rW rE rER) (by decide) rfl rfl
      (by decide) hS
    have hg' : Grow (wregs emC) c (RAM.run (.seq (.add rW rE rER) (.seq (push rW) prepCp)) c) :=
      hg.mono (by decide)
    have hv : (RAM.run (.add rW rE rER) c).reg rW = pe.2 + r.2 := by simp [he, her]
    rw [hv] at hS'
    refine ⟨⟨⟨hS', stable_bel _ _ _ c _ hb1 hg', by rw [hcs, hpp], by rw [hcl, he, hpe]⟩,
      ?_, ?_, ?_, stable_bel _ _ _ c _ hb2 hg'⟩, hg'⟩
    · rw [hg.reg _ (by decide), hn]
    · rw [hg.reg _ (by decide), her]
    · rw [hg.reg _ (by decide), hcp]
  have h₂ := HGB.frame (copy_spec (S := S) q (pp + 1) (out ++ [pe.2 + r.2]) pe.1
    (by simp only [List.length_append, List.length_singleton]; omega))
    (F := fun c => c.reg rQN = cnt ∧ c.reg rER = r.2 ∧ c.reg rCP = cp ∧ Bel (cp + 2) r.1.tail c)
    (by stab)
  have h₃ : HGB S emCb (wregs emC)
      (fun c => Strm q (out ++ [pe.2 + r.2] ++ pe.1) c ∧ (c.reg rQN = cnt ∧ c.reg rER = r.2 ∧
        c.reg rCP = cp ∧ Bel (cp + 2) r.1.tail c))
      (fun c => (Strm q (out ++ [pe.2 + r.2] ++ pe.1) c ∧ Bel (cp + 2) r.1.tail c ∧
        c.reg rCS = cp + 2 ∧ c.reg rCL = r.1.tail.length) ∧ c.reg rQN = cnt) 4 := by
    refine (HGB.runM (s := emCb) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    obtain ⟨hS, hn, her, hcp, hb⟩ := hc
    have hA : Agree [rT, rCS, rCL] c (RAM.run emCb c) := agree_run (by decide) rfl rfl (by decide) c
    refine ⟨⟨strm_agree hA (by decide) hS, hb.mono hA.mem (by rw [hA.reg _ (by decide)]), ?_, ?_⟩,
      by rw [hA.reg _ (by decide), hn]⟩
    · simp +decide [emCb, run_addc, run_mov, hcp]
    · simp +decide [emCb, run_addc, run_mov, her, htl]
  have h₄ := HGB.frame (copy_spec (S := S) q (cp + 2) (out ++ [pe.2 + r.2] ++ pe.1) r.1.tail
    (by simp only [List.length_append, List.length_singleton]; omega))
    (F := fun c => c.reg rQN = cnt) (by stab)
  have h₅ : HGB S (inc rQN) (wregs emC)
      (fun c => Strm q (out ++ [pe.2 + r.2] ++ pe.1 ++ r.1.tail) c ∧ c.reg rQN = cnt)
      (fun c => Strm q (out ++ enc [(pe.1 ++ r.1.tail, pe.2 + r.2)]) c ∧ c.reg rQN = cnt + 1) 2 := by
    refine (HGB.runM (s := inc rQN) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    obtain ⟨hS, hn⟩ := hc
    have hA : Agree [rT, rQN] c (RAM.run (inc rQN) c) := agree_run (by decide) rfl rfl (by decide) c
    have he : out ++ [pe.2 + r.2] ++ pe.1 ++ r.1.tail = out ++ enc [(pe.1 ++ r.1.tail, pe.2 + r.2)] := by
      simp [enc_singleton]
    rw [he] at hS
    exact ⟨strm_agree hA (by decide) hS, by simp +decide [run_inc, hn]⟩
  refine (h₁.seq ((h₂.mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl).seq
    (h₃.seq ((h₄.mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl).seq h₅)))).weaken ?_
  rw [hpe, htl]
  omega

/-! ### The scan of the child records -/

/-- The new records from the child records `cf.take j` in round `l`. -/
abbrev emJ (pe : List ℕ × ℕ) (cf : List (List ℕ × ℕ)) (l j : ℕ) : List (List ℕ × ℕ) :=
  (cf.take j).flatMap (emitR pe l)

/-- The invariant of the scan of the child records in round `l`, after `j` records. -/
def CInv (k y cb : ℕ) (cf : List (List ℕ × ℕ)) (pp : ℕ) (pe : List ℕ × ℕ) (q : ℕ)
    (out : List ℕ) (cnt l j : ℕ) (c : Config) : Prop :=
  PCtx k y cb cf pp pe c ∧ Strm q (out ++ enc (emJ pe cf l j)) c ∧
    c.reg rQN = cnt + (emJ pe cf l j).length ∧ c.reg rCP = cb + encOff cf j ∧ c.reg rW2 = l + 2

theorem CInv.indep (k y cb : ℕ) (cf : List (List ℕ × ℕ)) (pp : ℕ) (pe : List ℕ × ℕ) (q : ℕ)
    (out : List ℕ) (cnt l j : ℕ) :
    Indep [rT, rCJ2, rER, rW, rW3] (CInv k y cb cf pp pe q out cnt l j) := by
  indep [CInv, PCtx, sCtx_iff, Strm, Bel]

@[simp] theorem emJ_zero (pe : List ℕ × ℕ) (cf : List (List ℕ × ℕ)) (l : ℕ) : emJ pe cf l 0 = [] :=
  rfl

theorem emJ_succ (pe : List ℕ × ℕ) (cf : List (List ℕ × ℕ)) (l : ℕ) {j : ℕ} (hj : j < cf.length) :
    emJ pe cf l (j + 1) = emJ pe cf l j ++ emitR pe l cf[j] := by
  simp only [emJ, take_succ_eq hj, List.flatMap_append, List.flatMap_singleton]

theorem emJ_len_le (pe : List ℕ × ℕ) (cf : List (List ℕ × ℕ)) (l : ℕ) {i j : ℕ} (hij : i ≤ j) :
    (enc (emJ pe cf l i)).length ≤ (enc (emJ pe cf l j)).length :=
  enc_flatMap_take_le cf _ hij

theorem cBody_spec {S : ℕ} (k y cb : ℕ) (cf : List (List ℕ × ℕ)) (pp : ℕ) (pe : List ℕ × ℕ)
    (q : ℕ) (out : List ℕ) (cnt l : ℕ) (hpe : pe.1.length = pe.2 + 1) (hpek : pe.2 ≤ k)
    (hcf : ∀ r ∈ cf, r.2 ≤ k ∧ r.1.length = r.2 + 1) (j : ℕ) (hj : j < cf.length)
    (hSz : q + (out ++ enc (emJ pe cf l (j + 1))).length ≤ S) :
    HGB S cBody (wregs cLoop)
      (fun c => CInv k y cb cf pp pe q out cnt l j c ∧ c.reg rCJ2 = j ∧ c.reg rCN = cf.length)
      (fun c => CInv k y cb cf pp pe q out cnt l (j + 1) c ∧ c.reg rCJ2 = j ∧
        c.reg rCN = cf.length) (TC k) := by
  obtain ⟨hrk, hrl⟩ := hcf cf[j] (List.getElem_mem hj)
  have hrne : cf[j].1 ≠ [] := by intro h; rw [h] at hrl; simp at hrl
  have hlen : (out ++ enc (emJ pe cf l (j + 1))).length =
      (out ++ enc (emJ pe cf l j)).length + (enc (emitR pe l cf[j])).length := by
    rw [emJ_succ pe cf l hj, enc_append]; simp only [List.length_append]; omega
  -- the test
  have h₁ : HGB S cTest (wregs cLoop)
      (fun c => CInv k y cb cf pp pe q out cnt l j c ∧ c.reg rCJ2 = j ∧ c.reg rCN = cf.length)
      (fun c => (CInv k y cb cf pp pe q out cnt l j c ∧ c.reg rCJ2 = j ∧ c.reg rCN = cf.length) ∧
        c.reg rER = cf[j].2 ∧ (c.reg rW = 0 ↔ cf[j].2 = l + 2)) 4 := by
    refine (HGB.runR (s := cTest) (by decide) (by decide) (by decide) (by decide) (by decide)
      fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rER, rW, rW3] c (RAM.run cTest c) :=
      agree_run (by decide) rfl rfl (by decide) c
    obtain ⟨hI, hj', hn⟩ := hc
    have hrecB := (hI.1.1.bchl.rec hj).2
    have hrec := (hI.1.1.bchl.rec hj).cons.1
    have hcp' := hI.2.2.2.1
    have hw2 := hI.2.2.2.2
    have hfr := hI.2.1.2.1
    simp only [List.length_cons] at hrecB
    refine ⟨by addr_ok [cTest, hcp'], ?_⟩
    refine ⟨⟨(CInv.indep k y cb cf pp pe q out cnt l j).mono (by decide) c _ hA hI,
      by rw [hA.reg _ (by decide), hj'], by rw [hA.reg _ (by decide), hn]⟩, ?_, ?_⟩
    · simp +decide [cTest, hcp', hrec]
    · simp +decide [cTest, hcp', hrec, hw2]; omega
  -- the branch
  have h₂ : HGB S (.ifz rW emC .skip) (wregs cLoop)
      (fun c => (CInv k y cb cf pp pe q out cnt l j c ∧ c.reg rCJ2 = j ∧ c.reg rCN = cf.length) ∧
        c.reg rER = cf[j].2 ∧ (c.reg rW = 0 ↔ cf[j].2 = l + 2))
      (fun c => (PCtx k y cb cf pp pe c ∧ c.reg rCP = cb + encOff cf j ∧ c.reg rW2 = l + 2 ∧
        c.reg rCJ2 = j ∧ c.reg rER = cf[j].2) ∧ Strm q (out ++ enc (emJ pe cf l (j + 1))) c ∧
        c.reg rQN = cnt + (emJ pe cf l (j + 1)).length) (18 * k + 30) := by
    refine HGB.ifz ?_ ?_
    · refine HGB.of_pre (fun c h => h.1.2.2.mp h.2) fun hl2 => ?_
      have hem := HGB.frame (emC_spec (S := S) q (out ++ enc (emJ pe cf l j)) pe cf[j] pp
        (cb + encOff cf j) (cnt + (emJ pe cf l j).length) hpe hrl
        (by rw [emitR, ite_eq_left hl2] at hlen; rw [List.length_append]; omega))
        (F := fun c => PCtx k y cb cf pp pe c ∧ c.reg rCP = cb + encOff cf j ∧ c.reg rW2 = l + 2 ∧
          c.reg rCJ2 = j ∧ c.reg rER = cf[j].2)
        ((PCtx.stable (by decide) _ _ _ _ _ _).and (by stab))
      refine hem.mono (by decide) ?_ ?_ (by omega)
      · rintro c ⟨⟨⟨⟨hC, hS, hn, hcp', hw2⟩, hj', -⟩, her, -⟩, -⟩
        exact ⟨⟨hS, hn, hC.2.1, her, hC.2.2.1, hcp', hC.2.2.2.cons.2,
          (hC.1.bchl.rec hj).tail hrne⟩, hC, hcp', hw2, hj', her⟩
      · rintro c ⟨⟨hS, hn⟩, hF⟩
        refine ⟨hF, ?_, ?_⟩
        · rw [emJ_succ pe cf l hj, enc_append, ← List.append_assoc, emitR, ite_eq_left hl2]
          exact hS
        · rw [hn, emJ_succ pe cf l hj, emitR, ite_eq_left hl2]; simp; omega
    · refine HGB.of_pre (fun c h => fun h' => h.2 (h.1.2.2.mpr h')) fun hl2 => ?_
      refine (HGB.skip' (W := wregs cLoop)).mono (by decide) (fun _ h => h) ?_ (by omega)
      rintro c ⟨⟨⟨⟨hC, hS, hn, hcp', hw2⟩, hj', -⟩, her, -⟩, -⟩
      refine ⟨⟨hC, hcp', hw2, hj', her⟩, ?_, ?_⟩
      · rw [emJ_succ pe cf l hj, emitR, ite_eq_right hl2, List.append_nil]; exact hS
      · rw [emJ_succ pe cf l hj, emitR, ite_eq_right hl2, List.append_nil]; exact hn
  -- advancing
  have h₃ : HGB S cAdv (wregs cLoop)
      (fun c => (PCtx k y cb cf pp pe c ∧ c.reg rCP = cb + encOff cf j ∧ c.reg rW2 = l + 2 ∧
        c.reg rCJ2 = j ∧ c.reg rER = cf[j].2) ∧ Strm q (out ++ enc (emJ pe cf l (j + 1))) c ∧
        c.reg rQN = cnt + (emJ pe cf l (j + 1)).length)
      (fun c => CInv k y cb cf pp pe q out cnt l (j + 1) c ∧ c.reg rCJ2 = j ∧
        c.reg rCN = cf.length) 3 := by
    refine (HGB.runM (s := cAdv) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rT, rCP] c (RAM.run cAdv c) := agree_run (by decide) rfl rfl (by decide) c
    obtain ⟨⟨hC, hcp', hw2, hj', her⟩, hS, hn⟩ := hc
    refine ⟨⟨(PCtx.stable (W := [rT, rCP]) (by decide) _ _ _ _ _ _) c _ hC
        (grow_of_agree hA (by decide) (by decide)), strm_agree hA (by decide) hS,
        by rw [hA.reg _ (by decide), hn], ?_, by rw [hA.reg _ (by decide), hw2]⟩,
      by rw [hA.reg _ (by decide), hj'], by rw [hA.reg _ (by decide), hC.1.rcn]⟩
    simp +decide only [cAdv, run_seq', run_add, run_addc (show rCP ≠ rT by decide), setReg_reg,
      ↓reduceIte, hcp', her, encOff_succ hj, hrl]
    omega
  exact (h₁.seq (h₂.seq h₃)).weaken (by unfold TC; omega)

theorem cLoop_spec {S : ℕ} (k y cb : ℕ) (cf : List (List ℕ × ℕ)) (pp : ℕ) (pe : List ℕ × ℕ)
    (q : ℕ) (out : List ℕ) (cnt l : ℕ) (hpe : pe.1.length = pe.2 + 1) (hpek : pe.2 ≤ k)
    (hcf : ∀ r ∈ cf, r.2 ≤ k ∧ r.1.length = r.2 + 1) (hcfl : cf.length ≤ Poly.partsBound k)
    (hSz : q + (out ++ enc (emJ pe cf l cf.length)).length ≤ S) :
    HGB S cLoop (wregs cLoop)
      (fun c => CInv k y cb cf pp pe q out cnt l 0 c ∧ c.reg rCN = cf.length)
      (fun c => CInv k y cb cf pp pe q out cnt l cf.length c ∧ c.reg rCJ2 = cf.length ∧
        c.reg rCN = cf.length) (Poly.partsBound k * (TC k + 4) + 3) :=
  HGB.forUpCle (W := wregs cLoop) (i := rCJ2) (n := rCN) (body := cBody)
    (CInv k y cb cf pp pe q out cnt l) (TC k) _ hcfl (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (fun j => (CInv.indep k y cb cf pp pe q out cnt l j).mono
      (by decide))
    (fun j hj => cBody_spec k y cb cf pp pe q out cnt l hpe hpek hcf j hj (by
      have := emJ_len_le pe cf l (show j + 1 ≤ cf.length by omega)
      rw [List.length_append] at hSz ⊢; omega))

/-! ### The rounds -/

/-- The new records of the rounds before `l`. -/
abbrev emL (pe : List ℕ × ℕ) (cf : List (List ℕ × ℕ)) (l : ℕ) : List (List ℕ × ℕ) :=
  (List.range l).flatMap (emitL pe cf)

/-- The invariant of the rounds, before round `l`. -/
def LInv (k y cb : ℕ) (cf : List (List ℕ × ℕ)) (pp : ℕ) (pe : List ℕ × ℕ) (q : ℕ)
    (out : List ℕ) (cnt l : ℕ) (c : Config) : Prop :=
  PCtx k y cb cf pp pe c ∧ Strm q (out ++ enc (emL pe cf l)) c ∧
    c.reg rQN = cnt + (emL pe cf l).length

theorem LInv.indep (k y cb : ℕ) (cf : List (List ℕ × ℕ)) (pp : ℕ) (pe : List ℕ × ℕ) (q : ℕ)
    (out : List ℕ) (cnt l : ℕ) :
    Indep [rT, rL, rCP, rW2, rCJ2, rER, rW, rW3] (LInv k y cb cf pp pe q out cnt l) := by
  indep [LInv, PCtx, sCtx_iff, Strm, Bel]

@[simp] theorem emL_zero (pe : List ℕ × ℕ) (cf : List (List ℕ × ℕ)) : emL pe cf 0 = [] := rfl

theorem emL_succ (pe : List ℕ × ℕ) (cf : List (List ℕ × ℕ)) (l : ℕ) :
    emL pe cf (l + 1) = emL pe cf l ++ emJ pe cf l cf.length := by
  simp only [emL, emJ, List.range_succ, List.flatMap_append, List.flatMap_singleton, emitL,
    List.take_length]

theorem emL_len_le (pe : List ℕ × ℕ) (cf : List (List ℕ × ℕ)) {l N : ℕ} (h : l ≤ N) :
    (enc (emL pe cf l)).length ≤ (enc (emL pe cf N)).length := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [emL_succ, enc_append, List.length_append]; omega

theorem lBody_spec {S : ℕ} (k y cb : ℕ) (cf : List (List ℕ × ℕ)) (pp : ℕ) (pe : List ℕ × ℕ)
    (q : ℕ) (out : List ℕ) (cnt N : ℕ) (hpe : pe.1.length = pe.2 + 1) (hpek : pe.2 ≤ k)
    (hcf : ∀ r ∈ cf, r.2 ≤ k ∧ r.1.length = r.2 + 1) (hcfl : cf.length ≤ Poly.partsBound k)
    (l : ℕ) (hSz : q + (out ++ enc (emL pe cf (l + 1))).length ≤ S) :
    HGB S lBody (wregs lLoop)
      (fun c => LInv k y cb cf pp pe q out cnt l c ∧ c.reg rL = l ∧ c.reg rLN = N)
      (fun c => LInv k y cb cf pp pe q out cnt (l + 1) c ∧ c.reg rL = l ∧ c.reg rLN = N)
      (TL k) := by
  have h₁ : HGB S lInit (wregs lLoop)
      (fun c => LInv k y cb cf pp pe q out cnt l c ∧ c.reg rL = l ∧ c.reg rLN = N)
      (fun c => (CInv k y cb cf pp pe q (out ++ enc (emL pe cf l)) (cnt + (emL pe cf l).length)
        l 0 c ∧ c.reg rCN = cf.length) ∧ (c.reg rL = l ∧ c.reg rLN = N)) 4 := by
    refine (HGB.runM (s := lInit) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rT, rCP, rW2] c (RAM.run lInit c) := agree_run (by decide) rfl rfl (by decide) c
    obtain ⟨⟨hC, hS, hn⟩, hl, hN⟩ := hc
    refine ⟨⟨⟨(PCtx.stable (W := [rT, rCP, rW2]) (by decide) _ _ _ _ _ _) c _ hC
        (grow_of_agree hA (by decide) (by decide)), by simpa [enc_nil] using strm_agree hA (by decide) hS,
        by rw [hA.reg _ (by decide), hn]; simp, ?_, ?_⟩, by rw [hA.reg _ (by decide), hC.1.rcn]⟩,
      by rw [hA.reg _ (by decide), hl], by rw [hA.reg _ (by decide), hN]⟩
    · simp +decide [lInit, run_mov, run_addc, hC.1.rcb, encOff]
    · simp +decide [lInit, run_mov, run_addc, hl]
  have h₂ := HGB.frame (cLoop_spec (S := S) k y cb cf pp pe q (out ++ enc (emL pe cf l))
    (cnt + (emL pe cf l).length) l hpe hpek hcf hcfl
    (by rw [List.append_assoc, ← enc_append, ← emL_succ]; exact hSz))
    (F := fun c => c.reg rL = l ∧ c.reg rLN = N) (by stab)
  refine (h₁.seq (h₂.mono (by decide) (fun _ h => h) ?_ le_rfl)).weaken (by unfold TL; omega)
  rintro c ⟨⟨⟨hC, hS, hn, -, -⟩, -, -⟩, hl, hN⟩
  refine ⟨⟨hC, ?_, ?_⟩, hl, hN⟩
  · rw [emL_succ, enc_append, ← List.append_assoc]; exact hS
  · rw [hn, emL_succ, List.length_append]; omega

theorem lLoop_spec {S : ℕ} (k y cb : ℕ) (cf : List (List ℕ × ℕ)) (pp : ℕ) (pe : List ℕ × ℕ)
    (q : ℕ) (out : List ℕ) (cnt : ℕ) (hpe : pe.1.length = pe.2 + 1) (hpek : pe.2 ≤ k)
    (hcf : ∀ r ∈ cf, r.2 ≤ k ∧ r.1.length = r.2 + 1) (hcfl : cf.length ≤ Poly.partsBound k)
    (hSz : q + (out ++ enc (emL pe cf (k - pe.2 - 1))).length ≤ S) :
    HGB S lLoop (wregs lLoop)
      (fun c => LInv k y cb cf pp pe q out cnt 0 c ∧ c.reg rLN = k - pe.2 - 1)
      (fun c => LInv k y cb cf pp pe q out cnt (k - pe.2 - 1) c ∧ c.reg rL = k - pe.2 - 1 ∧
        c.reg rLN = k - pe.2 - 1) (k * (TL k + 4) + 3) :=
  HGB.forUpCle (W := wregs lLoop) (i := rL) (n := rLN) (body := lBody)
    (LInv k y cb cf pp pe q out cnt) (TL k) k (by omega) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (fun l => (LInv.indep k y cb cf pp pe q out cnt l).mono
      (by decide))
    (fun l hl => lBody_spec k y cb cf pp pe q out cnt _ hpe hpek hcf hcfl l (by
      have := emL_len_le pe cf (show l + 1 ≤ k - pe.2 - 1 by omega)
      rw [List.length_append] at hSz ⊢; omega))

/-! ### The path through the slot itself -/

theorem em2_spec {S : ℕ} (q : ℕ) (out : List ℕ) (pe : List ℕ × ℕ) (pp y cnt : ℕ)
    (hpe : pe.1.length = pe.2 + 1) (hSz : q + (out ++ enc [(pe.1 ++ [y], pe.2 + 1)]).length ≤ S) :
    HGB S em2 (wregs em2)
      (fun c => Strm q out c ∧ c.reg rQN = cnt ∧ c.reg rE = pe.2 ∧ c.reg rPP = pp ∧
        c.reg rY = y ∧ Bel (pp + 1) pe.1 c)
      (fun c => Strm q (out ++ enc [(pe.1 ++ [y], pe.2 + 1)]) c ∧ c.reg rQN = cnt + 1)
      (9 * pe.2 + 26) := by
  simp only [List.length_append, enc_singleton, List.length_cons] at hSz
  have h₁ : HGB S em2a (wregs em2)
      (fun c => Strm q out c ∧ c.reg rQN = cnt ∧ c.reg rE = pe.2 ∧ c.reg rPP = pp ∧
        c.reg rY = y ∧ Bel (pp + 1) pe.1 c)
      (fun c => (Strm q (out ++ [pe.2 + 1]) c ∧ Bel (pp + 1) pe.1 c ∧ c.reg rCS = pp + 1 ∧
        c.reg rCL = pe.1.length) ∧ (c.reg rQN = cnt ∧ c.reg rY = y)) 9 := by
    refine HGB.run (by decide) (by decide) fun c hc => ?_
    obtain ⟨hS, hn, he, hpp, hy, hb⟩ := hc
    have hfr := hS.2.1
    refine ⟨by addr_ok [em2a, push, prepCp], ?_⟩
    rw [show RAM.run em2a c = RAM.run (.seq (addc rW rE 1) (.seq (push rW) prepCp)) c from rfl]
    obtain ⟨hS', hcs, hcl, hg⟩ := pushPrep_run (pre := addc rW rE 1) (by decide) rfl rfl
      (by decide) hS
    have hg' : Grow (wregs em2) c (RAM.run (.seq (addc rW rE 1) (.seq (push rW) prepCp)) c) :=
      hg.mono (by decide)
    have hv : (RAM.run (addc rW rE 1) c).reg rW = pe.2 + 1 := by simp [run_addc, he]
    rw [hv] at hS'
    refine ⟨⟨⟨hS', stable_bel _ _ _ c _ hb hg', by rw [hcs, hpp], by rw [hcl, he, hpe]⟩,
      by rw [hg.reg _ (by decide), hn], by rw [hg.reg _ (by decide), hy]⟩, hg'⟩
  have h₂ := HGB.frame (copy_spec (S := S) q (pp + 1) (out ++ [pe.2 + 1]) pe.1
    (by simp only [List.length_append, List.length_singleton]; omega))
    (F := fun c => c.reg rQN = cnt ∧ c.reg rY = y) (by stab)
  have h₃ : HGB S em2b (wregs em2)
      (fun c => Strm q (out ++ [pe.2 + 1] ++ pe.1) c ∧ (c.reg rQN = cnt ∧ c.reg rY = y))
      (fun c => Strm q (out ++ enc [(pe.1 ++ [y], pe.2 + 1)]) c ∧ c.reg rQN = cnt + 1) 5 := by
    refine HGB.run (by decide) (by decide) fun c hc => ?_
    obtain ⟨hS, hn, hy⟩ := hc
    have hfr := hS.2.1
    simp only [List.length_append, List.length_singleton] at hfr
    refine ⟨by addr_ok [em2b, push], ?_⟩
    have hS₁ := push_strm hS rY
    have hg₁ := push_grow rY c
    have hA : Agree [rT, rQN] (RAM.run (push rY) c) (RAM.run (inc rQN) (RAM.run (push rY) c)) :=
      agree_run (by decide) rfl rfl (by decide) _
    have he : out ++ [pe.2 + 1] ++ pe.1 ++ [y] = out ++ enc [(pe.1 ++ [y], pe.2 + 1)] := by
      simp [enc_singleton]
    rw [hy, he] at hS₁
    refine ⟨⟨strm_agree hA (by decide) hS₁, ?_⟩, ?_⟩
    · simp +decide only [em2b, run_seq', run_inc (show rQN ≠ rT by decide), setReg_reg, ↓reduceIte]
      rw [push_reg _ _ (by decide) (by decide), hn]
    · exact (hg₁.mono (by decide)).trans (grow_of_agree hA (by decide) (by decide))
  refine (h₁.seq ((h₂.mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl).seq h₃)).weaken ?_
  rw [hpe]
  omega

/-! ### One partial path -/

theorem extPe_eq (k : ℕ) (pe : List ℕ × ℕ) (y : ℕ) (cf : List (List ℕ × ℕ)) :
    extPe k pe y cf = emit2 k pe y ++ emL pe cf (k - pe.2 - 1) := rfl

theorem peBody_spec {S : ℕ} (k y cb : ℕ) (cf : List (List ℕ × ℕ)) (pp : ℕ) (pe : List ℕ × ℕ)
    (q : ℕ) (out : List ℕ) (cnt : ℕ) (hpe : pe.1.length = pe.2 + 1) (hpek : pe.2 ≤ k)
    (hcf : ∀ r ∈ cf, r.2 ≤ k ∧ r.1.length = r.2 + 1) (hcfl : cf.length ≤ Poly.partsBound k)
    (hSz : q + (out ++ enc (extPe k pe y cf)).length ≤ S) :
    HGB S peBody (wregs peBody)
      (fun c => SCtx k y cb cf c ∧ c.reg rPP = pp ∧ Bel pp (pe.2 :: pe.1) c ∧ Strm q out c ∧
        c.reg rQN = cnt)
      (fun c => SCtx k y cb cf c ∧ c.reg rPP = pp + pe.2 + 2 ∧
        Strm q (out ++ enc (extPe k pe y cf)) c ∧ c.reg rQN = cnt + (extPe k pe y cf).length)
      (TPe k) := by
  have hlen : (out ++ enc (extPe k pe y cf)).length =
      out.length + (enc (emit2 k pe y)).length + (enc (emL pe cf (k - pe.2 - 1))).length := by
    rw [extPe_eq, enc_append]; simp only [List.length_append]; omega
  -- reading the record
  have h₁ : HGB S peHead (wregs peBody)
      (fun c => SCtx k y cb cf c ∧ c.reg rPP = pp ∧ Bel pp (pe.2 :: pe.1) c ∧ Strm q out c ∧
        c.reg rQN = cnt)
      (fun c => (PCtx k y cb cf pp pe c ∧ Strm q out c ∧ c.reg rQN = cnt) ∧
        (c.reg rW = 0 ↔ k ≤ pe.2)) 2 := by
    refine (HGB.runR (s := peHead) (by decide) (by decide) (by decide) (by decide) (by decide)
      fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rE, rW] c (RAM.run peHead c) := agree_run (by decide) rfl rfl (by decide) c
    obtain ⟨hC, hpp, hb, hS, hn⟩ := hc
    have hfr := hS.2.1
    have hbB := hb.2
    simp only [List.length_cons] at hbB
    refine ⟨by addr_ok [peHead, hpp], ?_⟩
    have hm : c.mem pp = pe.2 := hb.cons.1
    have he : (RAM.run peHead c).reg rE = pe.2 := by simp +decide [peHead, hpp, hm]
    refine ⟨⟨⟨SCtx.stable (W := [rE, rW]) (by decide) _ _ _ _ c _ hC
        (grow_of_agree hA (by decide) (by decide)), he, by rw [hA.reg _ (by decide), hpp],
        hb.mono hA.mem (by rw [hA.reg _ (by decide)])⟩, strm_agree hA (by decide) hS,
        by rw [hA.reg _ (by decide), hn]⟩, ?_⟩
    simp +decide [peHead, hpp, hm, hC.rk]
    omega
  -- the path through the slot
  have h₂ : HGB S (.ifz rW .skip em2) (wregs peBody)
      (fun c => (PCtx k y cb cf pp pe c ∧ Strm q out c ∧ c.reg rQN = cnt) ∧
        (c.reg rW = 0 ↔ k ≤ pe.2))
      (fun c => PCtx k y cb cf pp pe c ∧ Strm q (out ++ enc (emit2 k pe y)) c ∧
        c.reg rQN = cnt + (emit2 k pe y).length) (9 * k + 27) := by
    refine HGB.ifz ?_ ?_
    · refine HGB.of_pre (fun c h => h.1.2.mp h.2) fun hk => ?_
      refine (HGB.skip' (W := wregs peBody)).mono (by decide) (fun _ h => h) ?_ (by omega)
      rintro c ⟨⟨⟨hC, hS, hn⟩, -⟩, -⟩
      have h0 : emit2 k pe y = [] := by simp [emit2]; omega
      exact ⟨hC, by rw [h0]; simpa using hS, by rw [h0]; simpa using hn⟩
    · refine HGB.of_pre (fun c h => show ¬ k ≤ pe.2 from fun h' => h.2 (h.1.2.mpr h')) fun hk => ?_
      have h1 : emit2 k pe y = [(pe.1 ++ [y], pe.2 + 1)] := by simp [emit2]; omega
      have hem := HGB.frame (em2_spec (S := S) q out pe pp y cnt hpe
        (by rw [h1] at hlen; rw [List.length_append]; omega))
        (F := PCtx k y cb cf pp pe) (PCtx.stable (by decide) _ _ _ _ _ _)
      refine hem.mono (by decide) ?_ ?_ (by omega)
      · rintro c ⟨⟨⟨hC, hS, hn⟩, -⟩, -⟩
        exact ⟨⟨hS, hn, hC.2.1, hC.2.2.1, hC.1.ry, hC.2.2.2.cons.2⟩, hC⟩
      · rintro c ⟨⟨hS, hn⟩, hC⟩
        exact ⟨hC, by rw [h1]; exact hS, by rw [h1, hn]; rfl⟩
  -- the number of rounds
  have h₃ : HGB S peMid (wregs peBody)
      (fun c => PCtx k y cb cf pp pe c ∧ Strm q (out ++ enc (emit2 k pe y)) c ∧
        c.reg rQN = cnt + (emit2 k pe y).length)
      (fun c => LInv k y cb cf pp pe q (out ++ enc (emit2 k pe y)) (cnt + (emit2 k pe y).length)
        0 c ∧ c.reg rLN = k - pe.2 - 1) 3 := by
    refine (HGB.runM (s := peMid) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rT, rLN] c (RAM.run peMid c) := agree_run (by decide) rfl rfl (by decide) c
    obtain ⟨hC, hS, hn⟩ := hc
    refine ⟨⟨(PCtx.stable (W := [rT, rLN]) (by decide) _ _ _ _ _ _) c _ hC
        (grow_of_agree hA (by decide) (by decide)), by simpa [enc_nil] using strm_agree hA (by decide) hS,
        by rw [hA.reg _ (by decide), hn]; simp⟩, ?_⟩
    simp +decide [peMid, run_subc, hC.1.rk, hC.2.1]
  -- the rounds
  have h₄ := lLoop_spec (S := S) k y cb cf pp pe q (out ++ enc (emit2 k pe y))
    (cnt + (emit2 k pe y).length) hpe hpek hcf hcfl (by simp only [List.length_append]; omega)
  -- advancing
  have h₅ : HGB S peAdv (wregs peBody)
      (fun c => LInv k y cb cf pp pe q (out ++ enc (emit2 k pe y)) (cnt + (emit2 k pe y).length)
        (k - pe.2 - 1) c ∧ c.reg rL = k - pe.2 - 1 ∧ c.reg rLN = k - pe.2 - 1)
      (fun c => SCtx k y cb cf c ∧ c.reg rPP = pp + pe.2 + 2 ∧
        Strm q (out ++ enc (extPe k pe y cf)) c ∧ c.reg rQN = cnt + (extPe k pe y cf).length) 3 := by
    refine (HGB.runM (s := peAdv) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rT, rPP] c (RAM.run peAdv c) := agree_run (by decide) rfl rfl (by decide) c
    obtain ⟨⟨hC, hS, hn⟩, -, -⟩ := hc
    rw [extPe_eq, enc_append, ← List.append_assoc]
    refine ⟨SCtx.stable (W := [rT, rPP]) (by decide) _ _ _ _ c _ hC.1
        (grow_of_agree hA (by decide) (by decide)), ?_, strm_agree hA (by decide) hS,
      by rw [hA.reg _ (by decide), hn, List.length_append]; omega⟩
    simp +decide [peAdv, run_addc, hC.2.1, hC.2.2.1]
  refine (h₁.seq (h₂.seq (h₃.seq ((h₄.mono (by decide) (fun _ h => h) (fun _ h => h)
    le_rfl).seq h₅)))).weaken (by unfold TPe; omega)

/-! ### All partial paths -/

/-- The new records of the first `j` partial paths. -/
abbrev extJ (k : ℕ) (P : List (List ℕ × ℕ)) (y : ℕ) (cf : List (List ℕ × ℕ)) (j : ℕ) :
    List (List ℕ × ℕ) :=
  (P.take j).flatMap fun pe => extPe k pe y cf

@[simp] theorem extJ_zero (k : ℕ) (P : List (List ℕ × ℕ)) (y : ℕ) (cf : List (List ℕ × ℕ)) :
    extJ k P y cf 0 = [] := rfl

/-- The invariant of the loop over the partial paths `P` (records at `b`), after `j` of them. -/
def PeInv (k y cb : ℕ) (cf : List (List ℕ × ℕ)) (b : ℕ) (P : List (List ℕ × ℕ)) (q j : ℕ)
    (c : Config) : Prop :=
  SCtx k y cb cf c ∧ Bel b (enc P) c ∧ c.reg rPP = b + encOff P j ∧
    Strm q (enc (extJ k P y cf j)) c ∧ c.reg rQN = (extJ k P y cf j).length

theorem peLoop_spec {S : ℕ} (k y cb : ℕ) (cf : List (List ℕ × ℕ)) (b : ℕ)
    (P : List (List ℕ × ℕ)) (q : ℕ) (hP : ∀ pe ∈ P, pe.2 ≤ k ∧ pe.1.length = pe.2 + 1)
    (hPl : P.length ≤ Poly.partsBound k) (hcf : ∀ r ∈ cf, r.2 ≤ k ∧ r.1.length = r.2 + 1)
    (hcfl : cf.length ≤ Poly.partsBound k) (hSz : q + (enc (extJ k P y cf P.length)).length ≤ S) :
    HGB S peLoop (wregs peLoop) (fun c => PeInv k y cb cf b P q 0 c ∧ c.reg rPN = P.length)
      (fun c => PeInv k y cb cf b P q P.length c ∧ c.reg rPJ = P.length ∧ c.reg rPN = P.length)
      (TPL k) := by
  refine HGB.forUpCle (W := wregs peLoop) (i := rPJ) (n := rPN) (body := peBody)
    (PeInv k y cb cf b P q) (TPe k) _ hPl (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun j => by indep [PeInv, sCtx_iff, Strm, Bel]) fun j hj => ?_
  obtain ⟨hk, hl⟩ := hP P[j] (List.getElem_mem hj)
  have he : extJ k P y cf (j + 1) = extJ k P y cf j ++ extPe k P[j] y cf := by
    simp only [extJ, take_succ_eq hj, List.flatMap_append, List.flatMap_singleton]
  have hb := HGB.frame (peBody_spec (S := S) k y cb cf (b + encOff P j) P[j] q
    (enc (extJ k P y cf j)) (extJ k P y cf j).length hl hk hcf hcfl (by
      have : (enc (extJ k P y cf (j + 1))).length ≤ (enc (extJ k P y cf P.length)).length :=
        enc_flatMap_take_le P _ (show j + 1 ≤ P.length by omega)
      rw [← enc_append, ← he]; omega))
    (F := fun c => Bel b (enc P) c ∧ c.reg rPJ = j ∧ c.reg rPN = P.length) (by stab)
  refine hb.mono (by decide) ?_ ?_ le_rfl
  · rintro c ⟨⟨hC, hB, hpp, hS, hn⟩, hj', hN⟩
    exact ⟨⟨hC, hpp, hB.rec hj, hS, hn⟩, hB, hj', hN⟩
  · rintro c ⟨⟨hC, hpp, hS, hn⟩, hB, hj', hN⟩
    refine ⟨⟨hC, hB, ?_, ?_, ?_⟩, hj', hN⟩
    · rw [hpp, encOff_succ hj, hl]; omega
    · rw [he, enc_append]; exact hS
    · rw [hn, he, List.length_append]

end STACS2027.RAM.P2