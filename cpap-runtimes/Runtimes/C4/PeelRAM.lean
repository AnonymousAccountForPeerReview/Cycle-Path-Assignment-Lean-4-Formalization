module

public import Runtimes.C4.PeelProg
import Mathlib.Tactic

/-!
# Phase PEEL: the loops and the main triple

* `peelAlloc_spec`, `stepInit_spec` (the initialization loop, invariant
  `PRep g c₀ j (pinitPre (nb g) j)`, `j` nodes pushed);
* the relaxation loop of a removal (`forRange xJ xA xB relaxBody`, invariant: the fold of
  `relax` over the first `j - OFF[v]` neighbours) inside `removeV_spec`;
* one round `body_spec`: from a state `s` with an incomplete order, `peelBody` yields
  `pstep N (nb g) s` within `KP · acost s - 3` steps (cases: advance, stale pop, valid pop);
* the main loop `stepMain_spec`: a ghost-indexed `while` loop (`HTB.whileG`) over the
  iterates `S g k = (pstep N (nb g))^[k] (pinit N (nb g))` with the potential
  `PhiP g k = KP · pot (S g k)` (the abstract potential of `Peel.lean`, `pot_pstep`); when the
  test is zero the order is complete, so the state is `peelState g`
  (`iterate_eq_peelState`);
* **`peel_spec`**: from a `C4Base g` configuration, `peel` halts within `CP · (m + 1)` steps
  in a `PeelPost g` configuration (the positions `peelPos g` at `gPOS`), without output,
  storing only at or above the initial `rFREE`, and accessing only addresses below any
  `S ≥ peelEnd g F` (`F + 6N + 4 |E|`).

Space: the stack nodes are pushed at `rFREE`. The loops keep the budget
`rFREE + 2 · remSum ≤ peelEnd g F` (`remSum`: the degrees of the vertices not yet removed; a
removal of `v` relaxes `|nb v|` neighbours, each pushing at most one node), so that every push
has two cells below `S`.
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo STACS2027.RAM

section

variable {g : Graph} {c₀ : Config} {S : ℕ}

/-- `PMem` depends only on the fields `cur del ord stk` of the abstract state. -/
theorem PMem.congrS {k : ℕ} {s s' : PState} {fr : ℕ} {m : ℕ → ℕ} (h : PMem g c₀ k s fr m)
    (hc : s'.cur = s.cur) (hd : s'.del = s.del) (ho : s'.ord = s.ord) (hs : s'.stk = s.stk) :
    PMem g c₀ k s' fr m :=
  ⟨h.same, h.kle, hc ▸ h.cur, hd ▸ h.del, ho ▸ h.pos, hs ▸ h.bh, h.low, h.zero⟩

theorem PRep.congrS {k : ℕ} {s s' : PState} {c : Config} (h : PRep g c₀ k s c)
    (hc : s'.cur = s.cur) (hd : s'.del = s.del) (ho : s'.ord = s.ord) (hs : s'.stk = s.stk) :
    PRep g c₀ k s' c := ⟨h.glob, h.mem.congrS hc hd ho hs⟩

/-! ### The push budget -/

theorem remSum_congr {N : ℕ} {nb : ℕ → List ℕ} {s s' : PState} (h : s'.del = s.del) :
    remSum N nb s' = remSum N nb s := by
  unfold remSum; rw [h]

/-- Removing `v` takes its degree off the budget. -/
theorem remSum_of_del {N : ℕ} {nb : ℕ → List ℕ} {s s' : PState} {v : ℕ} (hv : v < N)
    (hd : s.del v = false) (h : s'.del = Function.update s.del v true) :
    remSum N nb s' + (nb v).length = remSum N nb s := by
  unfold remSum
  rw [h]
  have hset : ((Finset.range N).filter fun w => Function.update s.del v true w = false) =
      ((Finset.range N).filter fun w => s.del w = false).erase v := by
    ext w
    by_cases hw : w = v <;> simp [hw, Function.update_apply]
  rw [hset]
  exact Finset.sum_erase_add _ _ (by simp [hv, hd])

/-- The initial budget: all degrees. -/
theorem remSum_pinit (g : Graph) :
    remSum (numV g) (nb g) (pinit (numV g) (nb g)) = 2 * (idEdges g).length := by
  obtain ⟨h1, -⟩ := pinitPre_fields (nb g) (numV g)
  rw [pinit_eq]
  unfold remSum
  rw [h1, ← sum_length_nb]
  congr 1
  exact Finset.filter_true_of_mem fun _ _ => rfl

/-! ### Step 1: allocation -/

theorem peelAlloc_spec (hB : C4Base g c₀) :
    HTB S peelAlloc (fun c => c = c₀)
      (fun c => (PRep g c₀ 0 (pinitPre (nb g) 0) c ∧ c.reg rFREE = bNODE g (c₀.reg rFREE)) ∧
        c.reg gN = numV g) 12 := by
  refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => ?_
  subst hc
  have hL := peel_layout g (c.reg rFREE)
  have hZ := hB.r1.base.free
  have hn := hB.r1.base.n
  have hpos := hB.free_pos
  simp only [peelAlloc, run_seq', run_alloc (show gN ≠ rT by decide) (show gCUR ≠ gN by decide),
    run_alloc (show gN ≠ rT by decide) (show gDEL ≠ gN by decide),
    run_alloc (show gN ≠ rT by decide) (show gBH ≠ gN by decide),
    run_alloc (show gN ≠ rT by decide) (show gPOS ≠ gN by decide)]
  refine ⟨⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  all_goals try (simp +decide [hn, hB.r1.base.one, hL]; done)
  all_goals try (simp +decide [hn, hL]; omega)
  simp only [setReg_mem]
  refine PMem.ofEq (fr := bNODE g (c.reg rFREE)) ⟨SameOn.refl _ _, Nat.zero_le _, tab_zero _ _ _,
    ?_, ?_, ?_, le_rfl, hZ.mono (by omega)⟩ ?_
  · refine (hZ.tab (b := bDEL g (c.reg rFREE)) (by omega) (numV g)).congr_fun fun i _ => ?_
    simp [pinitPre_zero]
  · intro v _ hv; simp [pinitPre_zero] at hv
  · intro d hd
    simp only [pinitPre_zero, LL_nil]
    exact hZ.get (by omega)
  · simp +decide [hn, hL]; omega

/-! ### Step 2: the initial buckets -/

/-- The invariant of the initialization: `j` vertices pushed. -/
def PIInv (g : Graph) (c₀ : Config) (j : ℕ) (c : Config) : Prop :=
  PRep g c₀ j (pinitPre (nb g) j) c ∧ c.reg rFREE = bNODE g (c₀.reg rFREE) + 2 * j

theorem stepInit_spec (hB : C4Base g c₀) (hS : peelEnd g (c₀.reg rFREE) ≤ S) :
    HTB S stepInit (fun c => PIInv g c₀ 0 c ∧ c.reg gN = numV g)
      (fun c => PIInv g c₀ (numV g) c ∧ c.reg xI = numV g ∧ c.reg gN = numV g)
      (numV g * (21 + 4) + 3) :=
  HTB.forUpC (i := xI) (n := gN) (N := numV g) (body := initBody) (PIInv g c₀) 21 (by decide)
    (by decide) (by decide)
    (fun j => ((PRep.indep g c₀ j _).mono (by decide)).and
      (Indep.reg (r := rFREE) (by decide) (· = bNODE g (c₀.reg rFREE) + 2 * j)))
    (fun j hj => HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hfr⟩, hi, _⟩ => by
      have hF := peel_fits g (c₀.reg rFREE) hS
      obtain ⟨hR', hI', hN', hfr', hA⟩ := initBody_run hB hR hi hj hS (by rw [hfr]; omega)
      exact ⟨hA, ⟨hR', by rw [hfr', hfr]; ring⟩, hI', hN'⟩)

/-! ### The relaxation loop of a removal -/

theorem getElem_not_mem_take {l : List ℕ} (hl : l.Nodup) {i : ℕ} (hi : i < l.length) :
    l[i] ∉ l.take i := by
  rw [List.mem_take_iff_getElem]
  rintro ⟨j, hj, e⟩
  have := (hl.getElem_inj_iff (hi := by omega) (hj := hi)).mp e
  omega

/-- The removal of a valid top `v` of the current bucket. -/
theorem removeV_spec (hB : C4Base g c₀) (hSp : peelEnd g (c₀.reg rFREE) ≤ S) {s : PState}
    (hI : PInv (numV g) (nb g) s) {v : ℕ}
    {rest : List ℕ} (he : s.stk s.p = v :: rest) (hd : s.del v = false) :
    HTB S removeV (fun c => PRep g c₀ (numV g) { s with stk := Function.update s.stk s.p rest } c ∧
        c.reg xV = v ∧ c.reg xS = s.ord.length ∧ c.reg xP = s.p ∧
        c.reg rFREE + 2 * remSum (numV g) (nb g) s ≤ peelEnd g (c₀.reg rFREE))
      (fun c => PRep g c₀ (numV g)
          (remove (nb g) { s with stk := Function.update s.stk s.p rest } v) c ∧
        c.reg xS = s.ord.length + 1 ∧ c.reg xP = s.p - 1 ∧
        c.reg rFREE + 2 * remSum (numV g) (nb g)
          (remove (nb g) { s with stk := Function.update s.stk s.p rest } v) ≤
          peelEnd g (c₀.reg rFREE))
      (12 + ((nb g v).length * 26 + 4 + 2)) := by
  have hvN : v < numV g := hI.stk_lt _ v (by rw [he]; exact List.mem_cons_self ..)
  have hvo : v ∉ s.ord := (hI.del_eq_false_iff v).mp hd
  set s₁ : PState := { s with stk := Function.update s.stk s.p rest } with hs₁
  set s₂ : PState := { s₁ with del := Function.update s₁.del v true, ord := s₁.ord ++ [v] }
    with hs₂
  set A := R1.ps (idEdges g) v with hA
  set E := peelEnd g (c₀.reg rFREE) with hE
  have hAB : R1.ps (idEdges g) (v + 1) = A + (nb g v).length := by rw [R1.ps_succ]
  have hrem : remSum (numV g) (nb g) s₂ + (nb g v).length = remSum (numV g) (nb g) s :=
    remSum_of_del hvN hd rfl
  let Inv : ℕ → Config → Prop := fun j c =>
    PRep g c₀ (numV g) (((nb g v).take (j - A)).foldl relax s₂) c ∧
      c.reg xS = s.ord.length + 1 ∧ c.reg xP = s.p ∧
      c.reg rFREE + 2 * ((A + (nb g v).length - j) + remSum (numV g) (nb g) s₂) ≤ E
  -- step 1: removeHead
  have h₁ : HTB S removeHead (fun c => PRep g c₀ (numV g) s₁ c ∧ c.reg xV = v ∧
        c.reg xS = s.ord.length ∧ c.reg xP = s.p ∧
        c.reg rFREE + 2 * remSum (numV g) (nb g) s ≤ E)
      (fun c => Inv A c ∧ c.reg xA = A ∧ c.reg xB = A + (nb g v).length ∧
        A ≤ A + (nb g v).length) 12 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hR, hV, hS, hP, hbud⟩ => ?_
    obtain ⟨hR', hS', hA', hB', hreg, hAd⟩ := removeHead_run hB hR hvN hvo hV hS hSp
    refine ⟨hAd, ⟨by simpa using hR', hS', ?_, ?_⟩, hA', by rw [hB', hAB], by omega⟩
    · rw [hreg _ (by decide) (by decide) (by decide) (by decide) (by decide), hP]
    · rw [hreg _ (by decide) (by decide) (by decide) (by decide) (by decide)]
      omega
  -- step 2: the relaxation loop
  have h₂ := HTB.forRange (S := S) (i := xJ) (a := xA) (n := xB) (A := A)
    (N := A + (nb g v).length) (body := relaxBody) Inv (fun _ => 22) (by decide) (by decide)
    (by decide) (by decide)
    (fun j => ((PRep.indep g c₀ (numV g) _).mono (by decide)).and
      ((Indep.reg (r := xS) (by decide) (· = s.ord.length + 1)).and
        ((Indep.reg (r := xP) (by decide) (· = s.p)).and
          (Indep.reg (r := rFREE) (by decide)
            (fun x => x + 2 * ((A + (nb g v).length - j) + remSum (numV g) (nb g) s₂) ≤ E)))))
    (fun j hAj hjN => by
      refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hS, hP, hbud⟩, hJ, hBn⟩ => ?_
      have hi : j - A < (nb g v).length := by omega
      have hw : (nb g v).getD (j - A) 0 = (nb g v)[j - A] := getD_eq_getElem' hi
      have hcw : (((nb g v).take (j - A)).foldl relax s₂).del ((nb g v).getD (j - A) 0) = false →
          (((nb g v).take (j - A)).foldl relax s₂).cur ((nb g v).getD (j - A) 0) < numV g := by
        intro hdw
        have hnot := getElem_not_mem_take (nodup_nb g v) hi
        rw [← hw] at hnot
        have hwN : (nb g v).getD (j - A) 0 < numV g :=
          (nbOk g).lt v _ (by rw [hw]; exact List.getElem_mem _)
        rw [foldl_relax_del] at hdw
        rw [foldl_relax_cur ((nodup_nb g v).sublist (List.take_sublist _ _))]
        simp only [hnot, false_and, ↓reduceIte]
        have hdw' : s.del ((nb g v).getD (j - A) 0) = false := by
          by_cases hwv : (nb g v).getD (j - A) 0 = v
          · rw [hwv] at hdw; simp [hs₂] at hdw
          · have e : s₂.del ((nb g v).getD (j - A) 0) = s.del ((nb g v).getD (j - A) 0) :=
              Function.update_of_ne hwv _ _
            rwa [e] at hdw
        exact hI.cur_lt (nbOk g) hwN hdw'
      have hSS : E ≤ S := hSp
      obtain ⟨hR', hreg, hfr, hAd⟩ := relaxBody_run hB hR hvN hi (by rw [hJ]; omega) hcw hSp
        (by omega)
      have hfold : ((nb g v).take (j + 1 - A)).foldl relax s₂ =
          relax (((nb g v).take (j - A)).foldl relax s₂) ((nb g v).getD (j - A) 0) := by
        rw [show j + 1 - A = (j - A) + 1 by omega, List.take_succ_eq_append_getElem hi,
          List.foldl_append, hw]
        rfl
      refine ⟨hAd, ⟨⟨by rw [hfold]; exact hR', ?_, ?_, by omega⟩, ?_, ?_⟩⟩
      · rw [hreg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hS]
      · rw [hreg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hP]
      · rw [hreg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hJ]
      · rw [hreg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hBn])
  -- step 3: the pointer
  have h₃ : HTB S (dec xP) (fun c => Inv (A + (nb g v).length) c ∧
        c.reg xJ = A + (nb g v).length ∧ c.reg xB = A + (nb g v).length)
      (fun c => PRep g c₀ (numV g) (remove (nb g) s₁ v) c ∧
        c.reg xS = s.ord.length + 1 ∧ c.reg xP = s.p - 1 ∧
        c.reg rFREE + 2 * remSum (numV g) (nb g) (remove (nb g) s₁ v) ≤ E) 2 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hR, hS, hP, hbud⟩, _, _⟩ => ?_
    rw [run_dec (by decide)]
    have hfull : (nb g v).take (A + (nb g v).length - A) = nb g v := by
      rw [show A + (nb g v).length - A = (nb g v).length by omega, List.take_length]
    rw [hfull] at hR
    have hrs : remSum (numV g) (nb g) (remove (nb g) s₁ v) = remSum (numV g) (nb g) s₂ :=
      remSum_congr (by rw [remove_del])
    refine ⟨?_, by simp +decide [hS], by simp +decide [hP], ?_⟩
    · refine ((PRep.indep g c₀ (numV g) _).setReg (d := xP) (by decide) _
        ((PRep.indep g c₀ (numV g) _).setReg (d := rT) (by decide) _ hR)).congrS rfl rfl rfl rfl
    · simp +decide only [setReg_reg, ↓reduceIte]
      rw [hrs]
      omega
  refine (h₁.seq (h₂.seq h₃)).weaken (le_of_eq ?_)
  simp [Finset.sum_const, Nat.card_Ico]

/-! ### One round of the main loop -/

/-- The state of the main loop: the representation, `xS = |ord|`, `xP = p`, and the budget. -/
def MRep (g : Graph) (c₀ : Config) (s : PState) (c : Config) : Prop :=
  PRep g c₀ (numV g) s c ∧ c.reg xS = s.ord.length ∧ c.reg xP = s.p ∧
    c.reg rFREE + 2 * remSum (numV g) (nb g) s ≤ peelEnd g (c₀.reg rFREE)

theorem MRep.indep (g : Graph) (c₀ : Config) (s : PState) :
    Indep [rT, xI, xJ, xA, xB, xV, xW, xX, xY, xH, xQ, xD] (MRep g c₀ s) :=
  ((PRep.indep g c₀ (numV g) s).mono (by decide)).and
    ((Indep.reg (r := xS) (by decide) (· = s.ord.length)).and
      ((Indep.reg (r := xP) (by decide) (· = s.p)).and
        (Indep.reg (r := rFREE) (by decide)
          (fun x => x + 2 * remSum (numV g) (nb g) s ≤ peelEnd g (c₀.reg rFREE)))))

/-- The constant of the potential of the main loop. -/
def KP : ℕ := 64


/-- The state after the pop of `v` (the rest `rest` of the bucket). -/
def PopRep (g : Graph) (c₀ : Config) (s : PState) (v : ℕ) (rest : List ℕ) (c : Config) : Prop :=
  PRep g c₀ (numV g) { s with stk := Function.update s.stk s.p rest } c ∧
    c.reg xV = v ∧ c.reg xX = (if s.del v then 1 else 0) ∧ c.reg xY = s.cur v ∧
    c.reg xS = s.ord.length ∧ c.reg xP = s.p ∧
    c.reg rFREE + 2 * remSum (numV g) (nb g) s ≤ peelEnd g (c₀.reg rFREE)

theorem PopRep.indep (g : Graph) (c₀ : Config) (s : PState) (v : ℕ) (rest : List ℕ) :
    Indep [rT] (fun c => PopRep g c₀ s v rest c ∧ c.reg xX = 0) := by
  refine (((PRep.indep g c₀ (numV g) _).mono (by decide)).and ?_).and
    (Indep.reg (r := xX) (by decide) (· = 0))
  exact (Indep.reg (r := xV) (by decide) (· = v)).and
    ((Indep.reg (r := xX) (by decide) (· = if s.del v then 1 else 0)).and
    ((Indep.reg (r := xY) (by decide) (· = s.cur v)).and
      ((Indep.reg (r := xS) (by decide) (· = s.ord.length)).and
        ((Indep.reg (r := xP) (by decide) (· = s.p)).and
          (Indep.reg (r := rFREE) (by decide)
            (fun x => x + 2 * remSum (numV g) (nb g) s ≤ peelEnd g (c₀.reg rFREE)))))))

/-- **One round**: from a state with an incomplete order, `peelBody` computes `pstep`. -/
theorem body_spec (hB : C4Base g c₀) (hSp : peelEnd g (c₀.reg rFREE) ≤ S) {s : PState}
    (hI : PInv (numV g) (nb g) s) (hlt : s.ord.length < numV g) :
    HTB S peelBody (MRep g c₀ s) (MRep g c₀ (pstep (numV g) (nb g) s))
      (KP * acost (nb g) s - 3) := by
  have hpN := hI.p_lt (nbOk g) hlt
  have hL := peel_layout g (c₀.reg rFREE)
  have hF := peel_fits g (c₀.reg rFREE) hSp
  have hpos := hB.free_pos
  -- reading the head of the current bucket
  have hhead : HTB S (ld xH gBH xP) (MRep g c₀ s)
      (fun c => MRep g c₀ s c ∧ c.reg xH = c.mem (bBH g (c₀.reg rFREE) + s.p)) 2 := by
    refine HTB.run_le (by decide) (by decide) fun c hc => ?_
    refine ⟨by addr_ok [hc.1.glob.bh, hc.2.2.1], ?_⟩
    rw [run_ld]
    exact ⟨(MRep.indep g c₀ s).setReg (by decide) _ hc, by
      simp +decide [hc.1.glob.bh, hc.2.2.1]⟩
  rcases he : s.stk s.p with _ | ⟨v, rest⟩
  · -- advance
    rw [pstep_advance hlt he]
    have hac : acost (nb g) s = 1 := by simp [acost, he]
    rw [hac]
    refine (hhead.seq (HTB.ifz (HTB.of_HT rfl <| HT.run_le (s := inc xP) (b := 2) (by decide)
      (by decide) fun c ⟨⟨⟨hR, hS, hP, hbud⟩, _⟩, _⟩ => ?_)
      (HTB.of_false fun c ⟨⟨hR, hH⟩, h0⟩ => ?_))).weaken (by simp [KP])
    · rw [run_inc (by decide)]
      refine ⟨?_, by simp +decide [hS], by simp +decide [hP], by simpa +decide [remSum] using hbud⟩
      exact ((PRep.indep g c₀ (numV g) s).setReg (d := xP) (by decide) _
        ((PRep.indep g c₀ (numV g) s).setReg (d := rT) (by decide) _ hR)).congrS rfl rfl rfl rfl
    · have hLL := hR.1.mem.bh s.p hpN
      rw [he] at hLL
      exact h0 (by rw [hH]; exact hLL)
  · have hvN : v < numV g := hI.stk_lt _ v (by rw [he]; exact List.mem_cons_self ..)
    -- the head is a node
    have hne : ∀ c, MRep g c₀ s c → c.mem (bBH g (c₀.reg rFREE) + s.p) ≠ 0 := by
      intro c hc
      have hLL := hc.1.mem.bh s.p hpN
      rw [he] at hLL
      exact hLL.ne_zero (by rw [hL.2.2.2]; omega)
    -- the pop
    have hpop : HTB S popRead (fun c => (MRep g c₀ s c ∧
          c.reg xH = c.mem (bBH g (c₀.reg rFREE) + s.p)) ∧ c.reg xH ≠ 0)
        (PopRep g c₀ s v rest) 10 := by
      refine HTB.run_le (by decide) (by decide) fun c ⟨⟨⟨hR, hS, hP, hbud⟩, hH⟩, _⟩ => ?_
      obtain ⟨hR', hV, hX, hY, hreg, hAd⟩ := popRead_run hR hpN hvN hP he hH hSp (by omega)
      refine ⟨hAd, hR', hV, hX, hY, ?_, ?_, ?_⟩
      · rw [hreg _ (by decide) (by decide) (by decide) (by decide) (by decide), hS]
      · rw [hreg _ (by decide) (by decide) (by decide) (by decide) (by decide), hP]
      · rw [hreg _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hbud
    have hfalse : ∀ {Q : Config → Prop} {b : ℕ}, HTB S (inc xP) (fun c => (MRep g c₀ s c ∧
        c.reg xH = c.mem (bBH g (c₀.reg rFREE) + s.p)) ∧ c.reg xH = 0) Q b :=
      HTB.of_false fun c ⟨⟨hc, hH⟩, h0⟩ => hne c hc (hH ▸ h0)
    by_cases hv : s.del v = false ∧ s.cur v = s.p
    · -- valid pop: removal
      rw [pstep_valid hlt he hv.1 hv.2]
      have hac : acost (nb g) s = (nb g v).length + 1 := by simp [acost, he, hv]
      rw [hac]
      have hrem : HTB S removeV (fun c => (PopRep g c₀ s v rest c ∧ c.reg xX = 0) ∧
            c.reg xY = c.reg xP)
          (MRep g c₀ (remove (nb g) { s with stk := Function.update s.stk s.p rest } v))
          (12 + ((nb g v).length * 26 + 4 + 2)) :=
        (removeV_spec hB hSp hI he hv.1).mono (fun c ⟨⟨⟨hR, hV, _, _, hS, hP, hbud⟩, _⟩, _⟩ =>
          ⟨hR, hV, hS, hP, hbud⟩) (fun c ⟨hR, hS, hP, hbud⟩ => ⟨hR, by rw [hS, remove_ord]; simp,
            by rw [hP, remove_p], hbud⟩) le_rfl
      have hifEq := HTB.ifEq (s := removeV) (u := .skip) (ha := show xY ≠ rT by decide)
        (hb := show xP ≠ rT by decide) (PopRep.indep g c₀ s v rest) hrem
        (HTB.of_false fun c ⟨⟨⟨_, _, _, hY, _, hP, _⟩, _⟩, hne'⟩ => hne' (by rw [hY, hP, hv.2]))
      refine (hhead.seq (HTB.ifz hfalse (hpop.seq (HTB.ifz hifEq
        (HTB.of_false fun c ⟨⟨_, _, hX, _⟩, h0⟩ => h0 (by rw [hX, hv.1]; rfl)))))).weaken ?_
      simp only [KP]
      omega
    · -- stale pop
      rw [pstep_stale hlt he hv]
      have hac : acost (nb g) s = 1 := by simp [acost, he, hv]
      rw [hac]
      have hskip : ∀ {P : Config → Prop}, (∀ c, P c → PopRep g c₀ s v rest c) →
          HTB S RAM.Stmt.skip P (MRep g c₀ { s with stk := Function.update s.stk s.p rest }) 1 :=
        fun hP => HTB.of_HT rfl <| HT.run_le trivial le_rfl fun c hc => by
          obtain ⟨hR, _, _, _, hS, hP', hbud⟩ := hP c hc
          exact ⟨hR, hS, hP', by simpa [remSum] using hbud⟩
      by_cases hd : s.del v = false
      · -- current degree differs: the `ifEq` skips
        have hc : s.cur v ≠ s.p := fun h => hv ⟨hd, h⟩
        have hifEq := HTB.ifEq (s := removeV) (u := .skip) (ha := show xY ≠ rT by decide)
          (hb := show xP ≠ rT by decide) (PopRep.indep g c₀ s v rest)
          (HTB.of_false fun c ⟨⟨⟨_, _, _, hY, _, hP, _⟩, _⟩, he'⟩ =>
            hc (by rw [← hY, ← hP]; exact he'))
          (hskip fun c ⟨⟨h, _⟩, _⟩ => h)
        refine (hhead.seq (HTB.ifz hfalse (hpop.seq (HTB.ifz hifEq
          (HTB.of_false fun c ⟨⟨_, _, hX, _⟩, h0⟩ => h0 (by rw [hX, hd]; rfl)))))).weaken ?_
        simp only [KP]
        omega
      · -- removed: skip
        have hd' : s.del v = true := by simpa using hd
        refine (hhead.seq (HTB.ifz hfalse (hpop.seq (HTB.ifz
          (HTB.of_false fun c ⟨⟨_, _, hX, _⟩, h0⟩ => by rw [hX, hd'] at h0; simp at h0)
          ((hskip fun c h => h.1).weaken (show 1 ≤ 5 by omega)))))).weaken ?_
        simp only [KP]
        omega

/-! ### The main loop -/

/-- The `k`-th iterate of the peeling step from the initial state. -/
abbrev peelIt (g : Graph) (k : ℕ) : PState := (pstep (numV g) (nb g))^[k] (pinit (numV g) (nb g))

/-- The invariant of the main loop (after each evaluation of the test). -/
def MInv (g : Graph) (c₀ : Config) (k : ℕ) (c : Config) : Prop :=
  MRep g c₀ (peelIt g k) c ∧ c.reg rT = numV g - (peelIt g k).ord.length

/-- The potential of the main loop. -/
def PhiP (g : Graph) (k : ℕ) : ℕ := KP * pot (numV g) (nb g) (peelIt g k)

theorem cond_spec (s : PState) :
    HTB S peelCond (MRep g c₀ s) (fun c => MRep g c₀ s c ∧ c.reg rT = numV g - s.ord.length) 1 :=
  HTB.run_le trivial le_rfl fun c hc =>
    ⟨trivial, (MRep.indep g c₀ s).setReg (by decide) _ hc,
      by simp +decide [peelCond, hc.1.glob.n, hc.2.1]⟩

/-- **One round of the main loop**, with the potential. -/
theorem round_spec (hB : C4Base g c₀) (hSp : peelEnd g (c₀.reg rFREE) ≤ S) (k : ℕ) :
    HTBt S (.seq peelBody peelCond) (fun c => MInv g c₀ k c ∧ c.reg rT ≠ 0)
      (fun c' t => ∃ y, MInv g c₀ y c' ∧ PhiP g y + t + 1 ≤ PhiP g k) := by
  have hI : PInv (numV g) (nb g) (peelIt g k) := pinv_iterate (nbOk g) k
  by_cases hlt : (peelIt g k).ord.length < numV g
  · have hpot : pot (numV g) (nb g) (pstep (numV g) (nb g) (peelIt g k)) +
        acost (nb g) (peelIt g k) ≤ pot (numV g) (nb g) (peelIt g k) := pot_pstep (nbOk g) hI hlt
    have hac : 1 ≤ acost (nb g) (peelIt g k) := by
      unfold acost
      split
      · exact le_rfl
      · split_ifs <;> omega
    have hS1 : peelIt g (k + 1) = pstep (numV g) (nb g) (peelIt g k) :=
      Function.iterate_succ_apply' _ _ _
    have h := ((body_spec hB hSp hI hlt).pre fun c (h : MInv g c₀ k c ∧ c.reg rT ≠ 0) => h.1.1).seq
      (cond_spec (S := S) (c₀ := c₀) (pstep (numV g) (nb g) (peelIt g k)))
    refine HTB.toG (Inv := MInv g c₀) (Φ := PhiP g) (y := k + 1)
      (h.post fun c hc => by rw [MInv, hS1]; exact hc) ?_
    have e1 : PhiP g (k + 1) = 64 * pot (numV g) (nb g) (pstep (numV g) (nb g) (peelIt g k)) := by
      rw [PhiP, hS1]; rfl
    have e2 : PhiP g k = 64 * pot (numV g) (nb g) (peelIt g k) := rfl
    rw [e1, e2, show KP = 64 from rfl]
    omega
  · intro c ⟨⟨_, hT⟩, hne⟩
    exact absurd (by rw [hT]; omega) hne

/-- **Step 3: the peeling loop.** -/
theorem stepMain_spec (hB : C4Base g c₀) (hSp : peelEnd g (c₀.reg rFREE) ≤ S) :
    HTB S stepMain (fun c => PIInv g c₀ (numV g) c ∧ c.reg gN = numV g)
      (fun c => PRep g c₀ (numV g) (peelState g) c ∧ c.reg rFREE ≤ peelEnd g (c₀.reg rFREE))
      (1 + (1 + (1 + (PhiP g 0 + 1)))) := by
  obtain ⟨-, -, hp0, ho0, -⟩ := pinitPre_fields (nb g) (numV g)
  have hbud0 : bNODE g (c₀.reg rFREE) + 2 * numV g +
      2 * remSum (numV g) (nb g) (peelIt g 0) ≤ peelEnd g (c₀.reg rFREE) := by
    simp only [peelIt, Function.iterate_zero, id, remSum_pinit, bNODE, peelEnd]
    omega
  have h₀ : HTB S (.const xS 0) (fun c => PIInv g c₀ (numV g) c ∧ c.reg gN = numV g)
      (fun c => PIInv g c₀ (numV g) c ∧ c.reg xS = 0) 1 :=
    HTB.of_HT rfl <| HT.run_le trivial le_rfl fun c ⟨⟨hR, hfr⟩, _⟩ =>
      ⟨⟨(PRep.indep g c₀ (numV g) _).setReg (d := xS) (by decide) _ hR, by simpa using hfr⟩,
        by simp⟩
  have h₁ : HTB S (.const xP 0) (fun c => PIInv g c₀ (numV g) c ∧ c.reg xS = 0)
      (MRep g c₀ (peelIt g 0)) 1 :=
    HTB.of_HT rfl <| HT.run_le trivial le_rfl fun c ⟨⟨hR, hfr⟩, hS⟩ =>
      ⟨(PRep.indep g c₀ (numV g) _).setReg (d := xP) (by decide) _ hR,
        by simp +decide [hS, peelIt, pinit_eq, ho0], by simp +decide [peelIt, pinit_eq, hp0],
        by
          have e : (run (.const xP 0) c).reg rFREE = c.reg rFREE := by simp +decide
          rw [e, hfr]; exact hbud0⟩
  have hl := HTB.whileG (MInv g c₀) (PhiP g) 0 (cond_spec (S := S) (c₀ := c₀) (peelIt g 0))
    (round_spec hB hSp)
  refine h₀.seq (h₁.seq (hl.post fun c ⟨y, ⟨hR, hT⟩, h0⟩ => ?_))
  have hle : (peelIt g y).ord.length ≤ numV g := (pinv_iterate (nbOk g) y).length_ord_le
  have heq := iterate_eq_peelState g (k := y) (show (peelIt g y).ord.length = numV g by omega)
  rw [← heq]
  exact ⟨hR.1, by have := hR.2.2.2; omega⟩

/-- The constant of the running time of PEEL. -/
def CP : ℕ := 2000

theorem peel_wregs : ∀ r ∈ wregs peel, r = rT ∨ r = rFREE ∨ (30 ≤ r ∧ r < 50) ∨
    (100 ≤ r ∧ r < 150) := by decide

theorem peel_writes : writes peel = false := by decide

/-- **Phase PEEL**: from a `C4Base g` configuration `c₀`, the program `peel` computes the
positions `peelPos g` of the peeling order (at `gPOS`), within `CP · (m + 1)` steps, without
output, storing only at or above the initial `rFREE`, accessing only the addresses below any
`S ≥ peelEnd g F` (`F = c₀.reg rFREE`), and ending with `rFREE ≤ peelEnd g F`. -/
theorem peel_spec (g : Graph) (c₀ : Config) (hSp : peelEnd g (c₀.reg rFREE) ≤ S) :
    HTB S peel (fun c => C4Base g c ∧ c = c₀)
      (fun c => PeelPost g c ∧ c.out = c₀.out ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        c₀.reg rFREE ≤ c.reg rFREE ∧ c.reg rFREE ≤ peelEnd g (c₀.reg rFREE))
      (CP * (g.length + 1)) := by
  intro c ⟨hB, hc⟩
  subst hc
  have h := (peelAlloc_spec (S := S) hB).seq ((stepInit_spec hB hSp).seq
    ((stepMain_spec hB hSp).pre fun c' ⟨hR, _, hn⟩ => ⟨hR, hn⟩))
  obtain ⟨c', t, he, ⟨⟨hR, hfin⟩, hfr⟩, ht⟩ := h.withFrame c c ⟨rfl, rfl⟩
  have hL := peel_layout g (c.reg rFREE)
  have hlow := hR.mem.low
  have hreg : ∀ r, r < 30 → r ≠ rT → r ≠ rFREE → c'.reg r = c.reg r := fun r hr h1 h2 =>
    hfr.reg r fun hm => by rcases peel_wregs r hm with h | h | h | h <;> omega
  refine ⟨c', t, he, ⟨⟨hB.transfer hreg hR.mem.same (by omega) hR.mem.zero, ?_, ?_⟩,
    hfr.out peel_writes, hR.mem.same, by omega, hfin⟩, ?_⟩
  · rw [hR.glob.pos]
    intro v hv
    exact hR.mem.pos v hv (mem_peelOrd.mpr hv)
  · rw [hR.glob.pos]; omega
  · have hpot := pot_pinit_graph g
    have h1 := numV_le g
    have h2 := length_idEdges_le g
    simp only [PhiP, KP, peelIt, Function.iterate_zero, id, peelFuel] at ht hpot
    simp only [CP]
    omega

end

end STACS2027.Runtimes.C4
