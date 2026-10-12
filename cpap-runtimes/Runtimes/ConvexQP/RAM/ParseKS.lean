module

public import Runtimes.ConvexQP.RAM.QPIface
import Mathlib.Tactic

/-!
# Lemma 16 on the RAM, the constants: register states and steps

The constants of `QRegs` are computed by straight-line code with `mulN` and two counted loops.
The state `KS m₀ F B rs v` fixes the memory `m₀`, `rFREE = F`, `qBH = B`, an empty output, and
the values `v r` of the registers `r ∈ rs` (a register may appear several times in `rs`; `v` is a
function, so the facts agree). Each step lemma (`KS.add`, `KS.addc`, `KS.subc`, `KS.mov`,
`KS.const`, `KS.mulN`, `KS.clog`) turns `KS rs v` into `KS (d :: rs) (update v d z)` for its
destination `d` and value `z`; side conditions on concrete registers are decided.

`clogLoop dst src w` computes `Nat.clog 2 (reg src)` by doubling `w` (`KS.clog`).

**Space.** The only memory accesses are those of the multiplications (`Arith.mulN`): the scratch
table of `2 · size y ≤ mulCost y` cells above the free address `F`. So the steps are stated as
`HTF S F` triples (`HTF S F s P Q b := F + b ≤ S → HTB S s P Q b`: the space allowance above `F`
is the step bound), which compose like `HTB` triples (`HTF.seq`, `HTF.mono`, `HTF.forUpC`);
memory-free steps lift by `HTF.of_HT`, the multiplication is `KS.mulN`.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Parse

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ConvexQP

/-! ### Triples with the space allowance of their step bound -/

/-- A bounded triple whose space allowance above the free address `F` is its step bound. -/
def HTF (S F : ℕ) (s : Stmt) (P Q : Config → Prop) (b : ℕ) : Prop := F + b ≤ S → HTB S s P Q b

namespace HTF

variable {S F : ℕ} {s u : Stmt} {P P' Q Q' R : Config → Prop} {b b' : ℕ}

/-- Memory-free code. -/
theorem of_HT (hm : memFree s = true) (h : HT s P Q b) : HTF S F s P Q b := fun _ => HTB.of_HT hm h

theorem mono (h : HTF S F s P Q b) (hP : ∀ c, P' c → P c) (hQ : ∀ c, Q c → Q' c) (hb : b ≤ b') :
    HTF S F s P' Q' b' := fun hS => (h (by omega)).mono hP hQ hb

theorem seq (h₁ : HTF S F s P R b) (h₂ : HTF S F u R Q b') : HTF S F (.seq s u) P Q (b + b') :=
  fun hS => (h₁ (by omega)).seq (h₂ (by omega))

theorem frameReg {Fr : Config → Prop} (h : HTF S F s P Q b) (hF : RegIndep (wregs s) Fr) :
    HTF S F s (fun c => P c ∧ Fr c) (fun c => Q c ∧ Fr c) b := fun hS => (h hS).frameReg hF

/-- Counted loop with a constant bound per iteration. -/
theorem forUpC {i n N : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop) (T : ℕ)
    (hi : i ≠ rT) (hn : n ≠ rT) (hin : n ≠ i) (hInv : ∀ j, Indep [i, rT] (Inv j))
    (hbody : ∀ j, j < N → HTF S F body (fun c => Inv j c ∧ c.reg i = j ∧ c.reg n = N)
      (fun c => Inv (j + 1) c ∧ c.reg i = j ∧ c.reg n = N) T) :
    HTF S F (RAM.forUp i n body) (fun c => Inv 0 c ∧ c.reg n = N)
      (fun c => Inv N c ∧ c.reg i = N ∧ c.reg n = N) (N * (T + 4) + 3) := fun hS =>
  HTB.forUpC Inv T hi hn hin hInv fun j hj => hbody j hj (by
    have : T ≤ N * (T + 4) := by
      calc T ≤ 1 * (T + 4) := by omega
        _ ≤ N * (T + 4) := Nat.mul_le_mul_right _ (by omega)
    omega)

end HTF

/-- The state of the constants phase: frame and register values. -/
def KS (m₀ : ℕ → ℕ) (F B : ℕ) (rs : List ℕ) (v : ℕ → ℕ) (c : Config) : Prop :=
  c.mem = m₀ ∧ c.reg rFREE = F ∧ c.reg qBH = B ∧ c.out = [] ∧ ∀ r ∈ rs, c.reg r = v r

section KS

variable {m₀ : ℕ → ℕ} {F B : ℕ} {rs : List ℕ} {v : ℕ → ℕ}

theorem KS.get {c : Config} (h : KS m₀ F B rs v c) {r : ℕ} (hr : r ∈ rs) : c.reg r = v r :=
  h.2.2.2.2 r hr

theorem KS.sub {rs' : List ℕ} {v' : ℕ → ℕ} {c : Config} (h : KS m₀ F B rs v c)
    (hs : ∀ r ∈ rs', r ∈ rs ∧ v r = v' r) : KS m₀ F B rs' v' c :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun r hr => (h.get (hs r hr).1).trans (hs r hr).2⟩

theorem KS.indep {W : List ℕ} (hF : rFREE ∉ W) (hB : qBH ∉ W) (hrs : ∀ r ∈ rs, r ∉ W) :
    Indep W (KS m₀ F B rs v) := fun _ _ hA ⟨h1, h2, h3, h4, h5⟩ =>
  ⟨hA.mem ▸ h1, (hA.reg _ hF).trans h2, (hA.reg _ hB).trans h3, hA.out ▸ h4,
    fun r hr => (hA.reg r (hrs r hr)).trans (h5 r hr)⟩

/-- A step changing only `d` and `rT`. -/
theorem KS.update {c c' : Config} (h : KS m₀ F B rs v c) {d z : ℕ} (hA : Agree [d, rT] c c')
    (hd : c'.reg d = z) (hrT : rT ∉ rs) (hdF : d ≠ rFREE ∧ d ≠ qBH) :
    KS m₀ F B (d :: rs) (Function.update v d z) c' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨hA.mem ▸ h1, (hA.reg _ (by simp [Ne.symm hdF.1])).trans h2,
    (hA.reg _ (by simp [Ne.symm hdF.2])).trans h3, hA.out ▸ h4, fun r hr => ?_⟩
  by_cases hrd : r = d
  · subst hrd; simp [hd]
  · have hr' : r ∈ rs := by simpa [hrd] using hr
    have hrT' : r ≠ rT := fun e => hrT (e ▸ hr')
    rw [Function.update_of_ne hrd, hA.reg r (by simp [hrd, hrT']), h5 r hr']

theorem KS.add {d a b : ℕ} (ha : a ∈ rs) (hb : b ∈ rs) (hrT : rT ∉ rs)
    (hdF : d ≠ rFREE ∧ d ≠ qBH) :
    HT (.add d a b) (KS m₀ F B rs v) (KS m₀ F B (d :: rs) (Function.update v d (v a + v b))) 1 :=
  HT.run_le trivial le_rfl fun c h =>
    h.update (agree_run (s := .add d a b) trivial rfl rfl (by simp [wregs]) c)
      (by simp [h.get ha, h.get hb]) hrT hdF

theorem KS.addc {d a k : ℕ} (ha : a ∈ rs) (haT : a ≠ rT) (hrT : rT ∉ rs)
    (hdF : d ≠ rFREE ∧ d ≠ qBH) :
    HT (addc d a k) (KS m₀ F B rs v) (KS m₀ F B (d :: rs) (Function.update v d (v a + k))) 2 :=
  HT.run_le (by simp) (by simp) fun c h =>
    h.update (agree_run (by simp) rfl rfl (by simp) c) (by simp [run_addc haT, h.get ha]) hrT hdF

theorem KS.subc {d a k : ℕ} (ha : a ∈ rs) (haT : a ≠ rT) (hrT : rT ∉ rs)
    (hdF : d ≠ rFREE ∧ d ≠ qBH) :
    HT (subc d a k) (KS m₀ F B rs v) (KS m₀ F B (d :: rs) (Function.update v d (v a - k))) 2 :=
  HT.run_le (by simp) (by simp) fun c h =>
    h.update (agree_run (by simp) rfl rfl (by simp) c) (by simp [run_subc haT, h.get ha]) hrT hdF

theorem KS.mov {d a : ℕ} (ha : a ∈ rs) (haT : a ≠ rT) (hrT : rT ∉ rs)
    (hdF : d ≠ rFREE ∧ d ≠ qBH) :
    HT (mov d a) (KS m₀ F B rs v) (KS m₀ F B (d :: rs) (Function.update v d (v a))) 2 :=
  HT.run_le (by simp) (by simp) fun c h =>
    h.update (agree_run (by simp) rfl rfl (by simp) c) (by simp [run_mov haT, h.get ha]) hrT hdF

theorem KS.const {d z : ℕ} (hrT : rT ∉ rs) (hdF : d ≠ rFREE ∧ d ≠ qBH) :
    HT (.const d z) (KS m₀ F B rs v) (KS m₀ F B (d :: rs) (Function.update v d z)) 1 :=
  HT.run_le trivial le_rfl fun c h =>
    h.update (agree_run (s := .const d z) trivial rfl rfl (by simp [wregs]) c) (by simp) hrT hdF

/-- **Multiplication** `d := x · y` (cost in the size of the second factor), within the space
allowance of its cost above `F` (the scratch table, `2 · size y` cells). -/
theorem KS.mulN {S : ℕ} (hZ0 : ZeroFrom m₀ F) {d x y : ℕ} (hx : x ∉ Arith.arithW)
    (hy : y ∉ Arith.arithW) (hxr : x ∈ rs) (hyr : y ∈ rs)
    (hdF : rFREE ∉ d :: Arith.arithW ∧ qBH ∉ d :: Arith.arithW)
    (hrs : ∀ r ∈ rs, r ≠ d → r ∉ Arith.arithW) :
    HTF S F (Arith.mulN d x y) (KS m₀ F B rs v)
      (KS m₀ F B (d :: rs) (Function.update v d (v x * v y))) (Arith.mulCost (v y)) := by
  intro hS
  let P : Config → Prop := fun c => c.mem = m₀ ∧ c.reg rFREE = F ∧ c.reg qBH = B ∧ c.out = [] ∧
    ∀ r ∈ rs, r ≠ d → c.reg r = v r
  have hP : Indep (d :: Arith.arithW) P := by
    intro c c' hA ⟨h1, h2, h3, h4, h5⟩
    refine ⟨hA.mem ▸ h1, (hA.reg _ hdF.1).trans h2, (hA.reg _ hdF.2).trans h3, hA.out ▸ h4,
      fun r hr hrd => ?_⟩
    rw [hA.reg r (by simp [hrd, hrs r hr hrd]), h5 r hr hrd]
  refine (Arith.HTB.mulN (a := v x) (b := v y) hx hy hP
    (fun c hc => by rw [hc.1, hc.2.1]; exact hZ0)
    (fun c hc => by rw [hc.2.1]; unfold Arith.mulCost at hS; omega)).mono
    (fun c h => ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun r hr _ => h.get hr⟩, h.get hxr, h.get hyr⟩)
    (fun c ⟨⟨h1, h2, h3, h4, h5⟩, hd⟩ => ⟨h1, h2, h3, h4, fun r hr => ?_⟩) le_rfl
  by_cases hrd : r = d
  · subst hrd; simp [hd]
  · rw [Function.update_of_ne hrd]
    exact h5 r (by simpa [hrd] using hr) hrd

end KS

/-! ### `⌈log₂ x⌉` by doubling -/

/-- `dst := Nat.clog 2 (reg src)`: `w := 1`, double `w` while `w < reg src`. -/
def clogLoop (dst src w : ℕ) : Stmt :=
  .seq (.const dst 0) (.seq (.const w 1) (whileC (.sub rT src w) (.seq (.add w w w) (inc dst))))

/-- The cost of `clogLoop` on `x`. -/
def clogCost (x : ℕ) : ℕ := 2 + (1 + (Nat.clog 2 x * 5 + 1))

/-- The invariant of `clogLoop` (after the test). -/
def ClogInv (P : Config → Prop) (dst w x : ℕ) (c : Config) : Prop :=
  P c ∧ c.reg w = 2 ^ c.reg dst ∧ c.reg dst ≤ Nat.clog 2 x ∧ (c.reg rT = 0 ↔ x ≤ 2 ^ c.reg dst)

/-- **`⌈log₂⌉`** in `O(log x)` steps. -/
theorem clogLoop_spec {P : Config → Prop} {dst src w x : ℕ}
    (hreg : dst ≠ rT ∧ w ≠ rT ∧ src ≠ rT ∧ dst ≠ w ∧ src ≠ dst ∧ src ≠ w)
    (hP : Indep [dst, w, rT] P) (hx : ∀ c, P c → c.reg src = x) :
    HT (clogLoop dst src w) P (fun c => P c ∧ c.reg dst = Nat.clog 2 x) (clogCost x) := by
  obtain ⟨hdT, hwT, hsT, hdw, hsd, hsw⟩ := hreg
  have h0 : HT (.seq (.const dst 0) (.const w 1)) P
      (fun c => P c ∧ c.reg dst = 0 ∧ c.reg w = 1) 2 :=
    HT.run_le ⟨trivial, trivial⟩ le_rfl fun c hc => by
      refine ⟨hP.setReg (by simp) _ (hP.setReg (by simp) _ hc), ?_, ?_⟩ <;>
        simp [hdw]
  have hc0 : HT (.sub rT src w) (fun c => P c ∧ c.reg dst = 0 ∧ c.reg w = 1)
      (fun c => ClogInv P dst w x c ∧ Nat.clog 2 x - c.reg dst ≤ Nat.clog 2 x) 1 :=
    HT.run_le trivial le_rfl fun c ⟨hc, hd, hw⟩ => by
      have hs := hx c hc
      refine ⟨⟨hP.setReg (by simp) _ hc, ?_, ?_, ?_⟩, Nat.sub_le _ _⟩
      · simp [hwT, hdT, hd, hw]
      · simp [hdT, hd]
      · simp [hdT, hd, hw, hs]; omega
  have hstep : ∀ n, HT (.seq (.seq (.add w w w) (inc dst)) (.sub rT src w))
      (fun c => ClogInv P dst w x c ∧ c.reg rT ≠ 0 ∧ Nat.clog 2 x - c.reg dst = n)
      (fun c => ClogInv P dst w x c ∧ Nat.clog 2 x - c.reg dst < n) 4 := fun n =>
    HT.run_le (by simp [LoopFree]) (by simp [size]) fun c ⟨⟨hc, hw, hle, hiff⟩, hT, hn⟩ => by
      have hs := hx c hc
      have hlt : 2 ^ c.reg dst < x := by
        by_contra h'; exact hT (hiff.mpr (by omega))
      have hlt' : c.reg dst < Nat.clog 2 x := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr hlt
      simp only [run_seq', run_add, run_inc hdT, run_sub]
      refine ⟨⟨hP.setReg (by simp) _ (hP.setReg (by simp) _ (hP.setReg (by simp) _
        (hP.setReg (by simp) _ hc))), ?_, ?_, ?_⟩, ?_⟩
      · simp [hwT, hdT, hdw, Ne.symm hdw, hw, pow_succ]; ring
      · simp [hdT, hdw]; omega
      · simp [hdT, hsT, hwT, hdw, Ne.symm hdw, hsd, hsw, hs, hw, pow_succ]; omega
      · simp [hdT, hdw]; omega
  have hl := HT.whileC (cond := .sub rT src w) (body := .seq (.add w w w) (inc dst))
    (μ := fun c => Nat.clog 2 x - c.reg dst) (K := Nat.clog 2 x) hc0 hstep
  refine ZeroCost.HT.assoc ((h0.seq hl).mono (b' := clogCost x) (fun _ h => h)
    (fun c ⟨hinv, hT⟩ => ?_) (by unfold clogCost; omega))
  obtain ⟨hc, _, hle, hiff⟩ := hinv
  have h1 : Nat.clog 2 x ≤ c.reg dst := Nat.clog_le_of_le_pow (hiff.mp hT)
  exact ⟨hc, by omega⟩

theorem KS.clog {m₀ : ℕ → ℕ} {F B : ℕ} {rs : List ℕ} {v : ℕ → ℕ} {dst src w : ℕ}
    (hreg : dst ≠ rT ∧ w ≠ rT ∧ src ≠ rT ∧ dst ≠ w ∧ src ≠ dst ∧ src ≠ w)
    (hsr : src ∈ rs) (hrs : ∀ r ∈ rs, r ≠ dst → r ≠ w ∧ r ≠ rT)
    (hdF : rFREE ∉ [dst, w, rT] ∧ qBH ∉ [dst, w, rT]) :
    HT (clogLoop dst src w) (KS m₀ F B rs v)
      (KS m₀ F B (dst :: rs) (Function.update v dst (Nat.clog 2 (v src)))) (clogCost (v src)) := by
  let P : Config → Prop := fun c => c.mem = m₀ ∧ c.reg rFREE = F ∧ c.reg qBH = B ∧ c.out = [] ∧
    ∀ r ∈ rs, r ≠ dst → c.reg r = v r
  have hP : Indep [dst, w, rT] P := by
    intro c c' hA ⟨h1, h2, h3, h4, h5⟩
    refine ⟨hA.mem ▸ h1, (hA.reg _ hdF.1).trans h2, (hA.reg _ hdF.2).trans h3, hA.out ▸ h4,
      fun r hr hrd => ?_⟩
    rw [hA.reg r (by simp [hrd, (hrs r hr hrd).1, (hrs r hr hrd).2]), h5 r hr hrd]
  refine (clogLoop_spec hreg hP (x := v src) (fun c hc => hc.2.2.2.2 src hsr hreg.2.2.2.2.1)).mono
    (fun c h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun r hr _ => h.get hr⟩)
    (fun c ⟨⟨h1, h2, h3, h4, h5⟩, hd⟩ => ⟨h1, h2, h3, h4, fun r hr => ?_⟩) le_rfl
  by_cases hrd : r = dst
  · subst hrd; simp [hd]
  · rw [Function.update_of_ne hrd]
    exact h5 r (by simpa [hrd] using hr) hrd

end STACS2027.Runtimes.QPRam.Parse
