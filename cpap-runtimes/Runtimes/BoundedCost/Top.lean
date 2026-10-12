module

public import Runtimes.BoundedCost.Main
public import Runtimes.Flow.Single
import Mathlib.Tactic

/-!
# Theorem 4 as one RAM program, and the manuscript's bound

With the composition theorem `Flow.pipe3_spec` (`Runtimes/Flow/Pipe.lean`), the pipeline of
`boundedCost_ram` becomes **one** RAM program `boundedCostTop F`, the cited Almost 2-SAT program `F` being
a relocated subroutine: it reads `t` and `Ψ` (Corollary 5's `stepInit` and one load), clears the
registers it used (restoring the initial configuration), and runs
* `zero5` if `Ψ = 0` (2-SAT, no solver);
* the output `[1]` if `t = 0` and `Ψ ≥ 1` (the empty assignment, of cost `0`);
* `Flow.pipe3 lenP5 build5 F extract5` otherwise (`lenP5`: the length `2m + 4 + kt` of the input).

* `boundedCost_single`: within `C B + 4 T(Ψ, 2|Γ'| + 2)` steps and addresses
  (`B = (Ψ+1)k²t + kt² + m + 1`, `2|Γ'| + 2 ≤ 2 ((Ψ+1)k²t + kt² + 1)` the length of the solver's
  input);
* `boundedCost_ram_fpt`: with `FPTBound T` (the cited `O(15^Ψ Ψ m³)`), within
  `C (15^Ψ Ψ ((Ψ+1)k²t + kt²)³ + k²t + kt² + m + 1)` steps and addresses — the manuscript's
  bound, the enumeration (`Υ_k ≥ m`) being charged separately as in the paper.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost Complexity.SAT

variable {S : ℕ}

/-! ### The length of the input -/

/-- `Flow.xL := |boundedCostInput g k Ψ|`: the length of `Flow.flowInput g (cycles g k) k`, plus one. -/
def lenP5 : Stmt := .seq Flow.lenFlow (.seq (.const Flow.yC 1) (.add Flow.xL Flow.xL Flow.yC))

theorem boundedCostInput_flow (g : Graph) (k Ψ : ℕ) :
    boundedCostInput g k Ψ = Flow.flowInput g (cycles g k) k ++ [Ψ] := rfl

theorem isCycle_all (g : Graph) (k : ℕ) : ∀ c ∈ cycles g k, IsCycle g k c :=
  Flow.isCycle_of_perm (List.Perm.refl _)

/-- **The length of the input** (`Flow.LenPost`), within the addresses below any `S ≥ bV g`. -/
theorem lenP5_spec (g : Graph) (k Ψ : ℕ) (hS : bV g ≤ S) :
    HTB S lenP5 (· = initial (boundedCostInput g k Ψ)) (Flow.LenPost (boundedCostInput g k Ψ))
      (5 * (cycles g k).length + 17) := by
  have h1 := Flow.lenFlow_value_app (S := S) (isCycle_all g k) [Ψ] hS
  have h2 : HTB S (.seq (.const Flow.yC 1) (.add Flow.xL Flow.xL Flow.yC))
      (fun c => c.reg Flow.xL = (Flow.flowInput g (cycles g k) k).length ∧
        c.mem = (initial (Flow.flowInput g (cycles g k) k ++ [Ψ])).mem ∧ c.out = [])
      (fun c => c.reg Flow.xL = (boundedCostInput g k Ψ).length ∧ c.mem = (initial (boundedCostInput g k Ψ)).mem ∧
        c.out = []) 2 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨hL, hm, ho⟩ => ⟨?_, ?_, ?_⟩
    · simp +decide only [run_seq', run_const, run_add, setReg_reg, ↓reduceIte, hL,
        boundedCostInput_flow, List.length_append, List.length_singleton]
    · simpa only [run_seq', run_const, run_add, setReg_mem, boundedCostInput_flow] using hm
    · simpa only [run_seq', run_const, run_add, setReg_out] using ho
  intro c hc
  obtain ⟨c', t, he, ⟨h1', h2', h3'⟩, ht⟩ := (h1.seq h2) c (by rw [hc, boundedCostInput_flow])
  refine ⟨c', t, he, ⟨h1', h2', h3', fun r hr => ?_⟩, by omega⟩
  have hw : ∀ x ∈ wregs lenP5, x % 4 = 3 ∧ x ≠ Flow.xJ 0 ∧ x ≠ Flow.xZ := by decide
  have hr' : r ∉ wregs lenP5 := fun hm => by
    obtain ⟨a, b, d⟩ := hw r hm
    rcases hr with hr | hr | hr
    · exact hr a
    · exact b hr
    · exact d hr
  rw [he.frame.reg r hr', hc]; rfl

/-! ### Reading `t` and `Ψ`, and restoring the initial configuration -/

/-- Setting the registers `W` to `0`. -/
def clearRegs : List ℕ → Stmt
  | [] => .skip
  | r :: W => .seq (.const r 0) (clearRegs W)

theorem loopFree_clearRegs : ∀ W : List ℕ, LoopFree (clearRegs W)
  | [] => trivial
  | _ :: W => ⟨trivial, loopFree_clearRegs W⟩

theorem memFree_clearRegs : ∀ W : List ℕ, memFree (clearRegs W) = true
  | [] => rfl
  | _ :: W => by simp [clearRegs, memFree, memFree_clearRegs W]

theorem run_clearRegs : ∀ (W : List ℕ) (c : Config),
    (run (clearRegs W) c).reg = (fun r => if r ∈ W then 0 else c.reg r) ∧
      (run (clearRegs W) c).mem = c.mem ∧ (run (clearRegs W) c).out = c.out
  | [], c => ⟨by funext r; simp [clearRegs], rfl, rfl⟩
  | r₀ :: W, c => by
    obtain ⟨h1, h2, h3⟩ := run_clearRegs W (c.setReg r₀ 0)
    simp only [clearRegs, run_seq', run_const]
    refine ⟨?_, by rw [h2]; rfl, by rw [h3]; rfl⟩
    rw [h1]; funext r
    by_cases hr : r = r₀
    · subst hr; simp
    · by_cases hw : r ∈ W
      · simp [hw]
      · simp [hw, hr, Config.setReg]

/-- The registers used before the branch. -/
def topW : List ℕ := [gK, gT, gV, gKT, gNV, rFREE, rT, sX, sY, sQ, gPSI]

/-- The configuration of the input, the registers outside `topW` zero. -/
def TopPost (x : List ℕ) (c : Config) : Prop :=
  c.mem = (initial x).mem ∧ c.out = [] ∧ ∀ r, r ∉ topW → c.reg r = 0

/-- Clearing `topW` restores the initial configuration. -/
theorem clearTop_spec (x : List ℕ) :
    HTB S (clearRegs topW) (TopPost x) (· = initial x) 12 := HTB.of_HT (memFree_clearRegs _) <| by
  refine HT.run_le (loopFree_clearRegs _) (by decide) fun c ⟨hm, ho, hr⟩ => ?_
  obtain ⟨h1, h2, h3⟩ := run_clearRegs topW c
  have e : run (clearRegs topW) c = ⟨(run (clearRegs topW) c).reg, (run (clearRegs topW) c).mem,
      (run (clearRegs topW) c).out⟩ := rfl
  rw [e, h1, h2, h3, hm, ho]
  unfold initial
  congr 1
  funext r
  by_cases hw : r ∈ topW
  · simp [hw]
  · simp [hw, hr r hw]

/-- The first block: Corollary 5's `stepInit` and `gPSI := Ψ`. -/
def readTop : Stmt := .seq stepInit (.load gPSI rFREE)

theorem readTop_spec (g : Graph) (k Ψ : ℕ) (hS : bD g k + 1 ≤ S) :
    HTB S readTop (· = initial (boundedCostInput g k Ψ))
      (fun c => TopPost (boundedCostInput g k Ψ) c ∧ c.reg gPSI = Ψ ∧ c.reg gT = (cycles g k).length)
      (5 * (cycles g k).length + 17) := by
  have h1 := (stepInitZ_spec (S := S) g k Ψ [] (by omega)).withFrame (initial (boundedCostInput g k Ψ))
  simp only [List.append_nil] at h1
  obtain ⟨-, -, -, -, hP, -⟩ := input5_facts g k Ψ
  have h2 : HTB S (.load gPSI rFREE)
      (fun c => (GA g k c ∧ c.reg rFREE = bD g k ∧ c.mem = (initial (boundedCostInput g k Ψ)).mem ∧
        c.out = []) ∧ Frame stepInit (initial (boundedCostInput g k Ψ)) c)
      (fun c => TopPost (boundedCostInput g k Ψ) c ∧ c.reg gPSI = Ψ ∧ c.reg gT = (cycles g k).length) 1 :=
    HTB.run_le (by decide) (by decide) fun c ⟨⟨hga, hfr, hm, ho⟩, hF⟩ => by
      refine ⟨by addr_ok [hfr], ⟨by simp [hm], by simp [ho], fun r hr => ?_⟩, by simp [hfr, hm, hP],
        by simp +decide [hga.rt]⟩
      have hw : ∀ x ∈ wregs stepInit, x ∈ topW := by decide
      have hr' : r ∉ wregs stepInit := fun h => hr (hw r h)
      have hne : r ≠ gPSI := fun h => hr (by rw [h]; decide)
      simp only [run_load, setReg_reg, hne, ↓reduceIte]
      rw [hF.reg r hr']; rfl
  exact (h1.pre fun c hc => ⟨hc, hc⟩).seq h2 |>.weaken (by omega)

/-! ### The single program -/

/-- **The machine of Theorem 4** (`k ≥ 4`), with the Almost 2-SAT program `F` as a subroutine. -/
def boundedCostTop (F : Stmt) : Stmt :=
  .seq readTop (.ifz gPSI (.seq (clearRegs topW) zero5)
    (.ifz gT (.seq (.const sX 1) (.write sX)) (.seq (clearRegs topW) (Flow.pipe3 lenP5 build5 F extract5))))

/-- A computation from the initial configuration as a triple. -/
theorem htb_of_computesIn {P : Stmt} {x out : List ℕ} {t S' : ℕ} (h : ComputesIn P x out t S')
    (hS : S' ≤ S) : HTB S P (· = initial x) (fun c => c.out = out) t := fun c hc => by
  obtain ⟨c', he, ho⟩ := h
  exact ⟨c', t, hc ▸ he.mono hS, ho, le_rfl⟩

/-- `N' = 2|Γ'| + 2`, the length of the solver's input. -/
def lenA (g : Graph) (k Ψ : ℕ) : ℕ := 2 * (almostFormula g k Ψ).length + 2

/-- The constant of the single program. -/
def CT5 : ℕ := 30 * C5

/-- **The single program**, with the exact case split: the solver's term only when `Ψ ≥ 1` and
`t ≥ 1`. -/
theorem boundedCostTop_spec {F : RAM.Stmt} {T : ℕ → ℕ → ℕ} (hA : Almost2SatSolver F T) (g : Graph)
    (k Ψ : ℕ) (hk : 4 ≤ k) :
    ∃ (out : List ℕ) (steps : ℕ),
      RAM.ComputesIn (boundedCostTop F) (boundedCostInput g k Ψ) out steps
        (CT5 * bnd5 g k Ψ + (if Ψ = 0 ∨ (cycles g k).length = 0 then 0 else 4 * T Ψ (lenA g k Ψ))) ∧
      steps ≤ CT5 * bnd5 g k Ψ + (if Ψ = 0 ∨ (cycles g k).length = 0 then 0 else 4 * T Ψ (lenA g k Ψ)) ∧
      BoundedCostAnswer g k Ψ out := by
  set x := boundedCostInput g k Ψ
  set B := CT5 * bnd5 g k Ψ + (if Ψ = 0 ∨ (cycles g k).length = 0 then 0 else 4 * T Ψ (lenA g k Ψ))
  obtain ⟨h1, h2, h3, h4⟩ := bnd5_facts g k Ψ (by omega)
  have hL := lay5 g k
  have hb1 : (cycles g k).length + g.length + 1 ≤ bnd5 g k Ψ := by omega
  have hCB : C5 * bnd5 g k Ψ + 100 * bnd5 g k Ψ ≤ CT5 * bnd5 g k Ψ := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by unfold CT5 C5; omega)
  have hBB : CT5 * bnd5 g k Ψ ≤ B := Nat.le_add_right _ _
  have hD : bD g k + 1 ≤ C5 * bnd5 g k Ψ := by unfold C5; omega
  have hr := readTop_spec (S := B) g k Ψ (by omega)
  -- the three branches, each from `TopPost`
  suffices hbr : ∃ b, HTB B (.ifz gPSI (.seq (clearRegs topW) zero5)
      (.ifz gT (.seq (.const sX 1) (.write sX)) (.seq (clearRegs topW) (Flow.pipe3 lenP5 build5 F extract5))))
      (fun c => TopPost x c ∧ c.reg gPSI = Ψ ∧ c.reg gT = (cycles g k).length)
      (fun c => BoundedCostAnswer g k Ψ c.out) b ∧ 5 * (cycles g k).length + 17 + b ≤ B by
    obtain ⟨b, hb, hle⟩ := hbr
    obtain ⟨out, t, ht, ho, hc⟩ := HTB.computesIn_post (hr.seq hb)
    exact ⟨out, t, hc, ht.trans hle, ho⟩
  by_cases hΨ : Ψ = 0
  · -- `Ψ = 0`: 2-SAT
    subst hΨ
    obtain ⟨out, t₀, hc, ht, ho⟩ := zero5_ram g k hk
    refine ⟨12 + t₀ + 1, HTB.ifz (b := 12 + t₀) ?_ ?_, ?_⟩
    · exact ((clearTop_spec x).pre fun c h => h.1.1).seq
        ((htb_of_computesIn hc (by omega)).post fun c h => h ▸ ho)
    · exact HTB.of_false fun c ⟨⟨_, h, _⟩, hne⟩ => hne h
    · omega
  · by_cases ht0 : (cycles g k).length = 0
    · -- no cycle: `[1]`
      refine ⟨5, HTB.ifz (b := 4) ?_ ?_, by omega⟩
      · exact HTB.of_false fun c ⟨⟨_, h, _⟩, h0⟩ => hΨ (h ▸ h0)
      refine HTB.ifz (b := 3) ?_ ?_
      swap
      · exact HTB.of_false fun c ⟨⟨⟨_, _, h⟩, _⟩, hne⟩ => hne (by rw [h, ht0])
      refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨⟨⟨_, ho, _⟩, _⟩, _⟩, _⟩ => ?_
      refine Or.inr ⟨[], by simp [ho], by simp [ht0], by simp, ?_, ?_⟩
      · rw [List.eq_nil_of_length_eq_zero ht0]; simp [ValidChoices]
      · rw [List.eq_nil_of_length_eq_zero ht0]; simp [cost]
    · -- the pipeline
      obtain ⟨ans, out, t₁, t₂, t₃, h₁, ht₁, h₂, ht₂, hlen, h₃, ht₃, ho⟩ := pipeline5 hA g k Ψ hk
      have hb := buildCost_le g k Ψ (by omega)
      have hfs := formSpace_le g k Ψ (by omega)
      have hec := extractCost_le g k Ψ (by omega)
      have hes := extractSpace_le g k Ψ (by omega)
      have hl := almost_len_le g k Ψ
      have hx : x.length = bD g k + 1 := length_boundedCostInput g k Ψ
      have hy : (a2In (shiftF (almostFormula g k Ψ)) Ψ).length = lenA g k Ψ := by
        rw [a2In, List.length_cons, List.length_cons, codes_shiftF, List.length_map,
          length_codes_almost]; rfl
      have hlenA : lenA g k Ψ = 2 * (almostFormula g k Ψ).length + 2 := rfl
      rw [← hlenA] at ht₂
      obtain ⟨tp, hcp, htp⟩ := Flow.pipe3_spec (lenP5_spec (S := bV g) g k Ψ le_rfl) h₁ h₂ h₃
      rw [hx, hy] at hcp
      rw [hx] at htp
      have hB : B = CT5 * bnd5 g k Ψ + 4 * T Ψ (lenA g k Ψ) := by
        simp only [B, hΨ, ht0, or_self, ↓reduceIte]
      have hlA : lenA g k Ψ ≤ 2 * bnd5 g k Ψ := by unfold lenA; omega
      have hans : ans.length ≤ 2 * bnd5 g k Ψ := by omega
      have hbV : bV g ≤ bD g k := by omega
      have hsp : bV g + 4 * (bD g k + 1 + lenA g k Ψ + ans.length + formSpace g k Ψ +
          T Ψ (lenA g k Ψ) + extractSpace g k Ψ) ≤ B := by
        rw [hB]
        have h30 : 4 * (4 * (C5 * bnd5 g k Ψ)) ≤ CT5 * bnd5 g k Ψ := by
          rw [show 4 * (4 * (C5 * bnd5 g k Ψ)) = 16 * C5 * bnd5 g k Ψ by ring]
          exact Nat.mul_le_mul_right _ (by unfold CT5 C5; omega)
        omega
      refine ⟨12 + tp + 1 + 1, HTB.ifz (b := 12 + tp + 1) ?_ ?_, ?_⟩
      · exact HTB.of_false fun c ⟨⟨_, h, _⟩, h0⟩ => hΨ (h ▸ h0)
      · refine HTB.ifz (b := 12 + tp) ?_ ?_
        · exact HTB.of_false fun c ⟨⟨⟨_, _, h⟩, _⟩, h0⟩ => ht0 (h ▸ h0)
        exact ((clearTop_spec x).pre fun c h => h.1.1.1).seq
          ((htb_of_computesIn hcp hsp).post fun c h => h ▸ ho)
      · rw [hB]; unfold CT5 C5 at *; omega

/-- **Theorem 4 as one RAM program** (`k ≥ 4`), the cited Almost 2-SAT program `F` being a
subroutine: one program and one constant `C` such that for every graph `g`, every `k ≥ 4` and
every `Ψ`, on `boundedCostInput g k Ψ` the program halts within `C B + 4 T(Ψ, 2|Γ'| + 2)` steps,
accessing only the addresses below the same bound (`B = (Ψ+1)k²t + kt² + m + 1`;
`2|Γ'| + 2 ≤ 2((Ψ+1)k²t + kt² + 1)` is the length of the solver's input), with Theorem 4's
answer. -/
theorem boundedCost_single {F : RAM.Stmt} {T : ℕ → ℕ → ℕ} (hA : Almost2SatSolver F T) :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (k Ψ : ℕ), 4 ≤ k →
      ∃ (out : List ℕ) (steps : ℕ),
        RAM.ComputesIn prog (boundedCostInput g k Ψ) out steps
          (C * ((Ψ + 1) * k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length + g.length + 1) +
            4 * T Ψ (2 * (almostFormula g k Ψ).length + 2)) ∧
        steps ≤ C * ((Ψ + 1) * k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length + g.length + 1) +
            4 * T Ψ (2 * (almostFormula g k Ψ).length + 2) ∧
        BoundedCostAnswer g k Ψ out := by
  refine ⟨boundedCostTop F, CT5, fun g k Ψ hk => ?_⟩
  obtain ⟨out, steps, hc, hs, ho⟩ := boundedCostTop_spec hA g k Ψ hk
  have hle : (if Ψ = 0 ∨ (cycles g k).length = 0 then 0 else 4 * T Ψ (lenA g k Ψ)) ≤
      4 * T Ψ (2 * (almostFormula g k Ψ).length + 2) := by
    split_ifs <;> simp [lenA]
  exact ⟨out, steps, hc.mono (Nat.add_le_add_left hle _), hs.trans (Nat.add_le_add_left hle _), ho⟩

/-! ### The manuscript's bound -/

/-- `P = 15^Ψ Ψ ((Ψ+1)k²t + kt²)³ + k²t + kt² + m + 1`. -/
def paper5 (g : Graph) (k Ψ : ℕ) : ℕ :=
  15 ^ Ψ * Ψ * ((Ψ + 1) * k * k * (cycles g k).length +
    k * (cycles g k).length * (cycles g k).length) ^ 3 + k * k * (cycles g k).length +
    k * (cycles g k).length * (cycles g k).length + g.length + 1

/-- Without the solver (`Ψ = 0` or `t = 0`), `B ≤ P`; with it, `B ≤ 2P`. -/
theorem bnd5_le_paper (g : Graph) (k Ψ : ℕ) : bnd5 g k Ψ ≤ 2 * paper5 g k Ψ := by
  unfold bnd5 paper5
  set t := (cycles g k).length
  set X := (Ψ + 1) * k * k * t + k * t * t
  have e : (Ψ + 1) * k * k * t = k * k * t + Ψ * (k * k * t) := by ring
  rcases Nat.eq_zero_or_pos Ψ with h | h
  · subst h; omega
  · have hX : Ψ * (k * k * t) ≤ 15 ^ Ψ * Ψ * X ^ 3 := by
      rcases Nat.eq_zero_or_pos X with hx | hx
      · have : Ψ * (k * k * t) ≤ Ψ * X := Nat.mul_le_mul_left _ (by omega)
        rw [hx] at this ⊢; simpa using this
      · calc Ψ * (k * k * t) ≤ Ψ * X ^ 3 :=
              Nat.mul_le_mul_left _ ((show k * k * t ≤ X by omega).trans
                (by simpa using Nat.pow_le_pow_right hx (show 1 ≤ 3 by norm_num)))
          _ ≤ 15 ^ Ψ * (Ψ * X ^ 3) := Nat.le_mul_of_pos_left _ (by positivity)
          _ = 15 ^ Ψ * Ψ * X ^ 3 := by ring
    omega

/-- The solver's term under `FPTBound`, for `Ψ ≥ 1` and `t ≥ 1`. -/
theorem solver_le_paper {T : ℕ → ℕ → ℕ} {Cf : ℕ}
    (hT : ∀ Ψ N : ℕ, T Ψ N ≤ Cf * 15 ^ Ψ * (Ψ + 1) * (N + 1) ^ 3) (g : Graph) (k Ψ : ℕ)
    (hΨ : 1 ≤ Ψ) (ht : 1 ≤ (cycles g k).length) (hk : 1 ≤ k) :
    T Ψ (lenA g k Ψ) ≤ 250 * Cf * paper5 g k Ψ := by
  have hl := almost_len_le g k Ψ
  have hpos : 1 ≤ k * (cycles g k).length * (cycles g k).length := Nat.mul_pos (Nat.mul_pos hk ht) ht
  unfold paper5
  unfold lenA at *
  set t := (cycles g k).length
  set X := (Ψ + 1) * k * k * t + k * t * t
  have hX1 : 1 ≤ X := by omega
  have hN : 2 * (almostFormula g k Ψ).length + 2 + 1 ≤ 5 * X := by omega
  have hcube : (2 * (almostFormula g k Ψ).length + 2 + 1) ^ 3 ≤ 125 * X ^ 3 :=
    calc (2 * (almostFormula g k Ψ).length + 2 + 1) ^ 3 ≤ (5 * X) ^ 3 := Nat.pow_le_pow_left hN 3
      _ = 125 * X ^ 3 := by ring
  have hP : 15 ^ Ψ * Ψ * X ^ 3 ≤ 15 ^ Ψ * Ψ * X ^ 3 + k * k * t + k * t * t + g.length + 1 := by
    omega
  calc T Ψ (2 * (almostFormula g k Ψ).length + 2) ≤
        Cf * 15 ^ Ψ * (Ψ + 1) * (2 * (almostFormula g k Ψ).length + 2 + 1) ^ 3 := hT _ _
    _ ≤ Cf * 15 ^ Ψ * (2 * Ψ) * (125 * X ^ 3) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hcube
    _ = 250 * Cf * (15 ^ Ψ * Ψ * X ^ 3) := by ring
    _ ≤ 250 * Cf * (15 ^ Ψ * Ψ * X ^ 3 + k * k * t + k * t * t + g.length + 1) :=
        Nat.mul_le_mul_left _ hP

/-- **Theorem 4 with the manuscript's bound** (`k ≥ 4`, `FPTBound T`): the answer on `boundedCostInput`
within `C (15^Ψ Ψ ((Ψ+1)k²t + kt²)³ + k²t + kt² + m + 1)` steps and addresses. -/
theorem boundedCost_ram_fpt {F : RAM.Stmt} {T : ℕ → ℕ → ℕ} (hA : Almost2SatSolver F T)
    (hT : FPTBound T) :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (k Ψ : ℕ), 4 ≤ k →
      ∃ (out : List ℕ) (steps : ℕ),
        RAM.ComputesIn prog (boundedCostInput g k Ψ) out steps
          (C * (15 ^ Ψ * Ψ * ((Ψ + 1) * k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length) ^ 3 + k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length + g.length + 1)) ∧
        steps ≤ C * (15 ^ Ψ * Ψ * ((Ψ + 1) * k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length) ^ 3 + k * k * (cycles g k).length +
            k * (cycles g k).length * (cycles g k).length + g.length + 1) ∧
        BoundedCostAnswer g k Ψ out := by
  obtain ⟨Cf, hCf⟩ := hT
  refine ⟨boundedCostTop F, 2 * CT5 + 1000 * Cf, fun g k Ψ hk => ?_⟩
  obtain ⟨out, steps, hc, hs, ho⟩ := boundedCostTop_spec hA g k Ψ hk
  have hB := bnd5_le_paper g k Ψ
  have hle : CT5 * bnd5 g k Ψ + (if Ψ = 0 ∨ (cycles g k).length = 0 then 0 else
      4 * T Ψ (lenA g k Ψ)) ≤ (2 * CT5 + 1000 * Cf) * paper5 g k Ψ := by
    have h1 : CT5 * bnd5 g k Ψ ≤ CT5 * (2 * paper5 g k Ψ) := Nat.mul_le_mul_left _ hB
    have e : (2 * CT5 + 1000 * Cf) * paper5 g k Ψ =
        CT5 * (2 * paper5 g k Ψ) + 4 * (250 * Cf * paper5 g k Ψ) := by ring
    rw [e]
    split_ifs with h
    · omega
    · obtain ⟨h1, h2⟩ := not_or.mp h
      have := solver_le_paper hCf g k Ψ (by omega) (by omega) (by omega)
      omega
  exact ⟨out, steps, hc.mono hle, hs.trans hle, ho⟩

end STACS2027.Runtimes.BoundedCost
