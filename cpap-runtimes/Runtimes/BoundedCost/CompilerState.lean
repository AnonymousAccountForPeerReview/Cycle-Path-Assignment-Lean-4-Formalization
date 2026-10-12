module

public import Runtimes.BoundedCost.CompilerProgram
public import Runtimes.BoundedCost.EncodedIterative
public import Runtimes.BoundedCost.DenseTables
public import Runtimes.BoundedCost.CutFactory
import Mathlib.Tactic

/-! Fixed caller metadata and the semantic invariant of the prefix loop. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.Compiler

open STACS2027 STACS2027.RAM Complexity.SAT

@[mk_iff] structure Globals (layout : CompilerLayout) (n m k d : ℕ)
    (c : Config) : Prop where
  formula : c.reg 200 = layout.formula
  clauses : c.reg 201 = m
  active : c.reg 202 = layout.active
  candidate : c.reg 203 = layout.candidate
  reference : c.reg 204 = layout.reference
  nodes : c.reg 220 = n
  forced : c.reg 222 = layout.forced
  labels : c.reg 223 = layout.labels
  budget : c.reg 225 = k
  originalClauses : c.reg 226 = m
  edgeInput : c.reg 300 = layout.edgeInput
  innerDigits : c.reg 344 = layout.innerDigits
  depth : c.reg 345 = d
  region : c.reg 350 = 4 * layout.span + 1
  span : c.reg 400 = layout.span
  truthLength : c.reg 406 = 2 * n
  special : c.reg 430 = layout.special
  outerDigits : c.reg 433 = layout.outerDigits
  baseActive : c.reg 434 = layout.baseActive
  seedForced : c.reg 435 = layout.seedForced

theorem globals_of_initialized {constant m k : ℕ} {c : Config}
    (h : CompilerInit.Globals constant m k c) :
    Globals (compilerLayout constant m k) (2 * m + 1) m k (min k m + 1) c := by
  rcases h with ⟨hl, ha, hd⟩
  rcases hl with ⟨hs, hr, hf, hac, hc, href, hforced, hlabels, hbase, hseed,
    hspecial, houter, hinner, hsaved, hedges, hfree⟩
  rcases ha with ⟨hm, hom, hk, hn, hnp, hfactor, hcodes, htruth, hdepth, hsrc, hp⟩
  exact ⟨hf, hm, hac, hc, href, hn, hforced, hlabels, hk, hom, hedges, hinner,
    hd, hr, hs, htruth, hspecial, houter, hbase, hseed⟩

theorem Globals.leastCut {layout : CompilerLayout} {nodes m k depth : ℕ} {c : Config}
    (h : Globals layout nodes m k depth (registerView callerRegister c)) :
    LeastCutGlobals layout.formula layout.active layout.candidate layout.reference layout.forced
      layout.labels layout.edgeInput nodes m layout.span c := by
  exact ⟨⟨h.formula, h.active, h.reference, h.forced, h.labels, h.edgeInput, h.nodes,
    h.clauses⟩, h.candidate, h.region, h.span⟩

def prefixStep (factory : LeastCutFactory) (fuel k : ℕ) (original : CNF)
    (index : ℕ) : Option Assignment → Option Assignment
  | none => none
  | some σ =>
      if unsatisfiedCount σ (original.take (index + 1)) ≤ k then some σ else
        encodedCompressionSearch (factory σ) σ fuel (compressionBase σ (original.take index))
          (compressionSpecial σ (original.take index) (original.getD index [])) k

def prefixFold (factory : LeastCutFactory) (fuel k : ℕ) (original : CNF) (count : ℕ) :
    Option Assignment :=
  (List.range count).foldl (fun state i => prefixStep factory fuel k original i state)
    (some (fun _ => false))

def PrefixCorrect (original : CNF) (k count : ℕ) : Option Assignment → Prop
  | none => ¬ AlmostSatisfiable (original.take count) k
  | some σ => unsatisfiedCount σ (original.take count) ≤ k

theorem take_next {α : Type*} [Inhabited α] (original : List α) (i : ℕ)
    (hi : i < original.length) : original.take (i + 1) = original.take i ++ [original.getD i default] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]

theorem prefixStep_correct (factory : LeastCutFactory)
    (hfactory : LeastCutFactoryCorrect factory) {fuel k : ℕ} (hdepth : k < fuel)
    {original : CNF} (hf : Clauses2 original) (i : ℕ) (hi : i < original.length)
    (state : Option Assignment) (hstate : PrefixCorrect original k i state) :
    PrefixCorrect original k (i + 1) (prefixStep factory fuel k original i state) := by
  have hnext := take_next original i hi
  change original.take (i + 1) = original.take i ++ [original.getD i []] at hnext
  have hpre : Clauses2 (original.take i) := fun c hc => hf c (List.mem_of_mem_take hc)
  have hc : (original.getD i []).length = 2 := by
    rw [← List.getElem_eq_getD (h := hi) []]
    exact hf _ (List.getElem_mem hi)
  cases state with
  | none =>
    change ¬ AlmostSatisfiable (original.take (i + 1)) k
    intro hs
    obtain ⟨σ, hσ⟩ := (almostSatisfiable_iff_unsatisfiedCount _ _).mp hs
    apply hstate
    apply (almostSatisfiable_iff_unsatisfiedCount _ _).mpr
    rw [hnext, unsatisfiedCount_append] at hσ
    exact ⟨σ, by omega⟩
  | some σ =>
    change unsatisfiedCount σ (original.take i) ≤ k at hstate
    unfold prefixStep
    by_cases hs : unsatisfiedCount σ (original.take (i + 1)) ≤ k
    · simpa [hs, PrefixCorrect] using hs
    · simp only [hs, ↓reduceIte]
      let base := compressionBase σ (original.take i)
      let special := compressionSpecial σ (original.take i) (original.getD i [])
      have hb := compressionBase_clauses2 hpre σ
      have hsp := compressionSpecial_clauses2 hpre hc σ
      have hτ := compressionBase_satisfied σ (original.take i)
      have hperm := compression_partition_perm σ (original.take i) (original.getD i [])
      cases hanswer : encodedCompressionSearch (factory σ) σ fuel base special k with
      | none =>
        change ¬ AlmostSatisfiable (original.take (i + 1)) k
        intro hsol
        have hpartition : AlmostSatisfiable (base ++ special) k := by
          obtain ⟨ρ, hρ⟩ := (almostSatisfiable_iff_unsatisfiedCount _ _).mp hsol
          apply (almostSatisfiable_iff_unsatisfiedCount _ _).mpr
          refine ⟨ρ, ?_⟩
          dsimp only [base, special]
          rw [unsatisfiedCount_perm hperm, ← hnext]
          exact hρ
        obtain ⟨δ, hδ⟩ := (encodedCompressionSearch_correct (factory σ) σ (hfactory σ)
          hb hsp hτ fuel k hdepth).mpr hpartition
        rw [hanswer] at hδ
        cases hδ
      | some δ =>
        change unsatisfiedCount δ (original.take (i + 1)) ≤ k
        have hδ := encodedCompressionSearch_sound (factory σ) σ (hfactory σ) hb hsp hτ
          fuel k hanswer
        rw [unsatisfiedCount_perm hperm, ← hnext] at hδ
        exact hδ

@[simp] theorem prefixFold_zero (factory : LeastCutFactory) (fuel k : ℕ) (original : CNF) :
    prefixFold factory fuel k original 0 = some (fun _ => false) := rfl

theorem prefixFold_succ (factory : LeastCutFactory) (fuel k : ℕ) (original : CNF) (i : ℕ) :
    prefixFold factory fuel k original (i + 1) =
      prefixStep factory fuel k original i (prefixFold factory fuel k original i) := by
  simp only [prefixFold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem prefixFold_correct (factory : LeastCutFactory)
    (hfactory : LeastCutFactoryCorrect factory) {fuel k : ℕ} (hdepth : k < fuel)
    {original : CNF} (hf : Clauses2 original) (i : ℕ) (hi : i ≤ original.length) :
    PrefixCorrect original k i (prefixFold factory fuel k original i) := by
  induction i with
  | zero => simp [PrefixCorrect]
  | succ i ih =>
    rw [prefixFold_succ]
    exact prefixStep_correct factory hfactory hdepth hf i (by omega) _ (ih (by omega))

theorem prefixFold_decides (factory : LeastCutFactory)
    (hfactory : LeastCutFactoryCorrect factory) {fuel k : ℕ} (hdepth : k < fuel)
    {original : CNF} (hf : Clauses2 original) :
    HasSearchAnswer (prefixFold factory fuel k original original.length) ↔
      AlmostSatisfiable original k := by
  have h := prefixFold_correct factory hfactory hdepth hf original.length le_rfl
  cases ha : prefixFold factory fuel k original original.length with
  | none => simpa [ha, PrefixCorrect, HasSearchAnswer] using h
  | some σ =>
    constructor
    · intro _
      exact (almostSatisfiable_iff_unsatisfiedCount _ _).mpr
        ⟨σ, by simpa [ha, PrefixCorrect] using h⟩
    · intro _; exact ⟨σ, rfl⟩

end STACS2027.Runtimes.BoundedCost.Compiler
