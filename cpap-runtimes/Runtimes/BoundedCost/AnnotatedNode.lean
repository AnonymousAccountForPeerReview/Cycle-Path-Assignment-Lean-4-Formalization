module

public import Runtimes.BoundedCost.SearchScan
import Mathlib.Tactic

/-! The concrete bounded RAM update at an annotated search node, after the
least-cut assignment and the readonly clause scan have been computed. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM

abbrev nodeBudget : ℕ := 221
abbrev nodeForcedBase : ℕ := 222
abbrev nodeSuccess : ℕ := 227
abbrev nodeLive : ℕ := 228
abbrev nodeChoice : ℕ := 340
abbrev nodeIndex : ℕ := 341
abbrev nodeValue : ℕ := 342
abbrev nodeChoiceTail : ℕ := 343

inductive NodeAction where
  | accept
  | prune
  | delete (index : ℕ)
  | force (literal : ℕ)
  deriving DecidableEq

def nodeAction (summary : SearchSummary) (budget choice : ℕ) : NodeAction :=
  if summary.unsatisfied ≤ budget then .accept
  else if budget < summary.cut then .prune
  else if summary.conflict = 0 then .prune
  else if choice = 0 then
    if budget = 0 then .prune else .delete (summary.conflict - 1)
  else if choice = 1 then .force summary.firstLiteral
  else if choice = 2 then .force summary.secondLiteral
  else .prune

def nodeActionMemory (action : NodeAction) (active forced : ℕ)
    (memory : ℕ → ℕ) : ℕ → ℕ :=
  match action with
  | .delete i => upd memory (active + i) 0
  | .force a => upd memory (forced + a) 1
  | _ => memory

def nodeActionBudget (action : NodeAction) (budget : ℕ) : ℕ :=
  match action with
  | .delete _ => budget - 1
  | _ => budget

def nodeActionLive : NodeAction → ℕ
  | .delete _ | .force _ => 1
  | _ => 0

def nodeActionSuccess (action : NodeAction) (success : ℕ) : ℕ :=
  match action with
  | .accept => 1
  | _ => success

def nodeAccept : Stmt := .seq (.const nodeSuccess 1) (.const nodeLive 0)
def nodePrune : Stmt := .const nodeLive 0

def nodeDelete : Stmt :=
  .ifz nodeBudget nodePrune
    (.seq (subc nodeIndex scanConflict 1)
      (.seq (.const nodeValue 0)
        (.seq (st scanActiveBase nodeIndex nodeValue) (dec nodeBudget))))

def nodeForce (literal : ℕ) : Stmt :=
  .seq (.const nodeValue 1) (st nodeForcedBase literal nodeValue)

def nodeBranch : Stmt :=
  .ifz nodeChoice nodeDelete
    (.seq (subc nodeChoiceTail nodeChoice 1)
      (.ifz nodeChoiceTail (nodeForce scanFirstLiteral)
        (.seq (dec nodeChoiceTail)
          (.ifz nodeChoiceTail (nodeForce scanSecondLiteral) nodePrune))))

def annotatedNodeUpdate : Stmt :=
  ifLe scanUnsatisfied nodeBudget nodeAccept
    (ifLt nodeBudget scanCut nodePrune (.ifz scanConflict nodePrune nodeBranch))

def NodeGlobals (active forced budget choice success : ℕ) (summary : SearchSummary)
    (c : Config) : Prop :=
  c.reg scanActiveBase = active ∧ c.reg nodeForcedBase = forced ∧
    c.reg nodeBudget = budget ∧ c.reg nodeChoice = choice ∧
    c.reg nodeSuccess = success ∧ c.reg nodeLive = 1 ∧ SearchSummaryRep summary c

def NodeUpdated (active forced budget choice success : ℕ) (summary : SearchSummary)
    (memory : ℕ → ℕ) (c : Config) : Prop :=
  let action := nodeAction summary budget choice
  c.reg scanActiveBase = active ∧ c.reg nodeForcedBase = forced ∧
    c.reg nodeBudget = nodeActionBudget action budget ∧ c.reg nodeChoice = choice ∧
    c.reg nodeSuccess = nodeActionSuccess action success ∧
    c.reg nodeLive = nodeActionLive action ∧ SearchSummaryRep summary c ∧
    c.mem = nodeActionMemory action active forced memory

theorem annotatedNodeUpdate_spec {S active forced count bound budget choice success : ℕ}
    {summary : SearchSummary} {memory : ℕ → ℕ}
    (hconflict : summary.conflict ≤ count)
    (hfirst : summary.firstLiteral < bound) (hsecond : summary.secondLiteral < bound)
    (hactive : active + count ≤ S) (hforced : forced + bound ≤ S) :
    HTB S annotatedNodeUpdate
      (fun c => NodeGlobals active forced budget choice success summary c ∧ c.mem = memory)
      (NodeUpdated active forced budget choice success summary memory) 100 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨ha, hf, hk, hch, hs, hl, hu, hc, hd, hfl, hsl⟩, hm⟩
  have hforceFirst : forced + summary.firstLiteral < S := by omega
  have hforceSecond : forced + summary.secondLiteral < S := by omega
  have hdelete : summary.conflict ≠ 0 → active + (summary.conflict - 1) < S := by omega
  constructor
  · simp +decide only [annotatedNodeUpdate, nodeBranch, nodeDelete, nodePrune,
      nodeAccept, nodeForce, addrOK_ifLe, addrOK_ifLt, addrOK_ifz, addrOK_seq,
      addrOK_const, addrOK_subc, addrOK_dec, addrOK_st, run_sub, run_const,
      run_subc, run_dec, run_seq', run_ifz', setReg_reg, setReg_mem,
      ha, hf, hk, hch, hs, hl, hu, hc, hd, hfl, hsl, ↓reduceIte, true_and]
    aesop
  · simp +decide only [NodeUpdated, nodeAction, nodeActionMemory, nodeActionBudget,
      nodeActionLive, nodeActionSuccess, SearchSummaryRep, annotatedNodeUpdate,
      nodeBranch, nodeDelete, nodePrune, nodeAccept, nodeForce, ifLe, ifLt,
      run_sub, run_const, run_subc, run_dec, run_st, run_seq', run_ifz',
      setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd,
      ha, hf, hk, hch, hs, hl, hu, hc, hd, hfl, hsl, hm, ↓reduceIte]
    split_ifs <;> simp_all <;> omega

end STACS2027.Runtimes.BoundedCost
