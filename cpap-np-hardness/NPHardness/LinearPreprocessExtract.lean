module

public import NPHardness.LinearPreprocessUnits

/-!
Charged extraction from the unit-propagation clause table. Each scan step
reads one indexed cell and optionally conses a live clause pointer. The live
clause count is maintained explicitly for the later padding stage. Reversal
is a separate one-record-per-step pass.
-/

@[expose] public section
namespace STACS2027.LinearPreprocessExtract
open Complexity.SAT
open LinearPreprocessUnits

inductive State where
  | scan (next remaining : Nat) (reversed : CNF) (count : Nat)
  | reverse (remaining output : CNF) (count : Nat)
  | done (output : CNF) (count : Nat)

def step (mem : Memory) : State → State
  | .scan _ 0 acc count => .reverse acc [] count
  | .scan j (r+1) acc count =>
    match mem j with
    | none => .scan (j+1) r acc count
    | some c => .scan (j+1) r (c::acc) (count+1)
  | .reverse [] out count => .done out count
  | .reverse (c::cs) out count => .reverse cs (c::out) count
  | .done out count => .done out count

inductive Executes (mem : Memory) : Nat → State → State → Prop where
  | refl (s) : Executes mem 0 s s
  | next {t s u} : Executes mem t (step mem s) u → Executes mem (t+1) s u

theorem Executes.trans {mem : Memory} {t u : Nat} {s q r : State}
    (h : Executes mem t s q) (g : Executes mem u q r) : Executes mem (t+u) s r := by
  induction h with
  | refl => simpa using g
  | next h ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Executes.next (ih g)

theorem run_scan (mem : Memory) (j r : Nat) (acc : CNF) (count : Nat) :
    Executes mem (r+1) (.scan j r acc count)
      (.reverse (((List.range' j r).filterMap mem).reverse ++ acc) []
        (count+((List.range' j r).filterMap mem).length)) := by
  induction r generalizing j acc count with
  | zero => simpa [step] using (Executes.next (s := .scan j 0 acc count)
      (Executes.refl (.reverse acc [] count)))
  | succ r ih =>
    cases hm : mem j with
    | none =>
      have h := ih (j+1) acc count
      have hs : step mem (.scan j (r+1) acc count) = .scan (j+1) r acc count := by simp [step,hm]
      rw [← hs] at h
      simpa [List.range'_succ,hm] using Executes.next h
    | some c =>
      have h := ih (j+1) (c::acc) (count+1)
      have hs : step mem (.scan j (r+1) acc count) = .scan (j+1) r (c::acc) (count+1) := by simp [step,hm]
      rw [← hs] at h
      simpa [List.range'_succ,hm,List.reverse_cons,List.append_assoc,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Executes.next h

theorem run_reverse (mem : Memory) (cs out : CNF) (count : Nat) :
    Executes mem (cs.length+1) (.reverse cs out count) (.done (cs.reverse ++ out) count) := by
  induction cs generalizing out with
  | nil => exact Executes.next (Executes.refl _)
  | cons c cs ih =>
    apply Executes.next
    simpa [step,List.reverse_cons,List.append_assoc] using ih (c::out)

theorem executes_contents (size : Nat) (mem : Memory) :
    Executes mem (size+(contents size mem).length+2) (.scan 0 size [] 0)
      (.done (contents size mem) (contents size mem).length) := by
  have hs := run_scan mem 0 size [] 0
  simp only [← List.range_eq_range',List.append_nil,Nat.zero_add] at hs
  have hr := run_reverse mem (contents size mem).reverse [] (contents size mem).length
  have h := hs.trans hr
  have ht : size+1+((contents size mem).reverse.length+1) = size+(contents size mem).length+2 := by
    simp only [List.length_reverse]
    omega
  rw [ht] at h
  simpa [contents] using h

theorem extraction_linear (size : Nat) (mem : Memory) :
    ∃ t, Executes mem t (.scan 0 size [] 0) (.done (contents size mem) (contents size mem).length) ∧
      t ≤ 2*size+2 := by
  have hl : (contents size mem).length ≤ size := by
    simpa [contents] using List.length_filterMap_le mem (List.range size)
  exact ⟨_,executes_contents size mem,by omega⟩

end STACS2027.LinearPreprocessExtract
