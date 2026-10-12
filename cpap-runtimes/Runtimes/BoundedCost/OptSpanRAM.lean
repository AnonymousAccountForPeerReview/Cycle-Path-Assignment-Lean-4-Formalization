module

public import Runtimes.BoundedCost.OptArithmeticRAM
public import Runtimes.BoundedCost.OptSpanBounds
import Mathlib.Tactic

/-! # Actual arithmetic for the increasing-budget optimization wrapper -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.OptSpanRAM

open STACS2027.RAM

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
def baseProgram (C : Nat) : Stmt :=
  .seq (RAM.mul 650 620 621 678) (.seq (RAM.mul 651 650 620 678) (.seq (RAM.mul 652 650 621 678) (.seq (.add 653 651 652) (.seq (.add 654 653 650) (.seq (addc 655 654 1) (.seq (.const 656 (8*(C+1))) (.skip)))))))

def baseTime (_C k t _p : Nat) : Nat := (5*(t)+4)+((5*(k)+4)+((5*(t)+4)+((1)+((1)+((2)+((1)+(1)))))))

def positiveProgram (_C : Nat) : Stmt :=
  .seq (addc 657 622 1) (.seq (RAM.mul 658 657 651 678) (.seq (.add 659 658 652) (.seq (RAM.mul 660 659 659 678) (.seq (RAM.mul 661 660 659 678) (.seq (RAM.mul 662 622 661 678) (.seq (OptPowerRAM.program) (.seq (RAM.mul 664 663 662 678) (.seq (.add 665 655 664) (.seq (RAM.mul 624 656 665 678) (.skip))))))))))

def positiveTime (_C k t p : Nat) : Nat := (2)+((5*(((k)*(t))*(k))+4)+((1)+((5*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))+4)+((5*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))+4)+((5*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))+4)+((100*((p)+1))+((5*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))))+4)+((1)+((5*(((((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1)+((15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))))))+4)+(1))))))))))

def inputValues (k t p : Nat) := [(620,k),(621,t),(622,p)]

def baseValues (C k t p : Nat) := [(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]

def positiveValues (C k t p : Nat) := [(624,(8*(C+1))*(((((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1)+((15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))))))),(665,((((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1)+((15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))))),(664,(15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))))),(663,15^(p)),(662,(p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))),(661,(((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(660,((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]

theorem base_spec (S C k t p : Nat) :
    HTB S (baseProgram C) (Known (inputValues k t p))
      (Known (baseValues C k t p)) (baseTime C k t p) := by
  have step0 : HTB S (RAM.mul 650 620 621 678) (Known [(620,k),(621,t),(622,p)])
      (Known [(650,(k)*(t)),(620,k),(621,t),(622,p)]) (5*(t)+4) :=
    mul_known (by decide) (by intro rv h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; rcases h with rfl | rfl | rfl <;> norm_num [rT]) (by simp) (by simp)
  have step1 : HTB S (RAM.mul 651 650 620 678) (Known [(650,(k)*(t)),(620,k),(621,t),(622,p)])
      (Known [(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (5*(k)+4) :=
    mul_known (by decide) (by intro rv h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; rcases h with rfl | rfl | rfl | rfl <;> norm_num [rT]) (by simp) (by simp)
  have step2 : HTB S (RAM.mul 652 650 621 678) (Known [(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)])
      (Known [(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (5*(t)+4) :=
    mul_known (by decide) (by intro rv h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl <;> norm_num [rT]) (by simp) (by simp)
  have step3 : HTB S (.add 653 651 652) (Known [(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)])
      (Known [(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (1) :=
    add_known (by intro rv h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [rT]) (by simp) (by simp)
  have step4 : HTB S (.add 654 653 650) (Known [(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)])
      (Known [(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (1) :=
    add_known (by intro rv h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [rT]) (by simp) (by simp)
  have step5 : HTB S (addc 655 654 1) (Known [(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)])
      (Known [(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (2) :=
    addc_known (by decide) (by decide) (by intro rv h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [rT]) (by simp)
  have step6 : HTB S (.const 656 (8*(C+1))) (Known [(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)])
      (Known [(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (1) :=
    const_known (by intro rv h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [rT])
  have last : HTB S .skip (Known [(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (Known [(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) 1 :=
    by intro c hc;exact ⟨c,1,.skip c,hc,le_rfl⟩
  exact step0.seq (step1.seq (step2.seq (step3.seq (step4.seq (step5.seq (step6.seq (last)))))))

theorem positive_spec (S C k t p : Nat) :
    HTB S (positiveProgram C) (Known (baseValues C k t p))
      (Known (positiveValues C k t p)) (positiveTime C k t p) := by
  have step0 : HTB S (addc 657 622 1) (Known [(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)])
      (Known [(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (2) :=
    addc_known (by decide) (by decide) (by intro rv h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [rT]) (by simp)
  have step1 : HTB S (RAM.mul 658 657 651 678) (Known [(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)])
      (Known [(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (5*(((k)*(t))*(k))+4) :=
    mul_known (by decide) (by intro rv h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [rT]) (by simp) (by simp)
  have step2 : HTB S (.add 659 658 652) (Known [(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)])
      (Known [(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (1) :=
    add_known (by intro rv h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [rT]) (by simp) (by simp)
  have step3 : HTB S (RAM.mul 660 659 659 678) (Known [(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)])
      (Known [(660,((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (5*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))+4) :=
    mul_known (by decide) (by intro rv h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [rT]) (by simp) (by simp)
  have step4 : HTB S (RAM.mul 661 660 659 678) (Known [(660,((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)])
      (Known [(661,(((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(660,((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (5*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))+4) :=
    mul_known (by decide) (by intro rv h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [rT]) (by simp) (by simp)
  have step5 : HTB S (RAM.mul 662 622 661 678) (Known [(661,(((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(660,((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)])
      (Known [(662,(p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))),(661,(((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(660,((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (5*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))+4) :=
    mul_known (by decide) (by intro rv h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [rT]) (by simp) (by simp)
  have step6 : HTB S (OptPowerRAM.program) (Known [(662,(p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))),(661,(((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(660,((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)])
      (Known [(663,15^(p)),(662,(p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))),(661,(((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(660,((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (100*((p)+1)) :=
    pow_known (by intro rv h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [rT]) (by simp)
  have step7 : HTB S (RAM.mul 664 663 662 678) (Known [(663,15^(p)),(662,(p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))),(661,(((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(660,((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)])
      (Known [(664,(15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))))),(663,15^(p)),(662,(p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))),(661,(((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(660,((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (5*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))))+4) :=
    mul_known (by decide) (by intro rv h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [rT]) (by simp) (by simp)
  have step8 : HTB S (.add 665 655 664) (Known [(664,(15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))))),(663,15^(p)),(662,(p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))),(661,(((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(660,((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)])
      (Known [(665,((((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1)+((15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))))),(664,(15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))))),(663,15^(p)),(662,(p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))),(661,(((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(660,((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (1) :=
    add_known (by intro rv h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [rT]) (by simp) (by simp)
  have step9 : HTB S (RAM.mul 624 656 665 678) (Known [(665,((((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1)+((15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))))),(664,(15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))))),(663,15^(p)),(662,(p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))),(661,(((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(660,((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)])
      (Known [(624,(8*(C+1))*(((((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1)+((15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))))))),(665,((((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1)+((15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))))),(664,(15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))))),(663,15^(p)),(662,(p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))),(661,(((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(660,((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (5*(((((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1)+((15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))))))+4) :=
    mul_known (by decide) (by intro rv h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [rT]) (by simp) (by simp)
  have last : HTB S .skip (Known [(624,(8*(C+1))*(((((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1)+((15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))))))),(665,((((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1)+((15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))))),(664,(15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))))),(663,15^(p)),(662,(p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))),(661,(((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(660,((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) (Known [(624,(8*(C+1))*(((((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1)+((15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))))))),(665,((((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1)+((15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))))),(664,(15^(p))*((p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))))),(663,15^(p)),(662,(p)*((((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))),(661,(((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(660,((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))*((((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t)))),(659,(((p)+1)*(((k)*(t))*(k)))+(((k)*(t))*(t))),(658,((p)+1)*(((k)*(t))*(k))),(657,(p)+1),(656,8*(C+1)),(655,(((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t)))+1),(654,((((k)*(t))*(k))+(((k)*(t))*(t)))+((k)*(t))),(653,(((k)*(t))*(k))+(((k)*(t))*(t))),(652,((k)*(t))*(t)),(651,((k)*(t))*(k)),(650,(k)*(t)),(620,k),(621,t),(622,p)]) 1 :=
    by intro c hc;exact ⟨c,1,.skip c,hc,le_rfl⟩
  exact step0.seq (step1.seq (step2.seq (step3.seq (step4.seq (step5.seq (step6.seq (step7.seq (step8.seq (step9.seq (last))))))))))

def zeroProgram : Stmt := RAM.mul 624 656 655 678

def rawProgram (C : Nat) : Stmt :=
  .seq (baseProgram C) (.ifz 622 zeroProgram (positiveProgram C))

/-- The arithmetic scratch registers are disjoint from the caller's controls. -/
def program (C : Nat) : Stmt :=
  renameRegisters (Equiv.swap 3 679) (rawProgram C)

theorem baseTime_eq (C k t p : Nat) : baseTime C k t p=10*t+5*k+18 := by
  unfold baseTime
  omega

theorem positiveTime_eq (C k t p : Nat) :
    positiveTime C k t p=5*(k*k*t)+10*z k t p+5*(z k t p)^3+
      5*(p*(z k t p)^3)+5*Q k t p+100*(p+1)+29 := by
  unfold positiveTime Q z
  ring

theorem baseTime_le {C k t p : Nat} (hk : 0<k) (ht : 0<t) :
    baseTime C k t p≤15*Q k t p+18 := by
  obtain ⟨hk',ht',_⟩ := base_components_le hk ht p
  rw [baseTime_eq]
  omega

theorem positiveTime_le {C k t p : Nat} (hk : 0<k) (ht : 0<t) (hp : 0<p) :
    positiveTime C k t p≤130*Q k t p+29 := by
  obtain ⟨_,_,_,_,hkt,_,_⟩ := base_components_le hk ht p
  obtain ⟨_,_,hz,hcube,hpc,_,_,hpq⟩ := positive_components_le hk ht hp
  rw [positiveTime_eq]
  omega

theorem positiveValues_output {C k t p : Nat} {c : Config}
    (hc : Known (positiveValues C k t p) c) : c.reg 624=span C k t p := by
  have h := hc (positiveValues C k t p).head! (by simp [positiveValues])
  simp only [positiveValues,List.head!] at h
  change c.reg 624=_ at h
  rw [h]
  unfold span Q z
  ring

theorem rawProgram_spec (S C k t p : Nat) (hk : 0<k) (ht : 0<t) :
    HTB S (rawProgram C) (Known (inputValues k t p))
      (fun c=>c.reg 624=span C k t p) (1000*(span C k t p+1)) := by
  intro c hc
  obtain ⟨d,tb,heb,hb,htb⟩ := base_spec S C k t p c hc
  have hpreg := hb (622,p) (by simp [baseValues])
  change d.reg 622=p at hpreg
  have hbase := baseTime_le (C:=C) (p:=p) hk ht
  have hspan := Q_le_span C k t p
  by_cases hp : p=0
  · cases hp
    have hzero : HTB S zeroProgram (Known (baseValues C k t 0))
        (Known ((624,8*(C+1)*((k*t)*k+(k*t)*t+k*t+1))::baseValues C k t 0))
        (5*((k*t)*k+(k*t)*t+k*t+1)+4) := by
      exact mul_known (by decide)
        (by intro rv h; simp only [baseValues,List.mem_cons,List.mem_nil_iff,or_false] at h
            rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [rT])
        (by simp [baseValues]) (by simp [baseValues])
    obtain ⟨e,tz,hez,hz,htz⟩ := hzero d hb
    have hv := hz _ (List.mem_cons_self ..)
    have hq : (k*t)*k+(k*t)*t+k*t+1=Q k t 0 := by
      simp [Q];ring
    refine ⟨e,tb+(tz+1),.seq heb (.ifzTrue hpreg hez),?_,?_⟩
    · change e.reg 624=_ at hv
      rw [hv,hq]
      rfl
    · rw [hq] at htz
      omega
  · obtain ⟨e,tp,hep,hv,htp⟩ := positive_spec S C k t p d hb
    have hpos := positiveTime_le (C:=C) hk ht (by omega : 0<p)
    have htime : tb+(tp+1)≤1000*(span C k t p+1) := by omega
    exact ⟨e,tb+(tp+1),.seq heb (.ifzFalse (by rw [hpreg];exact hp) hep),
      positiveValues_output hv,htime⟩

theorem program_spec (S C k t p : Nat) (hk : 0<k) (ht : 0<t)
    (c : Config) (hkreg : c.reg 620=k) (htreg : c.reg 621=t) (hpreg : c.reg 622=p) :
    ∃ d time,ExecB S (program C) c time d ∧ d.reg 624=span C k t p ∧
      time≤1000*(span C k t p+1) ∧ d.mem=c.mem ∧ d.out=c.out := by
  have hinput : Known (inputValues k t p) (registerView (Equiv.swap 3 679) c) := by
    intro rv h
    simp only [inputValues,List.mem_cons,List.mem_nil_iff,or_false] at h
    rcases h with rfl | rfl | rfl <;> simpa [registerView,Equiv.swap_apply_def] using ‹_›
  obtain ⟨d,time,he,hd,htime⟩ := rawProgram_spec S C k t p hk ht _ hinput
  obtain ⟨e,hee,hview⟩ := renameRegisters_exec (Equiv.swap 3 679).injective he c rfl
  refine ⟨e,time,hee,?_,htime,?_,?_⟩
  · have hh := congrArg (fun cc : Config=>cc.reg 624) hview
    simpa [registerView,Equiv.swap_apply_def] using hh.trans hd
  · exact hee.mem_frame (by
      simp [renameRegisters_stores,rawProgram,baseProgram,positiveProgram,
        zeroProgram,OptPowerRAM.program,OptPowerRAM.body,RAM.mul,forUp,upLoop,
        addc,inc,stores])
  · exact hee.out_frame (by
      simp [renameRegisters_writes,rawProgram,baseProgram,positiveProgram,
        zeroProgram,OptPowerRAM.program,OptPowerRAM.body,RAM.mul,forUp,upLoop,
        addc,inc,writes])

theorem rawProgram_registers {C r : Nat} (hr : r∈wregs (rawProgram C)) :
    r=3 ∨ r=624 ∨ (650≤r ∧ r≤678) := by
  simp [rawProgram,baseProgram,positiveProgram,zeroProgram,
    OptPowerRAM.program,OptPowerRAM.body,OptPowerRAM.value,OptPowerRAM.temporary,
    OptPowerRAM.counter,RAM.mul,forUp,upLoop,addc,inc,wregs,rT] at hr
  omega

theorem program_registerFrame {S C time : Nat} {c d : Config}
    (he : ExecB S (program C) c time d) {r : Nat}
    (hr : r≠624) (hs : r<650 ∨ 679<r) : d.reg r=c.reg r := by
  apply he.reg_frame
  rw [program,renameRegisters_wregs]
  intro hm
  obtain ⟨a,ha,hphi⟩ := List.mem_map.mp hm
  have hb := rawProgram_registers ha
  rcases hb with hb | hb | hb
  · subst a
    simp at hphi
    omega
  · subst a
    simp [Equiv.swap_apply_def] at hphi
    omega
  · have hne : a≠3 ∧ a≠679 := by omega
    simp [Equiv.swap_apply_def,hne.1,hne.2] at hphi
    omega

end STACS2027.Runtimes.BoundedCost.OptSpanRAM
