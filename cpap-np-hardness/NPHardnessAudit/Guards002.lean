module

import NPHardness

/-!
Exact-message axiom guards for every explicitly named NPHardness declaration.
Each guard fails if its transitive axiom report changes. The generator rejects
axioms outside propext, Classical.choice, and Quot.sound before writing this
file. Regenerate with scripts/generate_audit.py.
-/

set_option maxRecDepth 100000

/-- info: 'STACS2027.PlanarSource.Packed.Index.column_cell_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.column_cell_block

/-- info: 'STACS2027.PlanarSource.Packed.Index.column_start_block' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.column_start_block

/-- info: 'STACS2027.PlanarSource.Packed.Index.column_end_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.column_end_block

/-- info: 'STACS2027.PlanarSource.Packed.Index.BlockAt.getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.BlockAt.getElem?

/-- info: 'STACS2027.PlanarSource.Packed.Index.BlockAt.index_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.BlockAt.index_lt

/-- info: 'STACS2027.PlanarSource.Packed.Index.BlockAt.off_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.BlockAt.off_add

/-- info: 'STACS2027.PlanarSource.Packed.Index.BlockAt.off' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.BlockAt.off

/-- info: 'STACS2027.PlanarSource.Packed.Index.columnBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.columnBase

/-- info: 'STACS2027.PlanarSource.Packed.Index.rainbowBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.rainbowBase

/-- info: 'STACS2027.PlanarSource.Packed.Index.grid_column_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.grid_column_block

/-- info: 'STACS2027.PlanarSource.Packed.Index.grid_rainbow_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.grid_rainbow_block

/-- info: 'STACS2027.PlanarSource.Packed.Index.grid_cell_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.grid_cell_block

/-- info: 'STACS2027.PlanarSource.Packed.Index.grid_start_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.grid_start_block

/-- info: 'STACS2027.PlanarSource.Packed.Index.grid_end_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.grid_end_block

/-- info: 'STACS2027.PlanarSource.Packed.sequence' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.sequence

/-- info: 'STACS2027.PlanarSource.Packed.sequence_emit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.sequence_emit

/-- info: 'STACS2027.PlanarSource.Packed.ringBlock' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.ringBlock

/-- info: 'STACS2027.PlanarSource.Packed.cellPositions' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.cellPositions

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cellProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cellProgram

/-- info: 'STACS2027.PlanarSource.Packed.Layout.startProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.startProgram

/-- info: 'STACS2027.PlanarSource.Packed.Layout.endProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.endProgram

/-- info: 'STACS2027.PlanarSource.Packed.Layout.rainbowProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.rainbowProgram

/-- info: 'STACS2027.PlanarSource.Packed.Layout.columnProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.columnProgram

/-- info: 'STACS2027.PlanarSource.Packed.Layout.gridPhase' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.gridPhase

/-- info: 'STACS2027.PlanarSource.Packed.Layout.program' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.program

/-- info: 'STACS2027.PlanarSource.Packed.halfGuard' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.halfGuard

/-- info: 'STACS2027.PlanarSource.Packed.gridProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.gridProgram

/-- info: 'STACS2027.PlanarSource.Packed.halfGuard_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.halfGuard_eval

/-- info: 'STACS2027.PlanarSource.Packed.gridProgram_emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.gridProgram_emit

/-- info: 'STACS2027.PlanarSource.Packed.cellProgram_copies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.cellProgram_copies

/-- info: 'STACS2027.PlanarSource.Packed.gridBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.gridBody

/-- info: 'STACS2027.PlanarSource.Packed.sourceProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.sourceProgram

/-- info: 'STACS2027.PlanarSource.Packed.output' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.output

/-- info: 'STACS2027.PlanarSource.Packed.output_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.output_polyTime

/-- info: 'STACS2027.PlanarSource.Packed.output_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.output_eq

/-- info: 'STACS2027.PlanarSource.Packed.incidenceNext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.incidenceNext

/-- info: 'STACS2027.PlanarSource.Packed.ringEdge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.ringEdge

/-- info: 'STACS2027.PlanarSource.Packed.successorProgram_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.successorProgram_source

/-- info: 'STACS2027.PlanarSource.Packed.Layout.source_lift' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.source_lift

/-- info: 'STACS2027.PlanarSource.Packed.Layout.startProgram_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.startProgram_correct

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cellProgram_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cellProgram_correct

/-- info: 'STACS2027.PlanarSource.Packed.Layout.endProgram_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.endProgram_correct

/-- info: 'STACS2027.PlanarSource.Packed.rainbowEndpoint_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.rainbowEndpoint_eq

/-- info: 'STACS2027.PlanarSource.Packed.Layout.rainbowProgram_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.rainbowProgram_correct

/-- info: 'STACS2027.PlanarSource.Packed.Layout.ringBlocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.ringBlocks

/-- info: 'STACS2027.PlanarSource.Packed.Layout.program_ringFormula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.program_ringFormula

/-- info: 'STACS2027.PlanarSource.Packed.expandCopies' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.expandCopies

/-- info: 'STACS2027.PlanarSource.Packed.expandCopies_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.expandCopies_append

/-- info: 'STACS2027.PlanarSource.Packed.expandCopies_flatMap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.expandCopies_flatMap

/-- info: 'STACS2027.PlanarSource.Packed.expandCopies_copiesAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.expandCopies_copiesAt

/-- info: 'STACS2027.PlanarSource.Packed.ringBlock_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.ringBlock_exact

/-- info: 'STACS2027.PlanarSource.Packed.ringBlock_copies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.ringBlock_copies

/-- info: 'STACS2027.PlanarSource.Packed.cellPositions_length' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.cellPositions_length

/-- info: 'STACS2027.PlanarSource.Packed.cellOccurrences_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.cellOccurrences_length

/-- info: 'STACS2027.PlanarSource.Packed.startOccurrences_length' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.startOccurrences_length

/-- info: 'STACS2027.PlanarSource.Packed.endOccurrences_length' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.endOccurrences_length

/-- info: 'STACS2027.PlanarSource.Packed.rainbowOccurrences_length' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.rainbowOccurrences_length

/-- info: 'STACS2027.PlanarSource.Packed.RingBlocks' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.RingBlocks

/-- info: 'STACS2027.PlanarSource.Packed.RingBlocks.column' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.RingBlocks.column

/-- info: 'STACS2027.PlanarSource.Packed.RingBlocks.row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.RingBlocks.row

/-- info: 'STACS2027.PlanarSource.Packed.gridPhase_rings' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.gridPhase_rings

/-- info: 'STACS2027.PlanarSource.Packed.program_eq_ringFormula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.program_eq_ringFormula

/-- info: 'STACS2027.PlanarSource.Packed.copiesAt_tagSource' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copiesAt_tagSource

/-- info: 'STACS2027.PlanarSource.Packed.copiesAt_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copiesAt_zero

/-- info: 'STACS2027.PlanarSource.Packed.copiesAt_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copiesAt_append

/-- info: 'STACS2027.PlanarSource.Packed.copiesAt_reverse_blocks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copiesAt_reverse_blocks

/-- info: 'STACS2027.PlanarSource.Packed.nodup_eq_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.nodup_eq_singleton

/-- info: 'STACS2027.PlanarSource.Packed.successorProgram_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.successorProgram_exact

/-- info: 'STACS2027.PlanarSource.Packed.Layout.bits' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.bits

/-- info: 'STACS2027.PlanarSource.Packed.Layout.source' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.source

/-- info: 'STACS2027.PlanarSource.Packed.DescriptorSound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.DescriptorSound

/-- info: 'STACS2027.PlanarSource.Packed.DescriptorSound.sign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.DescriptorSound.sign

/-- info: 'STACS2027.PlanarSource.Packed.SoundList' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.SoundList

/-- info: 'STACS2027.PlanarSource.Packed.SoundList.append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.SoundList.append

/-- info: 'STACS2027.PlanarSource.Packed.SoundList.gate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.SoundList.gate

/-- info: 'STACS2027.PlanarSource.Packed.blockOccurrences_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.blockOccurrences_live

/-- info: 'STACS2027.PlanarSource.Packed.blockOccurrences_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.blockOccurrences_sound

/-- info: 'STACS2027.PlanarSource.Packed.Layout.variableCount_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.variableCount_source

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cellTemplates_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cellTemplates_source

/-- info: 'STACS2027.PlanarSource.Packed.bool_cases_eq' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.bool_cases_eq

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cellOccurrences_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cellOccurrences_sound

/-- info: 'STACS2027.PlanarSource.Packed.Layout.startOccurrences_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.startOccurrences_sound

/-- info: 'STACS2027.PlanarSource.Packed.Layout.endOccurrences_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.endOccurrences_sound

/-- info: 'STACS2027.PlanarSource.Packed.Layout.rainbowOccurrences_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.rainbowOccurrences_sound

/-- info: 'STACS2027.PlanarSource.Packed.Layout.chainCandidates_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.chainCandidates_sound

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cellCandidates_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cellCandidates_sound

/-- info: 'STACS2027.PlanarSource.Packed.Layout.startCandidates_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.startCandidates_sound

/-- info: 'STACS2027.PlanarSource.Packed.Layout.endCandidates_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.endCandidates_sound

/-- info: 'STACS2027.PlanarSource.Packed.Layout.rainbowCandidates_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.rainbowCandidates_sound

/-- info: 'STACS2027.PlanarSource.Packed.Entry' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Entry

/-- info: 'STACS2027.PlanarSource.Packed.Occurrence' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Occurrence

/-- info: 'STACS2027.PlanarSource.Packed.Occurrence.eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Occurrence.eval

/-- info: 'STACS2027.PlanarSource.Packed.Before' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Before

/-- info: 'STACS2027.PlanarSource.Packed.Active' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Active

/-- info: 'STACS2027.PlanarSource.Packed.NextIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.NextIn

/-- info: 'STACS2027.PlanarSource.Packed.beforeTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.beforeTest

/-- info: 'STACS2027.PlanarSource.Packed.activeTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.activeTest

/-- info: 'STACS2027.PlanarSource.Packed.beforeTest_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.beforeTest_eval

/-- info: 'STACS2027.PlanarSource.Packed.activeTest_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.activeTest_eval

/-- info: 'STACS2027.PlanarSource.Packed.successorTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.successorTest

/-- info: 'STACS2027.PlanarSource.Packed.successorTest_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.successorTest_eval

/-- info: 'STACS2027.PlanarSource.Packed.successorProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.successorProgram

/-- info: 'STACS2027.PlanarSource.Packed.successorProgram_emit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.successorProgram_emit

/-- info: 'STACS2027.PlanarSource.Packed.Test' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Test

/-- info: 'STACS2027.PlanarSource.Packed.Test.eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Test.eval

/-- info: 'STACS2027.PlanarSource.Packed.Test.select' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Test.select

/-- info: 'STACS2027.PlanarSource.Packed.Test.select_emit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Test.select_emit

/-- info: 'STACS2027.PlanarSource.Packed.Test.eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Test.eq

/-- info: 'STACS2027.PlanarSource.Packed.Test.lt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Test.lt

/-- info: 'STACS2027.PlanarSource.Packed.Test.eval_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Test.eval_eq

/-- info: 'STACS2027.PlanarSource.Packed.Test.eval_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Test.eval_lt

/-- info: 'STACS2027.PlanarSource.Packed.Test.all' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Test.all

/-- info: 'STACS2027.PlanarSource.Packed.Test.eval_all' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Test.eval_all

/-- info: 'STACS2027.PlanarSource.Packed.pairProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.pairProgram

/-- info: 'STACS2027.PlanarSource.Packed.pairProgram_emit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.pairProgram_emit

/-- info: 'STACS2027.PlanarSource.Formula.placedRingDarts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.placedRingDarts

/-- info: 'STACS2027.PlanarSource.Formula.placedRingDarts_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.placedRingDarts_val

/-- info: 'STACS2027.PlanarSource.Formula.placedRingMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.placedRingMap

/-- info: 'STACS2027.PlanarSource.Formula.placedRingMap_predecessor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.placedRingMap_predecessor

/-- info: 'STACS2027.PlanarSource.Formula.placedRingMap_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.placedRingMap_edge

/-- info: 'STACS2027.PlanarSource.Formula.placedRingMap_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.placedRingMap_nodes

/-- info: 'STACS2027.PlanarSource.Formula.placedRingMap_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.placedRingMap_planar

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_placed_flatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_placed_flatten

/-- info: 'STACS2027.PlanarSource.Formula.copyFormula_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copyFormula_get

/-- info: 'STACS2027.PlanarSource.Formula.ringClauses_get_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringClauses_get_first

/-- info: 'STACS2027.PlanarSource.Formula.ringClauses_get_second' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringClauses_get_second

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_placed_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_placed_copy

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_placed_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_placed_first

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_placed_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_placed_second

/-- info: 'STACS2027.PlanarSource.placeLiterals_counts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.placeLiterals_counts

/-- info: 'STACS2027.PlanarSource.placeFormula_counts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.placeFormula_counts

/-- info: 'STACS2027.PlanarSource.Formula.copyFormula_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copyFormula_count

/-- info: 'STACS2027.PlanarSource.Formula.copyFormula_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copyFormula_nodup

/-- info: 'STACS2027.PlanarSource.Formula.copyFormula_placement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copyFormula_placement

/-- info: 'STACS2027.PlanarSource.Formula.ringClauses_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringClauses_nodup

/-- info: 'STACS2027.PlanarSource.Formula.ringClauses_variable_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringClauses_variable_lt

/-- info: 'STACS2027.PlanarSource.Formula.ringClauses_placement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringClauses_placement

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_placement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_placement

/-- info: 'STACS2027.PlanarSource.variableRoleDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.variableRoleDart

/-- info: 'STACS2027.PlanarSource.clauseRoleDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.clauseRoleDart

/-- info: 'STACS2027.PlanarSource.variableRoleDart_predecessor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.variableRoleDart_predecessor

/-- info: 'STACS2027.PlanarSource.clauseRoleDart_predecessor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.clauseRoleDart_predecessor

/-- info: 'STACS2027.PlanarSource.copiedClause_predecessor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.copiedClause_predecessor

/-- info: 'STACS2027.PlanarSource.variableRolePort' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.variableRolePort

/-- info: 'STACS2027.PlanarSource.reflectedVariableNext' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.reflectedVariableNext

/-- info: 'STACS2027.PlanarSource.variableRolePort_predecessor' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.variableRolePort_predecessor

/-- info: 'STACS2027.PlanarSource.rolePlacedLiteral' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.rolePlacedLiteral

/-- info: 'STACS2027.PlanarSource.rolePlacedLiteral_port' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.rolePlacedLiteral_port

/-- info: 'STACS2027.PlanarSource.Formula.copyFormula_clause_lengths' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copyFormula_clause_lengths

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_clause_lengths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_clause_lengths

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_off_copy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_off_copy

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_kl_copy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_kl_copy

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_off_ring' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_off_ring

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_kl_ring' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_kl_ring

/-- info: 'STACS2027.PlanarSource.Formula.ringDartValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringDartValue

/-- info: 'STACS2027.PlanarSource.Formula.expandedDartValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.expandedDartValue

/-- info: 'STACS2027.PlanarSource.Formula.ringDartValue_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringDartValue_lt

/-- info: 'STACS2027.PlanarSource.Formula.expandedDartValue_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.expandedDartValue_lt

/-- info: 'STACS2027.PlanarSource.Formula.expanded_ringDartValue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.expanded_ringDartValue

/-- info: 'STACS2027.PlanarSource.Formula.ring_expandedDartValue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ring_expandedDartValue

/-- info: 'STACS2027.PlanarSource.Formula.ringDarts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringDarts

/-- info: 'STACS2027.PlanarSource.Formula.ringDarts_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringDarts_zero

/-- info: 'STACS2027.PlanarSource.Formula.ringDarts_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringDarts_one

/-- info: 'STACS2027.PlanarSource.Formula.ringDarts_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringDarts_two

/-- info: 'STACS2027.PlanarSource.Formula.ringDarts_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringDarts_three

/-- info: 'STACS2027.PlanarSource.Formula.ringDarts_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringDarts_four

/-- info: 'STACS2027.PlanarSource.Formula.ringDarts_five' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringDarts_five

/-- info: 'STACS2027.PlanarSource.Formula.ringDarts_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringDarts_edge

/-- info: 'STACS2027.PlanarSource.Formula.implicationEdges_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.implicationEdges_succ

/-- info: 'STACS2027.PlanarSource.Formula.implicationEdges_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.implicationEdges_length

/-- info: 'STACS2027.PlanarSource.Formula.implicationEdges_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.implicationEdges_get

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_incidence_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_incidence_get

/-- info: 'STACS2027.PlanarSource.Formula.ringFormulaDarts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormulaDarts

/-- info: 'STACS2027.PlanarSource.Formula.ringFormulaDarts_val_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormulaDarts_val_eq

/-- info: 'STACS2027.PlanarSource.Formula.ringFormulaDarts_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormulaDarts_ends

/-- info: 'STACS2027.PlanarSource.RotationTable.NextIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.NextIn

/-- info: 'STACS2027.PlanarSource.RotationTable.nextIn_congr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.nextIn_congr

/-- info: 'STACS2027.PlanarSource.RotationTable.sorted_index_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.sorted_index_iff

/-- info: 'STACS2027.PlanarSource.RotationTable.nextIn_indices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.nextIn_indices

/-- info: 'STACS2027.PlanarSource.RotationTable.nextIn_iff_rnext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.nextIn_iff_rnext

/-- info: 'STACS2027.PlanarSource.RotationTable.Before' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.Before

/-- info: 'STACS2027.PlanarSource.RotationTable.before_irrefl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.before_irrefl

/-- info: 'STACS2027.PlanarSource.RotationTable.before_asymm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.before_asymm

/-- info: 'STACS2027.PlanarSource.RotationTable.incidenceOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.incidenceOrder

/-- info: 'STACS2027.PlanarSource.RotationTable.incidenceOrder_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.incidenceOrder_sorted

/-- info: 'STACS2027.PlanarSource.RotationTable.incidenceOrder_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.incidenceOrder_nodup

/-- info: 'STACS2027.PlanarSource.RotationTable.incidence_next_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.incidence_next_iff

/-- info: 'STACS2027.PlanarSource.RotationTable.mem_incidenceOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.mem_incidenceOrder

/-- info: 'STACS2027.PlanarSource.RotationTable.variable_next_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.variable_next_iff

/-- info: 'STACS2027.PlanarSource.RotationTable.nM_eq_flatten' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.nM_eq_flatten

/-- info: 'STACS2027.PlanarSource.RotationTable.indexed_literal_variable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.indexed_literal_variable

/-- info: 'STACS2027.PlanarSource.RotationTable.occurrence_at' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.occurrence_at

/-- info: 'STACS2027.PlanarSource.RotationTable.activeIndices_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.activeIndices_complete

/-- info: 'STACS2027.PlanarSource.RotationTable.activeIndices_nodup_of_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.activeIndices_nodup_of_projection

/-- info: 'STACS2027.PlanarSource.RotationTable.blockOccurrences_correct_of_blockAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.blockOccurrences_correct_of_blockAt

/-- info: 'STACS2027.PlanarSource.RotationTable.blockAt_occurrence_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.blockAt_occurrence_mem

/-- info: 'STACS2027.PlanarSource.RotationTable.blockOccurrences_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.blockOccurrences_source

/-- info: 'STACS2027.PlanarSource.RotationTable.sourceOccurrence_sign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.sourceOccurrence_sign

/-- info: 'STACS2027.PlanarSource.RotationTable.liveProjection' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.liveProjection

/-- info: 'STACS2027.PlanarSource.RotationTable.liveProjection_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.liveProjection_append

/-- info: 'STACS2027.PlanarSource.RotationTable.templateOccurrences_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.templateOccurrences_live

/-- info: 'STACS2027.PlanarSource.RotationTable.blockOccurrences_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.blockOccurrences_live

/-- info: 'STACS2027.PlanarSource.RotationTable.blockOccurrences_liveProjection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.blockOccurrences_liveProjection

/-- info: 'STACS2027.PlanarSource.RotationTable.liveProjection_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.liveProjection_gate

/-- info: 'STACS2027.PlanarSource.RotationTable.layoutBits' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.layoutBits

/-- info: 'STACS2027.PlanarSource.RotationTable.layoutCellTemplates_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.layoutCellTemplates_eval

/-- info: 'STACS2027.PlanarSource.RotationTable.cell_liveProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cell_liveProjection

/-- info: 'STACS2027.PlanarSource.RotationTable.start_liveProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.start_liveProjection

/-- info: 'STACS2027.PlanarSource.RotationTable.end_liveProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.end_liveProjection

/-- info: 'STACS2027.PlanarSource.RotationTable.rainbow_liveProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.rainbow_liveProjection

/-- info: 'STACS2027.PlanarSource.RotationTable.CompleteCandidates' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.CompleteCandidates

/-- info: 'STACS2027.PlanarSource.RotationTable.complete_of_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.complete_of_projection

/-- info: 'STACS2027.PlanarSource.RotationTable.cellCandidates_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cellCandidates_complete

/-- info: 'STACS2027.PlanarSource.RotationTable.startCandidates_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.startCandidates_complete

/-- info: 'STACS2027.PlanarSource.RotationTable.endCandidates_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.endCandidates_complete

/-- info: 'STACS2027.PlanarSource.RotationTable.rainbowCandidates_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.rainbowCandidates_complete

/-- info: 'STACS2027.PlanarSource.RotationTable.blockTags' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.blockTags

/-- info: 'STACS2027.PlanarSource.RotationTable.neighborhoodTags' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.neighborhoodTags

/-- info: 'STACS2027.PlanarSource.RotationTable.mem_neighborhoodTags' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.mem_neighborhoodTags

/-- info: 'STACS2027.PlanarSource.RotationTable.block_indices_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.block_indices_disjoint

/-- info: 'STACS2027.PlanarSource.RotationTable.neighborhoodTags_indices_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.neighborhoodTags_indices_nodup

/-- info: 'STACS2027.PlanarSource.RotationTable.neighborhoodTags_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.neighborhoodTags_source

/-- info: 'STACS2027.PlanarSource.RotationTable.neighborhoodTags_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.neighborhoodTags_complete

/-- info: 'STACS2027.PlanarSource.RotationTable.activeIndices_projection' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.activeIndices_projection

/-- info: 'STACS2027.PlanarSource.RotationTable.orientExpr_eval' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.orientExpr_eval

/-- info: 'STACS2027.PlanarSource.RotationTable.template_clause_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.template_clause_length

/-- info: 'STACS2027.PlanarSource.RotationTable.template_variable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.template_variable

/-- info: 'STACS2027.PlanarSource.RotationTable.template_lo' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.template_lo

/-- info: 'STACS2027.PlanarSource.RotationTable.template_hi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.template_hi

/-- info: 'STACS2027.PlanarSource.RotationTable.keyExpr_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.keyExpr_correct

/-- info: 'STACS2027.PlanarSource.RotationTable.templateOccurrences_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.templateOccurrences_correct

/-- info: 'STACS2027.PlanarSource.RotationTable.blockOccurrences_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.blockOccurrences_correct

/-- info: 'STACS2027.PlanarSource.RotationTable.entryOccurrence' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.entryOccurrence

/-- info: 'STACS2027.PlanarSource.RotationTable.templateOccurrences_enumerate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.templateOccurrences_enumerate

/-- info: 'STACS2027.PlanarSource.RotationTable.blockOccurrences_enumerate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.blockOccurrences_enumerate

/-- info: 'STACS2027.PlanarSource.RotationTable.blockOccurrences_indices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.blockOccurrences_indices

/-- info: 'STACS2027.PlanarSource.RotationTable.cellPositions' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cellPositions

/-- info: 'STACS2027.PlanarSource.RotationTable.cellPositions_length' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cellPositions_length

/-- info: 'STACS2027.PlanarSource.RotationTable.cellPositions_lt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cellPositions_lt

/-- info: 'STACS2027.PlanarSource.RotationTable.cell_variables' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cell_variables

/-- info: 'STACS2027.PlanarSource.RotationTable.column_position_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.column_position_eq

/-- info: 'STACS2027.PlanarSource.RotationTable.cell_position_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cell_position_eq

/-- info: 'STACS2027.PlanarSource.RotationTable.cell_interior_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cell_interior_eq

/-- info: 'STACS2027.PlanarSource.RotationTable.cell_chain_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cell_chain_eq

/-- info: 'STACS2027.PlanarSource.RotationTable.cell_position_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cell_position_lt

/-- info: 'STACS2027.PlanarSource.RotationTable.cell_columns_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cell_columns_eq

/-- info: 'STACS2027.PlanarSource.RotationTable.cell_interior_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cell_interior_unique

/-- info: 'STACS2027.PlanarSource.RotationTable.cell_literal_position' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cell_literal_position

/-- info: 'STACS2027.PlanarSource.RotationTable.start_literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.start_literal

/-- info: 'STACS2027.PlanarSource.RotationTable.end_literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.end_literal

/-- info: 'STACS2027.PlanarSource.RotationTable.rainbowEven_literal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.rainbowEven_literal

/-- info: 'STACS2027.PlanarSource.RotationTable.rainbowOdd_literal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.rainbowOdd_literal

/-- info: 'STACS2027.PlanarSource.RotationTable.rainbowEven_incident' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.rainbowEven_incident

/-- info: 'STACS2027.PlanarSource.RotationTable.rainbowOdd_incident' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.rainbowOdd_incident

/-- info: 'STACS2027.PlanarSource.RotationTable.cell_interior_not_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cell_interior_not_start

/-- info: 'STACS2027.PlanarSource.RotationTable.cell_interior_not_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cell_interior_not_end

/-- info: 'STACS2027.PlanarSource.RotationTable.chain_not_rainbow_endpoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.chain_not_rainbow_endpoint

/-- info: 'STACS2027.PlanarSource.RotationTable.chain_not_rainbowEven' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.chain_not_rainbowEven

/-- info: 'STACS2027.PlanarSource.RotationTable.chain_not_rainbowOdd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.chain_not_rainbowOdd

/-- info: 'STACS2027.PlanarSource.RotationTable.chain_start_incident' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.chain_start_incident

/-- info: 'STACS2027.PlanarSource.RotationTable.chain_end_incident' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.chain_end_incident

/-- info: 'STACS2027.PlanarSource.RotationTable.GridBlock' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.GridBlock

/-- info: 'STACS2027.PlanarSource.RotationTable.columnIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.columnIndex

/-- info: 'STACS2027.PlanarSource.RotationTable.GridBlock.Valid' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.GridBlock.Valid

/-- info: 'STACS2027.PlanarSource.RotationTable.GridBlock.formula' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.GridBlock.formula

/-- info: 'STACS2027.PlanarSource.RotationTable.interiorNeighborhood' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.interiorNeighborhood

/-- info: 'STACS2027.PlanarSource.RotationTable.columnIndex_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.columnIndex_injective

/-- info: 'STACS2027.PlanarSource.RotationTable.interiorNeighborhood_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.interiorNeighborhood_complete

/-- info: 'STACS2027.PlanarSource.RotationTable.chainNeighborhood' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.chainNeighborhood

/-- info: 'STACS2027.PlanarSource.RotationTable.chainNeighborhood_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.chainNeighborhood_complete

/-- info: 'STACS2027.PlanarSource.RotationTable.startAux_ne_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.startAux_ne_cell

/-- info: 'STACS2027.PlanarSource.RotationTable.endAux_ne_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.endAux_ne_cell

/-- info: 'STACS2027.PlanarSource.RotationTable.startNeighborhood_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.startNeighborhood_complete

/-- info: 'STACS2027.PlanarSource.RotationTable.endNeighborhood_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.endNeighborhood_complete

/-- info: 'STACS2027.PlanarSource.RotationTable.cellNeighborhood' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cellNeighborhood

/-- info: 'STACS2027.PlanarSource.RotationTable.startNeighborhood' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.startNeighborhood

/-- info: 'STACS2027.PlanarSource.RotationTable.endNeighborhood' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.endNeighborhood

/-- info: 'STACS2027.PlanarSource.RotationTable.rainbowNeighborhood' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.rainbowNeighborhood

/-- info: 'STACS2027.PlanarSource.RotationTable.cellNeighborhood_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cellNeighborhood_complete

/-- info: 'STACS2027.PlanarSource.RotationTable.startNeighborhood_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.startNeighborhood_cover

/-- info: 'STACS2027.PlanarSource.RotationTable.endNeighborhood_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.endNeighborhood_cover

/-- info: 'STACS2027.PlanarSource.RotationTable.interiorNeighborhood_nodup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.interiorNeighborhood_nodup

/-- info: 'STACS2027.PlanarSource.RotationTable.chainNeighborhood_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.chainNeighborhood_nodup

/-- info: 'STACS2027.PlanarSource.RotationTable.cellNeighborhood_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cellNeighborhood_nodup

/-- info: 'STACS2027.PlanarSource.RotationTable.startNeighborhood_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.startNeighborhood_nodup

/-- info: 'STACS2027.PlanarSource.RotationTable.endNeighborhood_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.endNeighborhood_nodup

/-- info: 'STACS2027.PlanarSource.RotationTable.rainbowNeighborhood_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.rainbowNeighborhood_nodup

/-- info: 'STACS2027.PlanarSource.RotationTable.rainbowVariable' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.rainbowVariable

/-- info: 'STACS2027.PlanarSource.RotationTable.rainbowNeighborhood_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.rainbowNeighborhood_cover

/-- info: 'STACS2027.PlanarSource.RotationTable.EntryCorrect' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.EntryCorrect

/-- info: 'STACS2027.PlanarSource.RotationTable.activeIndices' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.activeIndices

/-- info: 'STACS2027.PlanarSource.RotationTable.mem_activeIndices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.mem_activeIndices

/-- info: 'STACS2027.PlanarSource.RotationTable.before_entries' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.before_entries

/-- info: 'STACS2027.PlanarSource.RotationTable.nextIn_entries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.nextIn_entries

/-- info: 'STACS2027.PlanarSource.RotationTable.successorTest_iff_registered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.successorTest_iff_registered

/-- info: 'STACS2027.PlanarSource.RotationTable.cellTemplates_page' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cellTemplates_page

/-- info: 'STACS2027.PlanarSource.RotationTable.startTemplates_page' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.startTemplates_page

/-- info: 'STACS2027.PlanarSource.RotationTable.endTemplates_page' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.endTemplates_page

/-- info: 'STACS2027.PlanarSource.RotationTable.rainbowTemplates_page' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.rainbowTemplates_page

/-- info: 'STACS2027.PlanarSource.RotationTable.template_source_page' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.template_source_page

/-- info: 'STACS2027.PlanarSource.RotationTable.columnBlocks' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.columnBlocks

/-- info: 'STACS2027.PlanarSource.RotationTable.blocksByHalf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.blocksByHalf

/-- info: 'STACS2027.PlanarSource.RotationTable.globalBlocks' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.globalBlocks

/-- info: 'STACS2027.PlanarSource.RotationTable.GridBlock.address' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.GridBlock.address

/-- info: 'STACS2027.PlanarSource.RotationTable.half_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.half_eq

/-- info: 'STACS2027.PlanarSource.RotationTable.globalBlocks_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.globalBlocks_eq

/-- info: 'STACS2027.PlanarSource.RotationTable.blocksByHalf_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.blocksByHalf_mem

/-- info: 'STACS2027.PlanarSource.RotationTable.globalBlocks_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.globalBlocks_mem

/-- info: 'STACS2027.PlanarSource.RotationTable.GridBlock.blockAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.GridBlock.blockAt

/-- info: 'STACS2027.PlanarSource.RotationTable.zipIdx_reverse_blocks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.zipIdx_reverse_blocks

/-- info: 'STACS2027.PlanarSource.RotationTable.flatten_flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.flatten_flatMap

/-- info: 'STACS2027.PlanarSource.RotationTable.columnBlocks_partition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.columnBlocks_partition

/-- info: 'STACS2027.PlanarSource.RotationTable.rainbowBlocks_partition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.rainbowBlocks_partition

/-- info: 'STACS2027.PlanarSource.RotationTable.blocksByHalf_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.blocksByHalf_partition

/-- info: 'STACS2027.PlanarSource.RotationTable.globalBlocks_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.globalBlocks_partition

/-- info: 'STACS2027.PlanarSource.RotationTable.globalBlocks_indices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.globalBlocks_indices

/-- info: 'STACS2027.PlanarSource.RotationTable.globalBlocks_indices_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.globalBlocks_indices_nodup

/-- info: 'STACS2027.PlanarSource.RotationTable.globalBlocks_occurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.globalBlocks_occurrence

/-- info: 'STACS2027.PlanarSource.RotationTable.start_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.start_projection

/-- info: 'STACS2027.PlanarSource.RotationTable.end_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.end_projection

/-- info: 'STACS2027.PlanarSource.RotationTable.cell_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cell_projection

/-- info: 'STACS2027.PlanarSource.RotationTable.rainbow_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.rainbow_projection

/-- info: 'STACS2027.PlanarSource.RotationTable.chain_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.chain_projection

/-- info: 'STACS2027.PlanarSource.RotationTable.cellCandidates_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.cellCandidates_projection

/-- info: 'STACS2027.PlanarSource.RotationTable.startCandidates_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.startCandidates_projection

/-- info: 'STACS2027.PlanarSource.RotationTable.endCandidates_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.endCandidates_projection

/-- info: 'STACS2027.PlanarSource.RotationTable.rainbowCandidates_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.rainbowCandidates_projection

/-- info: 'STACS2027.PlanarSource.Formula.ringFormulaGraph_planar_of_odd_predecessor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormulaGraph_planar_of_odd_predecessor

/-- info: 'STACS2027.PlanarSource.Formula.ringOccurrence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringOccurrence

/-- info: 'STACS2027.PlanarSource.Formula.ringOccurrence_eq_of_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringOccurrence_eq_of_get

/-- info: 'STACS2027.PlanarSource.Formula.variableRole_occurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.variableRole_occurrence

/-- info: 'STACS2027.PlanarSource.Formula.variableRole_even' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.variableRole_even

/-- info: 'STACS2027.PlanarSource.Formula.variableRole_vertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.variableRole_vertex

/-- info: 'STACS2027.PlanarSource.Formula.reflectedVariableNext_eq_signed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.reflectedVariableNext_eq_signed

/-- info: 'STACS2027.PlanarSource.Formula.variableRole_portNumber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.variableRole_portNumber

/-- info: 'STACS2027.PlanarSource.Formula.variableRole_port_predecessor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.variableRole_port_predecessor

/-- info: 'STACS2027.PlanarSource.Formula.even_expanded_role' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.even_expanded_role

/-- info: 'STACS2027.PlanarSource.Formula.placedRingMap_even_predecessor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.placedRingMap_even_predecessor

/-- info: 'STACS2027.HasSphericalCofacialPorts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HasSphericalCofacialPorts

/-- info: 'STACS2027.HasSphericalCofacialPorts.cofacial' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HasSphericalCofacialPorts.cofacial

/-- info: 'STACS2027.HasSphericalCofacialPorts.mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HasSphericalCofacialPorts.mem

/-- info: 'STACS2027.HasSphericalCofacialPorts.perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HasSphericalCofacialPorts.perm

/-- info: 'STACS2027.PlanarOperations.Ports.splitMap_spherical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Ports.splitMap_spherical

/-- info: 'STACS2027.PlanarOperations.Ports.spherical_cofacial_subdivide' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Ports.spherical_cofacial_subdivide

/-- info: 'STACS2027.sphericalCofacialPorts_of_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sphericalCofacialPorts_of_tables

/-- info: 'STACS2027.spherical_subdivideOnce_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.spherical_subdivideOnce_bounded

/-- info: 'STACS2027.spherical_chainSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.spherical_chainSteps

/-- info: 'STACS2027.spherical_linkSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.spherical_linkSteps

/-- info: 'STACS2027.spherical_realizeLinks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.spherical_realizeLinks

/-- info: 'STACS2027.variable_skeleton_sphericalPorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_skeleton_sphericalPorts

/-- info: 'STACS2027.clauseThree_skeleton_sphericalPorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_skeleton_sphericalPorts

/-- info: 'STACS2027.clauseTwo_skeleton_sphericalPorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_skeleton_sphericalPorts

/-- info: 'STACS2027.variableGraph_sphericalPorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableGraph_sphericalPorts

/-- info: 'STACS2027.clauseThreeGraph_sphericalPorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeGraph_sphericalPorts

/-- info: 'STACS2027.clauseTwoGraph_sphericalPorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoGraph_sphericalPorts

/-- info: 'STACS2027.PlanarSource.Packed.graphOutput_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.graphOutput_planar

/-- info: 'STACS2027.PlanarSource.Packed.graphOutput_planar_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.graphOutput_planar_iff

/-- info: 'STACS2027.planarCPAP_np_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planarCPAP_np_hard

/-- info: 'STACS2027.tautological' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.tautological

/-- info: 'STACS2027.removeTautologies' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.removeTautologies

/-- info: 'STACS2027.tautological_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.tautological_eval

/-- info: 'STACS2027.removeTautologies_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.removeTautologies_eval

/-- info: 'STACS2027.CounterMemory' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.CounterMemory

/-- info: 'STACS2027.incrementCounter' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.incrementCounter

/-- info: 'STACS2027.historyMemory' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.historyMemory

/-- info: 'STACS2027.allocateLiterals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.allocateLiterals

/-- info: 'STACS2027.allocateFormula' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.allocateFormula

/-- info: 'STACS2027.increment_history' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.increment_history

/-- info: 'STACS2027.allocateLiterals_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.allocateLiterals_refines

/-- info: 'STACS2027.allocateFormula_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.allocateFormula_refines

/-- info: 'STACS2027.allocateLiterals_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.allocateLiterals_length

/-- info: 'STACS2027.occurrences_registered_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.occurrences_registered_positive

/-- info: 'STACS2027.occurrences_registered_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.occurrences_registered_negative

/-- info: 'STACS2027.boundedOccurrence_iff_registered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.boundedOccurrence_iff_registered

/-- info: 'STACS2027.variableEmbedding' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.variableEmbedding

/-- info: 'STACS2027.variableEmbedding_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.variableEmbedding_valid

/-- info: 'STACS2027.variableEmbedding_ends' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.variableEmbedding_ends

/-- info: 'STACS2027.variable_skeleton_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_skeleton_planar

/-- info: 'STACS2027.variable_skeleton_ports_cofacial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_skeleton_ports_cofacial

/-- info: 'STACS2027.clauseThreeEmbedding' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeEmbedding

/-- info: 'STACS2027.clauseThreeEmbedding_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeEmbedding_valid

/-- info: 'STACS2027.clauseThreeEmbedding_ends' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeEmbedding_ends

/-- info: 'STACS2027.clauseThree_skeleton_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_skeleton_planar

/-- info: 'STACS2027.clauseThree_skeleton_ports_cofacial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_skeleton_ports_cofacial

/-- info: 'STACS2027.clauseTwoEmbedding' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoEmbedding

/-- info: 'STACS2027.clauseTwoEmbedding_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoEmbedding_valid

/-- info: 'STACS2027.clauseTwoEmbedding_ends' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoEmbedding_ends

/-- info: 'STACS2027.clauseTwo_skeleton_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_skeleton_planar

/-- info: 'STACS2027.clauseTwo_skeleton_ports_cofacial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_skeleton_ports_cofacial

/-- info: 'STACS2027.edge_left_endpoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_left_endpoint

/-- info: 'STACS2027.edge_endpoints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_endpoints

/-- info: 'STACS2027.pathEdges_endpoints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_endpoints

/-- info: 'STACS2027.pathEdges_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_nodup

/-- info: 'STACS2027.selected_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.selected_nodup

/-- info: 'STACS2027.pathEdges_split' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_split

/-- info: 'STACS2027.cycleEdges_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.cycleEdges_append

/-- info: 'STACS2027.cycleEdges_append_swap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.cycleEdges_append_swap

/-- info: 'STACS2027.selected_mem_cycleEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.selected_mem_cycleEdges

/-- info: 'STACS2027.selected_mem_graph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.selected_mem_graph

/-- info: 'STACS2027.validChoices_properties' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.validChoices_properties

/-- info: 'STACS2027.enumerated_choices_properties' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.enumerated_choices_properties

/-- info: 'STACS2027.enumerated_cost_eq_load_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.enumerated_cost_eq_load_sum

/-- info: 'STACS2027.IsSimplePath' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.IsSimplePath

/-- info: 'STACS2027.IsSimplePath.vertices' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.IsSimplePath.vertices

/-- info: 'STACS2027.IsSimplePath.ne_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.IsSimplePath.ne_nil

/-- info: 'STACS2027.pathEdges_bridge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_bridge

/-- info: 'STACS2027.pathEdges_bridge_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_bridge_two

/-- info: 'STACS2027.remove_middle_sublist' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.remove_middle_sublist

/-- info: 'STACS2027.IsSimplePath.internal_split' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.IsSimplePath.internal_split

/-- info: 'STACS2027.IsSimplePath.remove_middle_endpoints' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.IsSimplePath.remove_middle_endpoints

/-- info: 'STACS2027.pathEdges_old_of_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_old_of_avoids

/-- info: 'STACS2027.IsSimplePath.close_cycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsSimplePath.close_cycle

/-- info: 'STACS2027.subdivideOnce_path_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivideOnce_path_contract

/-- info: 'STACS2027.signed_partition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.signed_partition

/-- info: 'STACS2027.literal_count_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.literal_count_bound

/-- info: 'STACS2027.BoundedOccurrence.literal_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BoundedOccurrence.literal_count

/-- info: 'STACS2027.clause_count_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clause_count_lower

/-- info: 'STACS2027.BoundedOccurrence.clause_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BoundedOccurrence.clause_count

/-- info: 'STACS2027.BoundedOccurrence.clause_count_variableBound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BoundedOccurrence.clause_count_variableBound

/-- info: 'STACS2027.SourceOccurrence' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.SourceOccurrence

/-- info: 'STACS2027.sourceValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.sourceValue

/-- info: 'STACS2027.sourceImplication' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.sourceImplication

/-- info: 'STACS2027.sourceChain' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.sourceChain

/-- info: 'STACS2027.sourceWheel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.sourceWheel

/-- info: 'STACS2027.sourceImplication_eval' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.sourceImplication_eval

/-- info: 'STACS2027.sourceChain_propagates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceChain_propagates

/-- info: 'STACS2027.sourceChain_returns' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sourceChain_returns

/-- info: 'STACS2027.sourceWheel_constant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceWheel_constant

/-- info: 'STACS2027.sourceChain_of_constant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sourceChain_of_constant

/-- info: 'STACS2027.sourceWheel_of_constant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sourceWheel_of_constant

/-- info: 'STACS2027.sourceChain_clause_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceChain_clause_length

/-- info: 'STACS2027.sourceWheel_clause_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceWheel_clause_length

/-- info: 'STACS2027.sourceGridFrom' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.sourceGridFrom

/-- info: 'STACS2027.sourceGrid' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.sourceGrid

/-- info: 'STACS2027.sourceGridFrom_indices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceGridFrom_indices

/-- info: 'STACS2027.sourceGrid_indices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceGrid_indices

/-- info: 'STACS2027.sourceGridFrom_variable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceGridFrom_variable

/-- info: 'STACS2027.sourceGrid_variable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceGrid_variable

/-- info: 'STACS2027.sourceGridFrom_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceGridFrom_mem

/-- info: 'STACS2027.sourceGrid_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceGrid_mem

/-- info: 'STACS2027.sourceGrid_all_indices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceGrid_all_indices

/-- info: 'STACS2027.sourceGrid_all_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceGrid_all_nodup

/-- info: 'STACS2027.gridCopyIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gridCopyIndex

/-- info: 'STACS2027.gridCopyClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gridCopyClause

/-- info: 'STACS2027.gridCopyFormula' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gridCopyFormula

/-- info: 'STACS2027.gridCopyClause_forget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.gridCopyClause_forget

/-- info: 'STACS2027.gridCopyFormula_forget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridCopyFormula_forget

/-- info: 'STACS2027.gridCopyClause_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.gridCopyClause_length

/-- info: 'STACS2027.gridCopyClause_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridCopyClause_cover

/-- info: 'STACS2027.gridCopyIndex_local_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridCopyIndex_local_bound

/-- info: 'STACS2027.gridCopyIndex_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridCopyIndex_injective

/-- info: 'STACS2027.gridCopyClause_indices_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridCopyClause_indices_nodup

/-- info: 'STACS2027.gridCopyFormula_indices_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridCopyFormula_indices_nodup

/-- info: 'STACS2027.gridCopyFormula_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridCopyFormula_cover

/-- info: 'STACS2027.tagSource' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.tagSource

/-- info: 'STACS2027.tagSource_forget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.tagSource_forget

/-- info: 'STACS2027.tagSource_flatten' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.tagSource_flatten

/-- info: 'STACS2027.sourcePositive' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.sourcePositive

/-- info: 'STACS2027.sourceNegative' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.sourceNegative

/-- info: 'STACS2027.sourceChain_flatten_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sourceChain_flatten_perm

/-- info: 'STACS2027.sourceWheel_flatten_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sourceWheel_flatten_perm

/-- info: 'STACS2027.sourceWheel_occurrences' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceWheel_occurrences

/-- info: 'STACS2027.sourceCopies' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.sourceCopies

/-- info: 'STACS2027.sourceGroups' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.sourceGroups

/-- info: 'STACS2027.splitSource' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.splitSource

/-- info: 'STACS2027.sourceGroups_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceGroups_mem

/-- info: 'STACS2027.sourceGroups_contains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceGroups_contains

/-- info: 'STACS2027.sourceWheel_family_occurrences' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceWheel_family_occurrences

/-- info: 'STACS2027.sourceCopies_occurrences' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceCopies_occurrences

/-- info: 'STACS2027.expandSourceUnit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.expandSourceUnit

/-- info: 'STACS2027.expandSourceUnit_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.expandSourceUnit_eval

/-- info: 'STACS2027.expandSourceUnits_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.expandSourceUnits_eval

/-- info: 'STACS2027.expandSourceUnit_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expandSourceUnit_size

/-- info: 'STACS2027.sourceLift' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sourceLift

/-- info: 'STACS2027.sourceDecode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.sourceDecode

/-- info: 'STACS2027.sourceLift_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceLift_at

/-- info: 'STACS2027.sourceLift_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceLift_value

/-- info: 'STACS2027.sourceCopies_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceCopies_eval

/-- info: 'STACS2027.sourceDecode_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceDecode_value

/-- info: 'STACS2027.sourceDecode_literal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceDecode_literal

/-- info: 'STACS2027.splitSource_satisfiable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.splitSource_satisfiable

/-- info: 'STACS2027.SourceWord.linearCoefficient' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.SourceWord.linearCoefficient

/-- info: 'STACS2027.SourceWord.linear_construction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.linear_construction

/-- info: 'STACS2027.SourceWord.SignMemory' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.SourceWord.SignMemory

/-- info: 'STACS2027.SourceWord.writeSign' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.SourceWord.writeSign

/-- info: 'STACS2027.SourceWord.State' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.SourceWord.State

/-- info: 'STACS2027.SourceWord.headerState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.headerState

/-- info: 'STACS2027.SourceWord.step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.step

/-- info: 'STACS2027.SourceWord.initial' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.SourceWord.initial

/-- info: 'STACS2027.SourceWord.run_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.run_header

/-- info: 'STACS2027.SourceWord.run_skip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.run_skip

/-- info: 'STACS2027.SourceWord.intervalSigns' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.SourceWord.intervalSigns

/-- info: 'STACS2027.SourceWord.intervalSigns_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.intervalSigns_succ

/-- info: 'STACS2027.SourceWord.ringSuffix' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.SourceWord.ringSuffix

/-- info: 'STACS2027.SourceWord.run_signs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.run_signs

/-- info: 'STACS2027.SourceWord.interval_sourceSigns' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.interval_sourceSigns

/-- info: 'STACS2027.SourceWord.graph_runs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.graph_runs

/-- info: 'STACS2027.SourceWord.extracts_sourceSigns' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.extracts_sourceSigns

/-- info: 'STACS2027.SourceWord.grid_next_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.grid_next_bounded

/-- info: 'STACS2027.SourceWord.ringGrid_input_variableBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.ringGrid_input_variableBound

/-- info: 'STACS2027.SourceWord.ringGrid_linear_word_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.ringGrid_linear_word_planar

/-- info: 'STACS2027.SourceWord.packed_linear_word_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.packed_linear_word_planar

/-- info: 'STACS2027.SourceWord.SignBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.SourceWord.SignBound

/-- info: 'STACS2027.SourceWord.SignBound.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.SignBound.mono

/-- info: 'STACS2027.SourceWord.writeSign_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.writeSign_bound

/-- info: 'STACS2027.SourceWord.DataBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.SourceWord.DataBound

/-- info: 'STACS2027.SourceWord.StateBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.SourceWord.StateBound

/-- info: 'STACS2027.SourceWord.StateBound.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.StateBound.mono

/-- info: 'STACS2027.SourceWord.header_state_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.header_state_bound

/-- info: 'STACS2027.SourceWord.step_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.step_bound

/-- info: 'STACS2027.SourceWord.Runs.bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.Runs.bounded

/-- info: 'STACS2027.SourceWord.initial_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.initial_bound

/-- info: 'STACS2027.SourceWord.wordWidth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.SourceWord.wordWidth

/-- info: 'STACS2027.SourceWord.WordsFit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.WordsFit

/-- info: 'STACS2027.SourceWord.bounded_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.bounded_words

/-- info: 'STACS2027.SourceWord.wordWidth_logarithmic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.wordWidth_logarithmic

/-- info: 'STACS2027.SourceWord.linear_word_construction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SourceWord.linear_word_construction

/-- info: 'STACS2027.FreshVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.FreshVertex

/-- info: 'STACS2027.subdivideOnce' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.subdivideOnce

/-- info: 'STACS2027.mem_subdivideOnce' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_subdivideOnce

/-- info: 'STACS2027.cycleEdges_endpoints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleEdges_endpoints

/-- info: 'STACS2027.cycleEdge_vertices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleEdge_vertices

/-- info: 'STACS2027.FreshVertex.not_mem_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.FreshVertex.not_mem_cycle

/-- info: 'STACS2027.subdivideOnce_neighbor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivideOnce_neighbor

/-- info: 'STACS2027.subdivideOnce_old_edge_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivideOnce_old_edge_absent

/-- info: 'STACS2027.subdivideOnce_old_of_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivideOnce_old_of_avoids

/-- info: 'STACS2027.cycleEdges_leading' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.cycleEdges_leading

/-- info: 'STACS2027.IsCycle.rotate_to_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.rotate_to_edge

/-- info: 'STACS2027.subdivideOnce_lift_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivideOnce_lift_head

/-- info: 'STACS2027.subdivideOnce_preserve_avoiding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivideOnce_preserve_avoiding

/-- info: 'STACS2027.subdivideOnce_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivideOnce_contract

/-- info: 'STACS2027.VerticesBelow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.VerticesBelow

/-- info: 'STACS2027.edge_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_below

/-- info: 'STACS2027.VerticesBelow.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.VerticesBelow.mono

/-- info: 'STACS2027.VerticesBelow.fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.VerticesBelow.fresh

/-- info: 'STACS2027.subdivideOnce_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivideOnce_below

/-- info: 'STACS2027.chainSteps' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.chainSteps

/-- info: 'STACS2027.chainSteps_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.chainSteps_below

/-- info: 'STACS2027.chainSteps_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.chainSteps_valid

/-- info: 'STACS2027.chainSteps_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.chainSteps_unchanged

/-- info: 'STACS2027.chainSteps_expands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.chainSteps_expands

/-- info: 'STACS2027.subdivisionGraph_append' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.subdivisionGraph_append

/-- info: 'STACS2027.validSubdivision_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.validSubdivision_append

/-- info: 'STACS2027.expandedEdge_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expandedEdge_append

/-- info: 'STACS2027.subdivisionGraph_membership' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivisionGraph_membership

/-- info: 'STACS2027.chainSteps_retains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.chainSteps_retains

/-- info: 'STACS2027.linkSteps' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.linkSteps

/-- info: 'STACS2027.linkEdges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.linkEdges

/-- info: 'STACS2027.subdivisionCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.subdivisionCount

/-- info: 'STACS2027.subdividedEdge_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdividedEdge_below

/-- info: 'STACS2027.subdividedEdge_avoids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdividedEdge_avoids

/-- info: 'STACS2027.linkSteps_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.linkSteps_unchanged

/-- info: 'STACS2027.linkSteps_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.linkSteps_head

/-- info: 'STACS2027.linkSteps_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.linkSteps_tail

/-- info: 'STACS2027.linkSteps_edge_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.linkSteps_edge_length

/-- info: 'STACS2027.realizeLinks_eq_expanded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.realizeLinks_eq_expanded

/-- info: 'STACS2027.linkSteps_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.linkSteps_valid

/-- info: 'STACS2027.linkSteps_from_base_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.linkSteps_from_base_valid

/-- info: 'STACS2027.realizeLinks_membership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.realizeLinks_membership

/-- info: 'STACS2027.realizeLinks_cycle_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.realizeLinks_cycle_projection

/-- info: 'STACS2027.splitEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.splitEdge

/-- info: 'STACS2027.liftEdges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.liftEdges

/-- info: 'STACS2027.mem_liftEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_liftEdges

/-- info: 'STACS2027.liftEdges_of_absent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.liftEdges_of_absent

/-- info: 'STACS2027.FreshVertex.edge_left_absent' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.FreshVertex.edge_left_absent

/-- info: 'STACS2027.FreshVertex.edge_right_absent' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.FreshVertex.edge_right_absent

/-- info: 'STACS2027.liftEdges_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.liftEdges_nodup

/-- info: 'STACS2027.IsCycle.edge_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.edge_length

/-- info: 'STACS2027.SameCycle.edge_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SameCycle.edge_perm

/-- info: 'STACS2027.liftEdges_contract_membership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.liftEdges_contract_membership

/-- info: 'STACS2027.subdivideOnce_cycle_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivideOnce_cycle_projection

/-- info: 'STACS2027.subdivideOnce_cycle_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivideOnce_cycle_lift

/-- info: 'STACS2027.SubdivisionStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.SubdivisionStep

/-- info: 'STACS2027.subdivisionGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.subdivisionGraph

/-- info: 'STACS2027.validSubdivision' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.validSubdivision

/-- info: 'STACS2027.expandedEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.expandedEdge

/-- info: 'STACS2027.subdivision_cycle_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivision_cycle_projection

/-- info: 'STACS2027.subdivision_cycle_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivision_cycle_lift

/-- info: 'STACS2027.expandedLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.expandedLength

/-- info: 'STACS2027.taggedFormulaGraph' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.taggedFormulaGraph

/-- info: 'STACS2027.renameClauseBlocks' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.renameClauseBlocks

/-- info: 'STACS2027.blockVertex_div' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.blockVertex_div

/-- info: 'STACS2027.renameClauseBlocks_variable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.renameClauseBlocks_variable

/-- info: 'STACS2027.renameClauseBlocks_private' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.renameClauseBlocks_private

/-- info: 'STACS2027.renameClauseBlocks_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.renameClauseBlocks_injective

/-- info: 'STACS2027.clauseVertex_block_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseVertex_block_bound

/-- info: 'STACS2027.formulaGraph_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_below

/-- info: 'STACS2027.mapGraph_normalized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapGraph_normalized

/-- info: 'STACS2027.formulaGraph_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_normalized

/-- info: 'STACS2027.mapGraph_comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapGraph_comp

/-- info: 'STACS2027.mapGraph_congr_on' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapGraph_congr_on

/-- info: 'STACS2027.renameClauseBlocks_clauseVertex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.renameClauseBlocks_clauseVertex

/-- info: 'STACS2027.taggedFormulaGraph_relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.taggedFormulaGraph_relabel

/-- info: 'STACS2027.taggedFormulaGraph_sat_iff_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.taggedFormulaGraph_sat_iff_assignment

/-- info: 'STACS2027.taggedWheels' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.taggedWheels

/-- info: 'STACS2027.taggedSplit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.taggedSplit

/-- info: 'STACS2027.taggedDecode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.taggedDecode

/-- info: 'STACS2027.exists_values_on_indices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.exists_values_on_indices

/-- info: 'STACS2027.taggedSplit_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.taggedSplit_bounded

/-- info: 'STACS2027.taggedDecode_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.taggedDecode_value

/-- info: 'STACS2027.taggedSplit_satisfiable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.taggedSplit_satisfiable

/-- info: 'STACS2027.firstUnit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.firstUnit

/-- info: 'STACS2027.firstUnit_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.firstUnit_some

/-- info: 'STACS2027.firstUnit_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.firstUnit_none

/-- info: 'STACS2027.unitReduce' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.unitReduce

/-- info: 'STACS2027.unitReduce_sat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.unitReduce_sat

/-- info: 'STACS2027.unitReduce_deletion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.unitReduce_deletion

/-- info: 'STACS2027.unitReduce_clause_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.unitReduce_clause_lower

/-- info: 'STACS2027.cleanFormula' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.cleanFormula

/-- info: 'STACS2027.cleanFormula_sat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cleanFormula_sat

/-- info: 'STACS2027.cleanFormula_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cleanFormula_bounded

/-- info: 'STACS2027.assignLiteral' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.assignLiteral

/-- info: 'STACS2027.setLiteral' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.setLiteral

/-- info: 'STACS2027.assignLiteral_self' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.assignLiteral_self

/-- info: 'STACS2027.assignLiteral_away' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.assignLiteral_away

/-- info: 'STACS2027.opposite_literal_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.opposite_literal_false

/-- info: 'STACS2027.evalClause_filter_assigned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.evalClause_filter_assigned

/-- info: 'STACS2027.setLiteral_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.setLiteral_eval

/-- info: 'STACS2027.setLiteral_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.setLiteral_avoids

/-- info: 'STACS2027.evalClause_congr_literals' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.evalClause_congr_literals

/-- info: 'STACS2027.evalCNF_congr_literals' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.evalCNF_congr_literals

/-- info: 'STACS2027.setLiteral_satisfiable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.setLiteral_satisfiable

/-- info: 'STACS2027.setLiteral_deletion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.setLiteral_deletion

/-- info: 'STACS2027.setLiteral_length_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.setLiteral_length_lt

/-- info: 'STACS2027.empty_clause_unsatisfiable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.empty_clause_unsatisfiable

/-- info: 'STACS2027.variablePotential' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variablePotential

/-- info: 'STACS2027.variablePotential_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variablePotential_lipschitz

/-- info: 'STACS2027.variablePotential_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variablePotential_source

/-- info: 'STACS2027.variablePotential_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variablePotential_other

/-- info: 'STACS2027.variableGraph_port_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableGraph_port_distance

/-- info: 'STACS2027.variableGraph_girth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableGraph_girth

/-- info: 'STACS2027.variableStateVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variableStateVertex

/-- info: 'STACS2027.variableSkeletonState' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variableSkeletonState

/-- info: 'STACS2027.variableExpandedState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableExpandedState

/-- info: 'STACS2027.variable_inputs_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_inputs_valid

/-- info: 'STACS2027.variableStateVertex_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableStateVertex_valid

/-- info: 'STACS2027.variableSkeletonState_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variableSkeletonState_zero

/-- info: 'STACS2027.variableSkeletonState_loads' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variableSkeletonState_loads

/-- info: 'STACS2027.variableSkeleton_normalizes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variableSkeleton_normalizes

/-- info: 'STACS2027.variableExpandedState_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableExpandedState_valid

/-- info: 'STACS2027.variableExpandedState_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableExpandedState_zero

/-- info: 'STACS2027.variableExpandedState_port' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableExpandedState_port

/-- info: 'STACS2027.variableExpandedState_loads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableExpandedState_loads

/-- info: 'STACS2027.variableExpansion_zero_normalizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableExpansion_zero_normalizes

/-- info: 'STACS2027.variableSkeletonCycles' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variableSkeletonCycles

/-- info: 'STACS2027.variableSkeletonInputs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variableSkeletonInputs

/-- info: 'STACS2027.variableSkeletonInputs_subset' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.variableSkeletonInputs_subset

/-- info: 'STACS2027.variableSkeleton_enumeration' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableSkeleton_enumeration

/-- info: 'STACS2027.variableSkeleton_cycles_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableSkeleton_cycles_valid

/-- info: 'STACS2027.variableSkeleton_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableSkeleton_represents

/-- info: 'STACS2027.variableWeight' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variableWeight

/-- info: 'STACS2027.variable_edge_expanded_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_edge_expanded_length

/-- info: 'STACS2027.variable_expanded_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_expanded_length

/-- info: 'STACS2027.variable_input_lengths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_input_lengths

/-- info: 'STACS2027.variable_outer_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_outer_length

/-- info: 'STACS2027.variable_general_cycle_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_general_cycle_classification

/-- info: 'STACS2027.variable_general_cycle_realization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_general_cycle_realization

/-- info: 'STACS2027.blockVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.blockVertex

/-- info: 'STACS2027.blockVertex_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.blockVertex_injective

/-- info: 'STACS2027.variableEndpoint' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variableEndpoint

/-- info: 'STACS2027.clauseEndpoint' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseEndpoint

/-- info: 'STACS2027.clausePortAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clausePortAt

/-- info: 'STACS2027.attachmentAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.attachmentAt

/-- info: 'STACS2027.clauseVertex' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseVertex

/-- info: 'STACS2027.variableEndpoint_bound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variableEndpoint_bound

/-- info: 'STACS2027.variableEndpoint_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variableEndpoint_injective

/-- info: 'STACS2027.clausePortAt_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clausePortAt_spec

/-- info: 'STACS2027.clausePortAt_endpoint' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clausePortAt_endpoint

/-- info: 'STACS2027.attachmentAt_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.attachmentAt_spec

/-- info: 'STACS2027.clauseVertex_attachment' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseVertex_attachment

/-- info: 'STACS2027.clauseVertex_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseVertex_injective

/-- info: 'STACS2027.WordConstructor.Phase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.Phase

/-- info: 'STACS2027.WordConstructor.Config' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.Config

/-- info: 'STACS2027.WordConstructor.ready' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.ready

/-- info: 'STACS2027.WordConstructor.ready_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.ready_reverse

/-- info: 'STACS2027.WordConstructor.step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.step

/-- info: 'STACS2027.WordConstructor.Executes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.Executes

/-- info: 'STACS2027.WordConstructor.Executes.trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.Executes.trans

/-- info: 'STACS2027.WordConstructor.run_variable_edges' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.run_variable_edges

/-- info: 'STACS2027.WordConstructor.variableOutput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.variableOutput

/-- info: 'STACS2027.WordConstructor.variableOutput_range' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.variableOutput_range

/-- info: 'STACS2027.WordConstructor.run_variables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.run_variables

/-- info: 'STACS2027.WordConstructor.run_literals' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.run_literals

/-- info: 'STACS2027.WordConstructor.run_clause_edges' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.run_clause_edges

/-- info: 'STACS2027.WordConstructor.clauseOutput' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.clauseOutput

/-- info: 'STACS2027.WordConstructor.clauseTime' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.clauseTime

/-- info: 'STACS2027.WordConstructor.run_clauses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.run_clauses

/-- info: 'STACS2027.WordConstructor.clauseOutput_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.clauseOutput_refines

/-- info: 'STACS2027.WordConstructor.initial' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.initial

/-- info: 'STACS2027.WordConstructor.transitionCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.transitionCount

/-- info: 'STACS2027.WordConstructor.executes_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.executes_graph

/-- info: 'STACS2027.WordConstructor.clauseTime_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.clauseTime_bound

/-- info: 'STACS2027.WordConstructor.linearCoefficient' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.linearCoefficient

/-- info: 'STACS2027.WordConstructor.linearCoefficient_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.linearCoefficient_eq

/-- info: 'STACS2027.WordConstructor.transitionCount_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.transitionCount_linear

/-- info: 'STACS2027.WordConstructor.graph_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.graph_correct

/-- info: 'STACS2027.WordConstructor.ready_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.ready_spec

/-- info: 'STACS2027.WordConstructor.block_payload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.block_payload

/-- info: 'STACS2027.WordConstructor.mapEdge_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordConstructor.mapEdge_payload

/-- info: 'STACS2027.WordPipeline.Runs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Runs

/-- info: 'STACS2027.WordPipeline.Runs.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Runs.trans

/-- info: 'STACS2027.WordPipeline.Runs.simulate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Runs.simulate

/-- info: 'STACS2027.WordPipeline.finish_padding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.finish_padding

/-- info: 'STACS2027.WordPipeline.linearCoefficient' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.linearCoefficient

/-- info: 'STACS2027.WordPipeline.linearCoefficient_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.linearCoefficient_eq

/-- info: 'STACS2027.WordPipeline.rejected_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.rejected_output

/-- info: 'STACS2027.WordPipeline.full_domain_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.full_domain_linear

/-- info: 'STACS2027.WordPipeline.Payload.PlacedBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.PlacedBound

/-- info: 'STACS2027.WordPipeline.Payload.GraphPhaseBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.GraphPhaseBound

/-- info: 'STACS2027.WordPipeline.Payload.GraphStateBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.GraphStateBound

/-- info: 'STACS2027.WordPipeline.Payload.PlacedBound.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.PlacedBound.mono

/-- info: 'STACS2027.WordPipeline.Payload.GraphPhaseBound.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.GraphPhaseBound.mono

/-- info: 'STACS2027.WordPipeline.Payload.GraphStateBound.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.GraphStateBound.mono

/-- info: 'STACS2027.WordPipeline.Payload.block_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.block_bound

/-- info: 'STACS2027.WordPipeline.Payload.clause_vertex_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.clause_vertex_bound

/-- info: 'STACS2027.WordPipeline.Payload.graph_step_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.graph_step_bound

/-- info: 'STACS2027.WordPipeline.Payload.graph_initial_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.graph_initial_bound

/-- info: 'STACS2027.WordPipeline.Header.State' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Header.State

/-- info: 'STACS2027.WordPipeline.Header.step' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Header.step

/-- info: 'STACS2027.WordPipeline.Header.run_clause' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Header.run_clause

/-- info: 'STACS2027.WordPipeline.Header.run_formula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Header.run_formula

/-- info: 'STACS2027.WordPipeline.Header.computes_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Header.computes_bound

/-- info: 'STACS2027.WordPipeline.State' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.State

/-- info: 'STACS2027.WordPipeline.normalizeState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.normalizeState

/-- info: 'STACS2027.WordPipeline.initializeState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.initializeState

/-- info: 'STACS2027.WordPipeline.unitsState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.unitsState

/-- info: 'STACS2027.WordPipeline.extractState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.extractState

/-- info: 'STACS2027.WordPipeline.paddingState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.paddingState

/-- info: 'STACS2027.WordPipeline.headerState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.headerState

/-- info: 'STACS2027.WordPipeline.graphState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.graphState

/-- info: 'STACS2027.WordPipeline.step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.step

/-- info: 'STACS2027.WordPipeline.initial' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.initial

/-- info: 'STACS2027.WordPipeline.normalize_simulation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.normalize_simulation

/-- info: 'STACS2027.WordPipeline.initialize_simulation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.initialize_simulation

/-- info: 'STACS2027.WordPipeline.units_simulation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.units_simulation

/-- info: 'STACS2027.WordPipeline.extract_simulation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.extract_simulation

/-- info: 'STACS2027.WordPipeline.padding_simulation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.padding_simulation

/-- info: 'STACS2027.WordPipeline.header_simulation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.header_simulation

/-- info: 'STACS2027.WordPipeline.graph_simulation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.graph_simulation

/-- info: 'STACS2027.WordPipeline.StateBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.StateBound

/-- info: 'STACS2027.WordPipeline.StateBound.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.StateBound.mono

/-- info: 'STACS2027.WordPipeline.normalize_state_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.normalize_state_bound

/-- info: 'STACS2027.WordPipeline.initialize_state_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.initialize_state_bound

/-- info: 'STACS2027.WordPipeline.units_state_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.units_state_bound

/-- info: 'STACS2027.WordPipeline.extract_state_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.extract_state_bound

/-- info: 'STACS2027.WordPipeline.padding_state_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.padding_state_bound

/-- info: 'STACS2027.WordPipeline.header_state_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.header_state_bound

/-- info: 'STACS2027.WordPipeline.graph_state_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.graph_state_bound

/-- info: 'STACS2027.WordPipeline.step_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.step_bound

/-- info: 'STACS2027.WordPipeline.Runs.bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Runs.bounded

/-- info: 'STACS2027.WordPipeline.initial_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.initial_bound

/-- info: 'STACS2027.WordPipeline.wordWidth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.wordWidth

/-- info: 'STACS2027.WordPipeline.WordsFit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.WordsFit

/-- info: 'STACS2027.WordPipeline.bounded_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.bounded_words

/-- info: 'STACS2027.WordPipeline.wordWidth_logarithmic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.wordWidth_logarithmic

/-- info: 'STACS2027.WordPipeline.full_domain_linear_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.full_domain_linear_words

/-- info: 'STACS2027.WordPipeline.Payload.formula_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.formula_cons

/-- info: 'STACS2027.WordPipeline.Payload.formula_tail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.formula_tail

/-- info: 'STACS2027.WordPipeline.Payload.clause_tail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.clause_tail

/-- info: 'STACS2027.WordPipeline.Payload.smallDistinct_sublist' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.smallDistinct_sublist

/-- info: 'STACS2027.WordPipeline.Payload.normalizeOne_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.normalizeOne_bound

/-- info: 'STACS2027.WordPipeline.Payload.NormStateBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.NormStateBound

/-- info: 'STACS2027.WordPipeline.Payload.NormStateBound.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.NormStateBound.mono

/-- info: 'STACS2027.WordPipeline.Payload.norm_step_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.norm_step_bound

/-- info: 'STACS2027.WordPipeline.Payload.ExtractStateBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.ExtractStateBound

/-- info: 'STACS2027.WordPipeline.Payload.ExtractStateBound.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.ExtractStateBound.mono

/-- info: 'STACS2027.WordPipeline.Payload.extract_step_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.extract_step_bound

/-- info: 'STACS2027.WordPipeline.Payload.PaddingStateBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.PaddingStateBound

/-- info: 'STACS2027.WordPipeline.Payload.PaddingStateBound.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.PaddingStateBound.mono

/-- info: 'STACS2027.WordPipeline.Payload.padding_step_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.padding_step_bound

/-- info: 'STACS2027.WordPipeline.Payload.HeaderStateBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.HeaderStateBound

/-- info: 'STACS2027.WordPipeline.Payload.HeaderStateBound.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.HeaderStateBound.mono

/-- info: 'STACS2027.WordPipeline.Payload.header_step_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Payload.header_step_bound
