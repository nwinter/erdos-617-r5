/-
R11 validation: print the exact statements of the four final theorems and the
core definitions, so a reviewer can read verbatim what is proved (did_you_prove_it
item 5 / ValidatingProofs "what does the theorem statement mean").

Run with:  lake env lean StatementPrint.lean
-/
import Lean617.Final

open Erdos617

-- Final theorem signatures (exact types the kernel accepted):
#check @erdos_617_r5
#check @erdos_617_r5_upstream
#check @lemma_MH2
#check @lemma_MM

-- The single classical hypothesis the final theorems are conditional on:
#print Erdos617.KPEqualityClassification
#check @brouwerFacts_of

-- Core definitions the statements rest on:
#print Erdos617.Main
#print Erdos617.Balanced
#print Erdos617.Misses
#print Erdos617.BrouwerFacts

-- Confirm Main means "no balanced 5-colouring of K₂₆":
#check @main_iff_no_balanced
