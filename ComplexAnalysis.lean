import VersoManual
import ComplexAnalysis.Chapter0Verso
import ComplexAnalysis.Chapter1_1Verso
import ComplexAnalysis.Chapter1_3Verso
import ComplexAnalysis.Chapter1_4Verso
import ComplexAnalysis.Chapter2_7Verso
import ComplexAnalysis.Chapter6_2Verso
import ComplexAnalysis.Chapter7_3Verso
import ComplexAnalysis.Chapter12_3Verso

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "MAT3253 Complex Variables" =>

%%%
authors := ["Kenneth Shum"]
%%%

Lean proof of selected theorems in the notes for the course MAT3253 Complex Variables.

The program compiles with *Mathlib 4.29*.

Inspired by Terence Tao’s Lean Companion to Analysis I,
the goal of this repository is to provide *faithful Lean translations
of proofs from the textbook*, following the structure and reasoning of
the original arguments as closely as possible.
While many of these results already appear in Mathlib,
the library versions are often intentionally concise.
In contrast, the proofs here aim to be pedagogically transparent,
mirroring the step‑by‑step style of the textbook.

Lean is designed to be _proof‑irrelevant_:
two proofs of the same proposition are considered definitionally
interchangeable. Thus, both the detailed textbook‑style proofs and
the shorter Mathlib proofs are equally valid in Lean. Nevertheless,
the expanded versions can be more helpful for learners who want to
see the intermediate reasoning, while the Mathlib versions are ideal
for reuse in later developments.

---

*Funding Acknowledgment*

This project is partially funded by *CUHK(SZ) CLEAR Teaching Innovation Grant* (2024),
"Enhancement of mathematical learning using the LEAN computer proof assistant".

---

*Contributors*

The library on extended complex numbers in Chapter 2
is completed with great help by *Fubin Yan*.

Parts of the formalization were developed with assistance
from *Harmonic Aristotle*, *ChatGPT 5.5*, and *Gemini 3.1*.

{include 1 ComplexAnalysis.Chapter0Verso}

{include 1 ComplexAnalysis.Chapter1_1Verso}

{include 1 ComplexAnalysis.Chapter1_3Verso}

{include 1 ComplexAnalysis.Chapter1_4Verso}

{include 1 ComplexAnalysis.Chapter2_7Verso}

{include 1 ComplexAnalysis.Chapter6_2Verso}

{include 1 ComplexAnalysis.Chapter7_3Verso}

{include 1 ComplexAnalysis.Chapter12_3Verso}
