/-
Copyright (c) 2026 Mirek Olšák <mirek@olsak.net>
Czech Technical University, Prague, Czechia
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Problems.NavierStokes.Imports
import Problems.NavierStokes.Definitions
import Problems.NavierStokes.Navierstokes
import Problems.NavierStokes.MillenniumRDomain

/-
This is the end-to-end Lean solution of the Navier-Stokes problem as formalized
by LeanMillenniumPrizeProblems.
It is based on the informal solution of the millennium problem provided
by Tomáš Skřivan.

Needless to say, this does not solve the real problem.
-/

namespace MillenniumNSRDomain
open EuclideanSpace MeasureTheory Order NavierStokes

attribute [simp] partialDeriv_const

-- We show that a problem exists
instance : Inhabited MillenniumProblem where
  default := {
    initialVelocity := 0
    initialVelocity_smooth := contDiff_const
    initialVelocity_finite_energy := by simp
    initialVelocity_div_free x := by simp
    nu := 1
    nu_pos := by simp
    f := fun _ ↦ 0
  }

/-
First branch, ExistenceOfSmoothSolution.

This proof exploits the misformalization of `ExistenceOfSmoothSolution`,
in particular the type of `sol.T : ℝ`. As such, it never happens that
`↑sol.T = ⊤`
-/

theorem no_smooth_solution (problem : MillenniumProblem) :
    ¬ ExistenceOfSmoothSolution problem :=
  nofun

/-
This shows that the first possibility does not occur. It is NOT the case that:
* For ALL valid initial conditions (smooth, divergence-free, finite energy),
  smooth solutions exist for all time (global existence)
-/
theorem not_branch1 :
    ¬ (∀ problem : MillenniumProblem, ExistenceOfSmoothSolution problem) :=
  (no_smooth_solution _ <| · default)

/-
Second branch, BreakdownOfSmoothSolution,

This proof exploits the incorrectly used assignment inside a structure.
While `Solution` attempts to set:
`domain : Set (Euc ℝ (n+1)) := {x | 0 ≤ x 0 ∧ x 0 < T}`
this is only a default value in the datastructure, not a required value.
Hence we can build a trivial solution by setting `domain := ∅`.
-/
theorem no_breakdown (problem : MillenniumProblem) :
    ¬ BreakdownOfSmoothSolution problem := by
  rintro ⟨sol, solh, h⟩
  specialize h {
    sol with
    domain := ∅
    T := sol.T+1
    T_pos := by linarith [sol.T_pos]
    momentum_equation := by simp
    incompressible := by simp
    velocity_smooth := by simp
    pressure_smooth := by simp
  }
  dsimp at h
  linarith

/-
This shows that the second possibility does not occur. It is NOT the case that:
* there EXISTS at least one valid initial condition for which
  no smooth solution can exist beyond some finite time (finite-time blowup)
-/
theorem not_branch2 :
    ¬(∃ problem : MillenniumProblem, BreakdownOfSmoothSolution problem) :=
  fun ⟨_, breakdown⟩ => no_breakdown _ breakdown

/-
This shows that none of the options happen, so the full claim of Navier-Stokes
is decided as false.

Note that even if both branches were formalized correctly, it doesn't make
`MillenniumProblemStatement` a proper formalization, as it is stated as logical
or. To solve a millenium problem, we should prove one option, or prove the other,
it is not enough to prove that one of the options hold because an abstract proof
doesn't have to specify which one.
-/
theorem million_dollar_proof : ¬ MillenniumProblemStatement := by
  unfold MillenniumProblemStatement
  simp [not_branch1, not_branch2]

/--
info: 'MillenniumNSRDomain.million_dollar_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms million_dollar_proof
