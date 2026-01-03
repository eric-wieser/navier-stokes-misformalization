/-
Copyright (c) 2026 Mirek Olšák <mirek@olsak.net>
Czech Technical University, Prague, Czechia
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
This is the end-to-end Lean solution of the Navier-Stokes problem as formalized
by LeanMillenniumPrizeProblems.
It is based on the informal solution of the millennium problem provided
by Tomáš Skřivan.

To test it, clone the repository
https://github.com/lean-dojo/LeanMillenniumPrizeProblems/tree/main
and copy this file to the directory `Problems/NavierStokes`
-/

import Problems.NavierStokes.Imports
import Problems.NavierStokes.Definitions
import Problems.NavierStokes.Navierstokes
import Problems.NavierStokes.MillenniumRDomain

namespace MillenniumNSRDomain
open EuclideanSpace MeasureTheory Order NavierStokes

-- We show that a problem exists
instance : Inhabited MillenniumProblem where
  default := {
    initialVelocity := fun _ ↦ 0
    initialVelocity_smooth := by apply contDiff_const
    initialVelocity_finite_energy := by simp
    initialVelocity_div_free := by
      intro x
      simp
      apply Finset.sum_eq_zero
      intro i i_univ
      apply partialDeriv_const
    nu := 1
    nu_pos := by norm_num
    f := fun _ ↦ 0
  }

-- First branch, ExistenceOfSmoothSolution

-- Short proof by Yaël Dillies of a non-existence of a smooth solution
theorem no_smooth_solution (problem : MillenniumProblem) :
    ¬ ExistenceOfSmoothSolution problem := by rintro ⟨sol, ⟨⟩⟩

/-
This shows that the first possibility does not occur. It is NOT the case that:
* For ALL valid initial conditions (smooth, divergence-free, finite energy),
  smooth solutions exist for all time (global existence)
-/
theorem branch1_eq_False :
    (∀ problem : MillenniumProblem, ExistenceOfSmoothSolution problem) = False := by
  simp
  use default
  apply no_smooth_solution

-- Second branch, BreakdownOfSmoothSolution,
theorem no_breakdown (problem : MillenniumProblem) :
    ¬ BreakdownOfSmoothSolution problem := by
  unfold BreakdownOfSmoothSolution
  push_neg
  intro sol solh
  use {
    sol with
    domain := ∅
    T := sol.T+1
    T_pos := by linarith [sol.T_pos]
    momentum_equation := by simp
    incompressible := by simp
    velocity_smooth := by simp
    pressure_smooth := by simp
  }
  simp

/-
This shows that the second possibility does not occur. It is NOT the case that:
* there EXISTS at least one valid initial condition for which
  no smooth solution can exist beyond some finite time (finite-time blowup)
-/
theorem branch2_eq_False :
    (∃ problem : MillenniumProblem, BreakdownOfSmoothSolution problem) = False := by
  simp
  intro x
  apply no_breakdown

/-
This shows that none of the options happen, so the full claim of Navier-Stokes
is decided as false.
-/
theorem million_dollar_proof : ¬ MillenniumProblemStatement := by
  unfold MillenniumProblemStatement
  rw [branch1_eq_False, branch2_eq_False]
  -- This simplifies to `False ∨ False`, which can be decided
  decide
