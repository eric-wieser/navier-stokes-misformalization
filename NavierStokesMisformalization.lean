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

-- First branch, ExistenceOfSmoothSolution

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

-- Second branch, BreakdownOfSmoothSolution,
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
-/
theorem million_dollar_proof : ¬ MillenniumProblemStatement := by
  unfold MillenniumProblemStatement
  simp [not_branch1, not_branch2]

/--
info: 'MillenniumNSRDomain.million_dollar_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms million_dollar_proof
