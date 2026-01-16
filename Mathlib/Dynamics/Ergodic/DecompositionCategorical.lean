/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import Mathlib

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable (M : Type u₁) (C : Type u₂) [Monoid M] [Category.{v₁} C]

def DynamicalSystem := Functor (SingleObj M) C

variable {α : Type*} (f : α → α)  
  
variable (D : DynamicalSystem M C)

open Limits

structure IsMarkovColimit (t : Cocone D) extends IsColimit t
