import Mettapedia.CategoryTheory.RelativeClosedSyntax

/-!
# Reflection of complete codes under injective primitive renaming

With the base category retained, injective object and arrow name maps
reflect equality of every complete object and arrow expression. The mutual
proof retains the embedded arrows in equalizers and every annotation and
candidate in an equalizer lift. It concerns raw codes; it does not assert
faithfulness of the category obtained by adding equation declarations.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax

open _root_.CategoryTheory

universe u v a b
variable {C : Type u} [Category.{v} C] {before : Symbols.{a}} {after : Symbols.{b}}
variable (objects : before.ObjectName → after.ObjectName) (arrows : before.ArrowName → after.ArrowName)
mutual

theorem ObjectCode.map_injective
    (objectsInjective : Function.Injective objects) (arrowsInjective : Function.Injective arrows) :
    (first second : ObjectCode C before) →
    first.map (Functor.id C) objects arrows = second.map (Functor.id C) objects arrows → first = second
  | .base _, other, same => by
      cases other <;> cases same; rfl
  | .name origin, other, same => by
      cases other <;> simp only [ObjectCode.map, ObjectCode.name.injEq, reduceCtorEq] at same
      exact congrArg ObjectCode.name (objectsInjective same)
  | .terminal, other, same => by
      cases other <;> cases same; rfl
  | .product first second, other, same => by
      cases other <;> simp only [ObjectCode.map, ObjectCode.product.injEq, reduceCtorEq] at same
      rename_i nextFirst nextSecond
      obtain ⟨left, right⟩ := same
      cases ObjectCode.map_injective objectsInjective arrowsInjective first nextFirst left
      cases ObjectCode.map_injective objectsInjective arrowsInjective second nextSecond right
      rfl
  | .exponential argument result, other, same => by
      cases other <;> simp only [ObjectCode.map, ObjectCode.exponential.injEq, reduceCtorEq] at same
      rename_i nextArgument nextResult
      obtain ⟨left, right⟩ := same
      cases ObjectCode.map_injective objectsInjective arrowsInjective argument nextArgument left
      cases ObjectCode.map_injective objectsInjective arrowsInjective result nextResult right
      rfl
  | .equalizer source target first second, other, same => by
      cases other <;> simp only [ObjectCode.map, ObjectCode.equalizer.injEq, reduceCtorEq] at same
      rename_i nextSource nextTarget nextFirst nextSecond
      obtain ⟨sourceRead, targetRead, firstRead, secondRead⟩ := same
      cases ObjectCode.map_injective objectsInjective arrowsInjective source nextSource sourceRead
      cases ObjectCode.map_injective objectsInjective arrowsInjective target nextTarget targetRead
      cases ArrowCode.map_injective objectsInjective arrowsInjective first nextFirst firstRead
      cases ArrowCode.map_injective objectsInjective arrowsInjective second nextSecond secondRead
      rfl

theorem ArrowCode.map_injective
    (objectsInjective : Function.Injective objects) (arrowsInjective : Function.Injective arrows) :
    (first second : ArrowCode C before) →
    first.map (Functor.id C) objects arrows = second.map (Functor.id C) objects arrows → first = second
  | .base _, other, same => by
      cases other <;> cases same; rfl
  | .name origin, other, same => by
      cases other <;> simp only [ArrowCode.map, ArrowCode.name.injEq, reduceCtorEq] at same
      exact congrArg ArrowCode.name (arrowsInjective same)
  | .identity object, other, same => by
      cases other <;> simp only [ArrowCode.map, ArrowCode.identity.injEq, reduceCtorEq] at same
      rename_i nextObject
      exact congrArg ArrowCode.identity
        (ObjectCode.map_injective objectsInjective arrowsInjective object nextObject same)
  | .compose first second, other, same => by
      cases other <;> simp only [ArrowCode.map, ArrowCode.compose.injEq, reduceCtorEq] at same
      rename_i nextFirst nextSecond
      obtain ⟨left, right⟩ := same
      cases ArrowCode.map_injective objectsInjective arrowsInjective first nextFirst left
      cases ArrowCode.map_injective objectsInjective arrowsInjective second nextSecond right
      rfl
  | .terminal source, other, same => by
      cases other <;> simp only [ArrowCode.map, ArrowCode.terminal.injEq, reduceCtorEq] at same
      rename_i nextSource
      exact congrArg ArrowCode.terminal
        (ObjectCode.map_injective objectsInjective arrowsInjective source nextSource same)
  | .first first second, other, same => by
      cases other <;> simp only [ArrowCode.map, ArrowCode.first.injEq, reduceCtorEq] at same
      rename_i nextFirst nextSecond
      obtain ⟨left, right⟩ := same
      cases ObjectCode.map_injective objectsInjective arrowsInjective first nextFirst left
      cases ObjectCode.map_injective objectsInjective arrowsInjective second nextSecond right
      rfl
  | .second first second, other, same => by
      cases other <;> simp only [ArrowCode.map, ArrowCode.second.injEq, reduceCtorEq] at same
      rename_i nextFirst nextSecond
      obtain ⟨left, right⟩ := same
      cases ObjectCode.map_injective objectsInjective arrowsInjective first nextFirst left
      cases ObjectCode.map_injective objectsInjective arrowsInjective second nextSecond right
      rfl
  | .pair first second, other, same => by
      cases other <;> simp only [ArrowCode.map, ArrowCode.pair.injEq, reduceCtorEq] at same
      rename_i nextFirst nextSecond
      obtain ⟨left, right⟩ := same
      cases ArrowCode.map_injective objectsInjective arrowsInjective first nextFirst left
      cases ArrowCode.map_injective objectsInjective arrowsInjective second nextSecond right
      rfl
  | .evaluation argument result, other, same => by
      cases other <;> simp only [ArrowCode.map, ArrowCode.evaluation.injEq, reduceCtorEq] at same
      rename_i nextArgument nextResult
      obtain ⟨left, right⟩ := same
      cases ObjectCode.map_injective objectsInjective arrowsInjective argument nextArgument left
      cases ObjectCode.map_injective objectsInjective arrowsInjective result nextResult right
      rfl
  | .curry context argument result body, other, same => by
      cases other <;> simp only [ArrowCode.map, ArrowCode.curry.injEq, reduceCtorEq] at same
      rename_i nextContext nextArgument nextResult nextBody
      obtain ⟨contextRead, argumentRead, resultRead, bodyRead⟩ := same
      cases ObjectCode.map_injective objectsInjective arrowsInjective context nextContext contextRead
      cases ObjectCode.map_injective objectsInjective arrowsInjective argument nextArgument argumentRead
      cases ObjectCode.map_injective objectsInjective arrowsInjective result nextResult resultRead
      cases ArrowCode.map_injective objectsInjective arrowsInjective body nextBody bodyRead
      rfl
  | .equalizerArrow source target first second, other, same => by
      cases other <;> simp only [ArrowCode.map, ArrowCode.equalizerArrow.injEq, reduceCtorEq] at same
      rename_i nextSource nextTarget nextFirst nextSecond
      obtain ⟨sourceRead, targetRead, firstRead, secondRead⟩ := same
      cases ObjectCode.map_injective objectsInjective arrowsInjective source nextSource sourceRead
      cases ObjectCode.map_injective objectsInjective arrowsInjective target nextTarget targetRead
      cases ArrowCode.map_injective objectsInjective arrowsInjective first nextFirst firstRead
      cases ArrowCode.map_injective objectsInjective arrowsInjective second nextSecond secondRead
      rfl
  | .equalizerLift source target first second context candidate, other, same => by
      cases other <;> simp only [ArrowCode.map, ArrowCode.equalizerLift.injEq, reduceCtorEq] at same
      rename_i nextSource nextTarget nextFirst nextSecond nextContext nextCandidate
      obtain ⟨sourceRead, targetRead, firstRead, secondRead, contextRead, candidateRead⟩ := same
      cases ObjectCode.map_injective objectsInjective arrowsInjective source nextSource sourceRead
      cases ObjectCode.map_injective objectsInjective arrowsInjective target nextTarget targetRead
      cases ArrowCode.map_injective objectsInjective arrowsInjective first nextFirst firstRead
      cases ArrowCode.map_injective objectsInjective arrowsInjective second nextSecond secondRead
      cases ObjectCode.map_injective objectsInjective arrowsInjective context nextContext contextRead
      cases ArrowCode.map_injective objectsInjective arrowsInjective candidate nextCandidate candidateRead
      rfl

end

end Mettapedia.CategoryTheory.RelativeClosedSyntax
