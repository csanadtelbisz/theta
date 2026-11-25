/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.analysis.algorithm.refinery

import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionRuleBuilder.Companion.UNSUPPORTED_FEATURE
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntType
import java.math.BigInteger

abstract class RefineryTransitionSystemBuilder {

  companion object {

    val String.refinerified: String
      get() = replace("::", "__")

    val Type.refineryType: String
      get() =
        when (this) {
          is BoolType -> "boolean"
          is IntType -> "int"
          else -> error("Unsupported type in RefineryTransformationSystemBuilder: $this")
        }
  }

  protected val variables = mutableSetOf<Decl<*>>()

  // Metamodel

  protected val metamodel: String =
    """
    |import builtin::strategy.
    |
    |pred $UNSUPPORTED_FEATURE().
    |!$UNSUPPORTED_FEATURE().
    |pred invalidDeref().
    |!invalidDeref().
    |pred invalidFree().
    |!invalidFree().
    |pred invalidMemtrack().
    |!invalidMemtrack().
    |
    |class MemoryRegion {
    |    int address
    |    contains MemoryObject[] parts
    |    int size
    |    int dataType
    |}
    |
    |pred valid(MemoryRegion region).
    |pred interpreted(MemoryRegion region).
    |default !interpreted(*).
    |
    |abstract class Pointable.
    |
    |class InvalidMemory extends Pointable.
    |
    |abstract class MemoryObject extends Pointable {
    |    int offset
    |    int size
    |}
    |
    |class Value extends MemoryObject {
    |    int value
    |}
    |
    |abstract class AbstractPointer {
    |    Pointable target
    |}
    |
    |class Pointer extends AbstractPointer, MemoryObject.
    |
    |class NullPointer extends AbstractPointer.
    |
    |class ConstantPointer extends AbstractPointer.
    |
    |class NamedPointer {
    |    contains Pointer pointer
    |}
    """
      .trimMargin()

  // Environment

  protected open val environmentDeclarations: List<String>
    get() =
      listOf("int next_address().") +
        variables.map { "${it.type.refineryType} ${it.name.refinerified}()." }

  protected open val environmentSetup: String
    get() = environmentDeclarations.joinToString("\n")

  protected val invalidMemorySetup: String
    get() =
      """
      |InvalidMemory(null).
      |atom null.
      |scope InvalidMemory += 0.
      |
      |NullPointer(nullptr).
      |atom nullptr.
      |scope NullPointer += 0.
      |offset(nullptr): 0.
      |target(nullptr, null).
      """
        .trimMargin()

  // Initial state

  /** The value of the allocation counter before the first allocation. */
  protected abstract val initialNextAddress: BigInteger

  protected open val initialStateDeclarations: List<String>
    get() =
      listOf(
        "scope MemoryRegion += 0.",
        "scope ConstantPointer += 0.",
        "scope Value += 0.",
        "scope Pointer += 0.",
        "next_address(): $initialNextAddress.",
      )

  protected val initialState: String
    get() = initialStateDeclarations.joinToString("\n")

  // Transitions

  protected abstract val transitions: List<RefineryRule>

  protected val transitionDeclarations: String
    get() = transitions.joinToString("\n\n") { it.toString() }

  // Error property

  /** The violations of the verified property; reaching an unsupported feature always stops too. */
  protected abstract val targetProperties: List<String>

  protected val targetDeclaration: String
    get() =
      """
      |@target
      |pred error_property() <-> ${(listOf("$UNSUPPORTED_FEATURE()") + targetProperties).joinToString(" ; ")}.
      """
        .trimMargin()

  // Top-level declarations

  protected val topLevelDeclaration: List<String>
    get() =
      listOf(
        "% --- METAMODEL ---",
        metamodel,
        "% --- ENVIRONMENT SETUP ---",
        environmentSetup,
        invalidMemorySetup,
        "% --- INITIAL STATE ---",
        initialState,
        "% --- ERROR PROPERTY ---",
        targetDeclaration,
        "% --- TRANSITIONS ---",
        transitionDeclarations,
      )

  fun build(): String = topLevelDeclaration.joinToString("\n\n")
}
