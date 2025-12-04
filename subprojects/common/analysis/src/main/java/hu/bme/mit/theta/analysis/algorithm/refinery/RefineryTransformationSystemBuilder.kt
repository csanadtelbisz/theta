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

import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransformationSystemBuilder.Companion.ENVIRONMENT
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.MultiaryExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.abstracttype.MulExpr
import hu.bme.mit.theta.core.type.abstracttype.NegExpr
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType

abstract class RefineryTransformationSystemBuilder {

  companion object {

    const val ENVIRONMENT = "env"
  }

  protected val variables = mutableSetOf<Decl<*>>()

  protected val metamodel: String =
    """
    |class MemoryRegion {
    |    int address
    |    contains MemoryObject[] parts
    |}
    |
    |class MemoryObject {
    |    int offset
    |    contains Pointable object
    |}
    |
    |abstract class Pointable.
    |
    |class Pointer extends Pointable {
    |    contains MemoryObject target
    |}
    |
    |class NamedPointer extends Pointer {
    |    string name
    |}
    |
    |class Value extends Pointable {
    |    int value
    |}
    """.trimMargin()

  protected open val environmentDeclarations: List<String>
    get() =
      listOf("contains NamedPointer[] pointers") +
        variables.map { "${it.type.refineryType} ${it.name}" }

  protected val environmentSetup: String
    get() =
      """
    |class Environment {
    |    ${environmentDeclarations.joinToString("\n    ")}
    |}
    |
    |scope Environment = 1.
    |
    |Environment($ENVIRONMENT).
    |atom $ENVIRONMENT.
    """.trimMargin()

  protected val regionExists: String =
    """
    |pred regionExists(MemoryRegion region, int address) <->
    |    exists(region), address(region) == address.
    """.trimMargin()

  protected abstract val transitionDeclarations: List<String>

  protected val transitions: String
    get() =
      transitionDeclarations.joinToString("\n\n")

  protected val topLevelDeclaration: List<String>
    get() =
      listOf(metamodel, environmentSetup, transitions)

  protected val Type.refineryType: String
    get() =
      when (this) {
        is BoolType -> "boolean"
        is IntType -> "int"
        else -> error("Unsupported type in RefineryTransformationSystemBuilder: $this")
      }

  open fun build(): String =
    topLevelDeclaration.joinToString("\n\n")
}

data class RefineryRule(
  val header: String,
  val parameters: List<String> = listOf(),
  val preConditionClauses: List<String>,
  val actionClauses: List<String>,
) {

  init {
    check(actionClauses.isNotEmpty()) { "Action clauses cannot be empty in a Refinery rule." }
  }

  override fun toString(): String =
    """
    |rule $header(${parameters.joinToString(", ")}) <->
    |    ${
      if (preConditionClauses.isEmpty()) "true"
      else preConditionClauses.joinToString(",\n    ")
    }
    |==>
    |    ${actionClauses.joinToString(",\n    ")}.
    """.trimMargin()
}

abstract class RefineryTransitionRuleBuilder<T>(
  protected val variables: MutableSet<Decl<*>>,
  protected val pointers: Set<Decl<*>>,
) {

  protected data class RefineryRuleData(
    val name: String,
    val parameters: List<String> = listOf(),
    val preConditionClauses: List<String>,
    val actionClauses: List<String>,
  ) {

    fun toRefineryRule(): RefineryRule =
      RefineryRule(
        header = name,
        parameters = parameters,
        preConditionClauses = preConditionClauses,
        actionClauses = actionClauses,
      )
  }

  private var transitionCount: Int = 0
  private var dereferenceCount: Int = 0

  abstract fun build(transition: T): List<RefineryRule>

  protected fun Stmt.toRules(transitionName: String): List<RefineryRuleData> {
    dereferenceCount = 0
    return when (this) {
      is SequenceStmt -> stmts.flatMap { it.toRules(transitionName) }

      is AssignStmt<*> -> {
        if (varDecl in pointers) {
          when (val expr = expr) {
            is RefExpr<*> -> {
              val other = expr.decl
              check(other in pointers) { "Pointer assigned from non-pointer variable: $other" }
              val parameters = listOf("NamedPointer pointer", "MemoryObject object")
              val preconditions = listOf(
                "name(pointer) == \"${varDecl.name}\"",
                "name(otherPointer) == \"${other.name}\"",
                "target(otherPointer, object)",
              )
              val actions = listOf("target(pointer, object)")
              val rule = RefineryRuleData(
                name = "${transitionName}_${transitionCount++}",
                parameters = parameters,
                preConditionClauses = preconditions,
                actionClauses = actions,
              )
              listOf(rule)
            }

            is IntLitExpr -> {
              val parametersRegionExists = listOf("NamedPointer pointer", "MemoryObject base")
              val preconditionsRegionExists = listOf(
                "name(pointer) == \"${varDecl.name}\"",
                "regionExists(region, ${expr.value})",
                "parts(region, base)",
                "offset(base) == 0",
              )
              val actionsRegionExists = listOf("target(pointer, base)")
              val ruleIfRegionExists = RefineryRuleData(
                name = "${transitionName}_${transitionCount++}",
                parameters = parametersRegionExists,
                preConditionClauses = preconditionsRegionExists,
                actionClauses = actionsRegionExists,
              )

              val parametersRegionNotExists = listOf("NamedPointer pointer", "MemoryRegion region", "MemoryObject base")
              val preconditionsRegionNotExists = listOf(
                "name(pointer) == \"${varDecl.name}\"",
                "!regionExists(region, ${expr.value})",
              )
              val actionsRegionNotExists = listOf(
                "exists(region)",
                "address(region) == ${expr.value}",
                "parts(region, base)",
                "offset(base) == 0",
                "target(pointer, base)",
              )
              val ruleIfRegionNotExists = RefineryRuleData(
                name = "${transitionName}_${transitionCount++}",
                parameters = parametersRegionNotExists,
                preConditionClauses = preconditionsRegionNotExists,
                actionClauses = actionsRegionNotExists,
              )

              listOf(ruleIfRegionExists, ruleIfRegionNotExists)
            }

            else -> error("Unsupported pointer assignment expression in RefineryRuleBuilder: $this")
          }
        } else {
          variables.add(varDecl)
          val preConditionClauses = mutableListOf<String>()
          val assignedExpr = expr.toClauses(preConditionClauses)
          val rule = RefineryRuleData(
            name = "${transitionName}_${transitionCount++}",
            preConditionClauses = preConditionClauses,
            actionClauses = listOf("${varDecl.name}($ENVIRONMENT): $assignedExpr"),
          )
          listOf(rule)
        }
      }

      is AssumeStmt -> {
        val preConditionClauses = mutableListOf<String>()
        val conditionExpr = cond.toClauses(preConditionClauses)
        val rule = RefineryRuleData(
          name = "${transitionName}_${transitionCount++}",
          preConditionClauses = preConditionClauses + listOf(conditionExpr),
          actionClauses = emptyList(),
        )
        listOf(rule)
      }

      is MemoryAssignStmt<*, *, *> -> {
        val preConditionClauses = mutableListOf<String>()
        val referencedValue = deref.toClauses(preConditionClauses)
        val rule = RefineryRuleData(
          name = "${transitionName}_${transitionCount++}",
          parameters = listOf("MemoryObject ${referencedValue.removePrefix("value(").removeSuffix(")")}"),
          preConditionClauses = preConditionClauses,
          actionClauses = listOf("$referencedValue: ${expr.toClauses(mutableListOf())}"),
        )
        listOf(rule)
      }

      is SkipStmt -> {
        val rule = RefineryRuleData(
          name = "${transitionName}_${transitionCount++}",
          preConditionClauses = listOf(),
          actionClauses = listOf(),
        )
        listOf(rule)
      }

      else -> error("Unsupported statement in RefineryRuleBuilder: $this")
    }
  }

  private fun Expr<*>.toClauses(additionalClauses: MutableList<String>): String =
    when (this) {
      is LitExpr<*> ->
        when (this) {
          is BoolLitExpr -> if (value) "true" else "false"
          is IntLitExpr -> value.toString()
          else -> error("Unsupported literal expression in RefineryRuleBuilder: $this")
        }

      is RefExpr<*> -> {
        variables.add(decl)
        "${decl.name}($ENVIRONMENT)"
      }

      is Dereference<*, *, *> -> {
        val derefCount = dereferenceCount++
        val pointer = "pointer_${derefCount}"
        val base = "base_${derefCount}"
        val region = "region_${derefCount}"
        var referenced = "referenced_${derefCount}"

        when (val array = this.array) {
          is RefExpr<*> -> {
            check(array.decl in pointers) { "Non-pointer variable dereferenced: ${array.decl}" }
            additionalClauses.add("name($pointer) == \"${array.decl.name}\"")
          }

          is Dereference<*, *, *> -> {
            val referencedValue = array.toClauses(additionalClauses)
            val referencedMemoryObject = referencedValue.removePrefix("value(").removeSuffix(")")
            additionalClauses.add("object($referencedMemoryObject, $pointer)")
          }

          else -> error("Unsupported array expression in Dereference: $array")
        }
        additionalClauses.add("target($pointer, $base)")

        when {
          this.offset == Int(0) -> {
            referenced = base
          }

          this.offset.type == Int() -> {
            additionalClauses.add("parts($region, $base)")
            additionalClauses.add("parts($region, $referenced)")
            val offset = this.offset.toClauses(additionalClauses)
            additionalClauses.add("offset($referenced) == offset($base) + ($offset)")
          }

          else -> error("Unsupported offset expression in Dereference: ${this.offset}")
        }

        "value($referenced)"
      }

      is NegExpr<*> -> "- (${op})"
      is AddExpr<*> -> toClauses(additionalClauses, "+")
      is MulExpr<*> -> toClauses(additionalClauses, "*")
      is AndExpr -> toClauses(additionalClauses, "&&")
      is OrExpr -> toClauses(additionalClauses, "||")

      is NotExpr -> {
        val inner = op.toClauses(additionalClauses)
        "!($inner)"
      }

      is EqExpr<*> -> {
        val l = leftOp.toClauses(additionalClauses)
        val r = rightOp.toClauses(additionalClauses)
        "$l == $r"
      }

      is NeqExpr<*> -> {
        val l = leftOp.toClauses(additionalClauses)
        val r = rightOp.toClauses(additionalClauses)
        "$l != $r"
      }

      else -> error("Unsupported expression in RefineryRuleBuilder: $this")
    }

  private fun MultiaryExpr<*, *>.toClauses(additionalClauses: MutableList<String>, operator: String): String =
    ops.joinToString(" $operator ") { it.toClauses(additionalClauses) }
}