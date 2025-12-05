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

import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionSystemBuilder.Companion.ENVIRONMENT
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.MultiaryExpr
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.abstracttype.ModExpr
import hu.bme.mit.theta.core.type.abstracttype.MulExpr
import hu.bme.mit.theta.core.type.abstracttype.NegExpr
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr

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

  protected data class ExprWithParameters(
    val expr: String,
    val parameters: Set<String> = setOf(),
  )

  protected data class ExprsWithParameters(
    val nonPointerExprWithParameters: ExprWithParameters? = null,
    val pointerExprWithParameters: ExprWithParameters? = null,
  ) {

    constructor(
      nonPointerExpr: String? = null,
      pointerExpr: String? = null,
      nonPointerExprParameters: Set<String> = setOf(),
      pointerExprParameters: Set<String> = setOf(),
    ) : this(
      nonPointerExprWithParameters =
        nonPointerExpr?.let { ExprWithParameters(it, nonPointerExprParameters) },
      pointerExprWithParameters =
        pointerExpr?.let { ExprWithParameters(it, pointerExprParameters) },
    )

    val nonPointerExpr: String?
      get() = nonPointerExprWithParameters?.expr

    val pointerExpr: String?
      get() = pointerExprWithParameters?.expr
  }

  private var transitionCounter: Int = 0
  private var dereferenceCounter: Int = 0
  private var pointerArithmeticCounter: Int = 0
  private var pointerComparisonCounter: Int = 0

  private fun getName(name: String) = "${name}_${transitionCounter++}"

  abstract fun build(transition: T): List<RefineryRule>

  protected fun Stmt.toRules(transitionName: String): List<RefineryRuleData> {
    dereferenceCounter = 0
    pointerArithmeticCounter = 0
    pointerComparisonCounter = 0
    return when (this) {
      is SequenceStmt -> stmts.flatMap { it.toRules(transitionName) }

      is AssignStmt<*> -> {
        if (varDecl in pointers) {
          val commonPreconditions = mutableListOf("name(assigned_pointer) == \"${varDecl.name}\"")
          val (nonPointerExpr, pointerExpr) = expr.toClauses(commonPreconditions)
          check(nonPointerExpr == null || pointerExpr == null) {
            "Expression of assignment $this cannot be interpreted as both pointer and non-pointer assignment."
          }

          when {
            pointerExpr != null -> {
              val parameters = listOf("NamedPointer assigned_pointer", "MemoryObject object")
              val preconditions = listOf(
                "target(${pointerExpr.expr}, object)",
              )
              val actions = listOf("target(assigned_pointer, object)")
              val rule = RefineryRuleData(
                name = getName(transitionName),
                parameters = parameters,
                preConditionClauses = commonPreconditions + preconditions,
                actionClauses = actions,
              )
              listOf(rule)
            }

            nonPointerExpr != null -> {
              commonPreconditions.add("Value(address)")
              commonPreconditions.add("value(address) == ${nonPointerExpr.expr}")

              val parametersRegionExists = listOf("NamedPointer pointer", "MemoryObject base")
              val preconditionsRegionExists = listOf(
                "regionExists(region, address)",
                "parts(region, base)",
                "offset(base) == 0",
              )
              val actionsRegionExists = listOf("target(pointer, base)")
              val ruleIfRegionExists = RefineryRuleData(
                name = getName(transitionName),
                parameters = parametersRegionExists,
                preConditionClauses = commonPreconditions + preconditionsRegionExists,
                actionClauses = actionsRegionExists,
              )

              val parametersRegionNotExists = listOf("NamedPointer pointer", "MemoryRegion region", "MemoryObject base")
              val preconditionsRegionNotExists = listOf(
                "!regionExists(region, address)",
              )
              val actionsRegionNotExists = listOf(
                "exists(region)",
                "address(region, address)",
                "exists(base)",
                "parts(region, base)",
                "offset(base): 0",
                "target(pointer, base)",
              )
              val ruleIfRegionNotExists = RefineryRuleData(
                name = getName(transitionName),
                parameters = parametersRegionNotExists,
                preConditionClauses = commonPreconditions + preconditionsRegionNotExists,
                actionClauses = actionsRegionNotExists,
              )

              listOf(ruleIfRegionExists, ruleIfRegionNotExists)
            }

            else -> error("Either a pointer or a non-pointer expression is expected at assignment $this.")
          }
        } else {
          variables.add(varDecl)
          val preConditionClauses = mutableListOf<String>()
          val (assignedExpr, parameters) = expr.getNonPointerExpr(preConditionClauses, this)
          val rule = RefineryRuleData(
            name = getName(transitionName),
            parameters = parameters.toList(),
            preConditionClauses = preConditionClauses,
            actionClauses = listOf("${varDecl.name}($ENVIRONMENT): $assignedExpr"),
          )
          listOf(rule)
        }
      }

      is AssumeStmt -> {
        val preConditionClauses = mutableListOf<String>()
        val conditionExpr = cond.getNonPointerExpr(preConditionClauses, this).expr
        val rule = RefineryRuleData(
          name = getName(transitionName),
          preConditionClauses = preConditionClauses + listOf(conditionExpr),
          actionClauses = emptyList(),
        )
        listOf(rule)
      }

      is MemoryAssignStmt<*, *, *> -> {
        val preConditionClauses = mutableListOf<String>()
        val (referencedNonPointer, referencedPointer) = deref.toClauses(preConditionClauses)
        val (nonPointerExpr, pointerExpr) = expr.toClauses(preConditionClauses)
        check(nonPointerExpr == null || pointerExpr == null) {
          "Expression of assignment $this cannot be interpreted as both pointer and non-pointer assignment."
        }

        when {
          pointerExpr != null -> {
            val referenced = referencedPointer!!.expr
            val target = pointerExpr.expr
            val rule = RefineryRuleData(
              name = getName(transitionName),
              parameters = listOf("MemoryObject $referenced", "Pointer $target"),
              preConditionClauses = preConditionClauses,
              actionClauses = listOf("target($referenced, $target)"),
            )
            listOf(rule)
          }

          nonPointerExpr != null -> {
            val assignedExpr = nonPointerExpr.expr
            val assignedExprParams = nonPointerExpr.parameters
            val parameters = setOf("Value ${referencedPointer!!.expr}") + assignedExprParams
            val rule = RefineryRuleData(
              name = getName(transitionName),
              parameters = parameters.toList(),
              preConditionClauses = preConditionClauses,
              actionClauses = listOf("${referencedNonPointer!!.expr}: $assignedExpr"),
            )
            listOf(rule)
          }

          else -> error("Either a pointer or a non-pointer expression is expected at memory assignment $this.")
        }
      }

      is SkipStmt -> {
        val rule = RefineryRuleData(
          name = getName(transitionName),
          preConditionClauses = listOf(),
          actionClauses = listOf(),
        )
        listOf(rule)
      }

      else -> error("Unsupported statement in RefineryRuleBuilder: $this")
    }
  }

  /**
   * Converts an expression to Refinery clauses.
   *
   * @param additionalClauses A mutable list to which additional clauses can be added.
   * @return A pair containing the value of the expression as a non-pointer expression (if applicable)
   *         and the value of the expression as a pointer expression (if applicable).
   */
  private fun Expr<*>.toClauses(additionalClauses: MutableList<String>): ExprsWithParameters =
    when (this) {
      is LitExpr<*> ->
        ExprsWithParameters(
          nonPointerExpr =
            when (this) {
              is BoolLitExpr -> if (value) "true" else "false"
              is IntLitExpr -> value.toString()
              else -> error("Unsupported literal expression in RefineryRuleBuilder: $this")
            }
        )

      is RefExpr<*> -> {
        if (decl in pointers) {
          additionalClauses.add("name(${decl.name}) == \"${decl.name}\"")
          ExprsWithParameters(
            pointerExpr = decl.name,
            pointerExprParameters = setOf("NamedPointer ${decl.name}")
          )
        } else {
          variables.add(decl)
          ExprsWithParameters(nonPointerExpr = "${decl.name}($ENVIRONMENT)")
        }
      }

      is Dereference<*, *, *> -> {
        val derefCount = dereferenceCounter++
        val base = "base_${derefCount}"
        val region = "region_${derefCount}"
        var referenced = "referenced_${derefCount}"
        val pointed = "pointed_${derefCount}"

        val (basePointer, _) = array.getPointerExpr(additionalClauses, this)
        additionalClauses.add("target($basePointer, $base)")

        when {
          offset == Int(0) -> {
            referenced = base
          }

          offset.type == Int() -> {
            additionalClauses.add("parts($region, $base)")
            additionalClauses.add("parts($region, $referenced)")
            val (offset, _) = offset.getNonPointerExpr(additionalClauses, this)
            additionalClauses.add("offset($referenced) == offset($base) + ($offset)")
          }

          else -> error("Unsupported offset expression in Dereference: ${this.offset}")
        }
        additionalClauses.add("object($referenced, $pointed)")

        ExprsWithParameters(
          nonPointerExpr = "value($pointed)",
          nonPointerExprParameters = setOf("Value $pointed"),
          pointerExpr = pointed,
          pointerExprParameters = setOf("Pointer $pointed"),
        )
      }

      is AddExpr<*> -> {
        val ops = ops.map { it.toClauses(additionalClauses) }

        val nonPointerExprWithParams =
          if (ops.any { it.nonPointerExpr == null }) null
          else {
            val nonPointerOps = ops.map { it.nonPointerExprWithParameters!! }
            val nonPointerExpr = nonPointerOps.map { it.expr }.join("+")
            val nonPointerParams = nonPointerOps.flatMap { it.parameters }.toSet()
            ExprWithParameters(nonPointerExpr, nonPointerParams)
          }

        val pointerExprSupported = ops.count { it.pointerExpr != null } == 1
        val pointerExprWithParams =
          if (pointerExprSupported) {
            val pointerOp = ops.first { it.pointerExpr != null }.pointerExprWithParameters!!
            val pointer = pointerOp.expr
            val pointerParams = pointerOp.parameters
            val nonPointerOps = ops.filter { it.pointerExpr == null }.map { it.nonPointerExprWithParameters!! }
            val nonPointerSum = nonPointerOps.map { it.expr }.join("+")
            val nonPointerParams = nonPointerOps.flatMap { it.parameters }.toSet()
            val pointerArithmeticCount = pointerArithmeticCounter++
            val base = "ptr_arith_base_${pointerArithmeticCount}"
            val region = "ptr_arith_region_${pointerArithmeticCount}"
            val referenced = "ptr_arith_referenced_${pointerArithmeticCount}"
            additionalClauses.add("target($pointer, $base)")
            additionalClauses.add("parts($region, $base)")
            additionalClauses.add("parts($region, $referenced)")
            additionalClauses.add("offset($referenced) == offset($base) + ($nonPointerSum)")
            ExprWithParameters(referenced, pointerParams + nonPointerParams)
          } else null

        ExprsWithParameters(
          nonPointerExprWithParameters = nonPointerExprWithParams,
          pointerExprWithParameters = pointerExprWithParams,
        )
      }

      is NegExpr<*> -> {
        val (innerExpr, innerParams) = op.getNonPointerExpr(additionalClauses, this)
        ExprsWithParameters(
          nonPointerExpr = "- ($innerExpr)",
          nonPointerExprParameters = innerParams,
        )
      }

      is ModExpr<*> -> {
        val (lExpr, lParams) = leftOp.getNonPointerExpr(additionalClauses, this)
        val (rExpr, rParams) = rightOp.getNonPointerExpr(additionalClauses, this)
        ExprsWithParameters(
          // No mod operator in Refinery
          nonPointerExpr = "($lExpr) - ((($lExpr) / ($rExpr)) * ($rExpr))",
          nonPointerExprParameters = lParams + rParams
        )
      }

      is MulExpr<*> -> toNonPointerClauses(additionalClauses, "*")
      is AndExpr -> toNonPointerClauses(additionalClauses, "&&")
      is OrExpr -> toNonPointerClauses(additionalClauses, "||")
      is NotExpr -> {
        val (innerExpr, innerParams) = op.getNonPointerExpr(additionalClauses, this)
        ExprsWithParameters(
          nonPointerExpr = "!($innerExpr)",
          nonPointerExprParameters = innerParams
        )
      }

      is EqExpr<*> -> equalityCheck(additionalClauses, "==")
      is NeqExpr<*> -> equalityCheck(additionalClauses, "!=")

      else -> error("Unsupported expression in RefineryRuleBuilder: $this")
    }.let { result: ExprsWithParameters ->
      check(result.nonPointerExpr != null || result.pointerExpr != null) {
        "At least a non-pointer or a pointer expression must be yielded, none is yielded at $this"
      }
      result
    }

  private fun MultiaryExpr<*, *>.toNonPointerClauses(
    additionalClauses: MutableList<String>,
    operator: String,
  ): ExprsWithParameters =
    ops
      .map { it.getNonPointerExpr(additionalClauses, this) }
      .let {
        ExprsWithParameters(
          nonPointerExprWithParameters =
            ExprWithParameters(
              expr = it.map { ewp -> ewp.expr }.join(operator),
              parameters = it.flatMap { ewp -> ewp.parameters }.toSet(),
            )
        )
      }

  private fun List<String>.join(operator: String): String =
    this.joinToString(" $operator ") { "($it)" }

  private fun Expr<*>.getNonPointerExpr(additionalClauses: MutableList<String>, parent: Any): ExprWithParameters =
    this.toClauses(additionalClauses).nonPointerExprWithParameters
      ?: error("Non-pointer expression expected at $parent, expression $this does not yield a non-pointer expression.")

  private fun Expr<*>.getPointerExpr(additionalClauses: MutableList<String>, parent: Any): ExprWithParameters =
    this.toClauses(additionalClauses).pointerExprWithParameters
      ?: error("Pointer expression expected at $parent, expression $this does not yield a pointer expression.")

  private fun BinaryExpr<*, *>.equalityCheck(
    additionalClauses: MutableList<String>,
    operator: String
  ): ExprsWithParameters {
    val (lNonPointer, lPointer) = leftOp.toClauses(additionalClauses)
    val (rNonPointer, rPointer) = rightOp.toClauses(additionalClauses)

    val nonPointer =
      if (lNonPointer != null && rNonPointer != null) {
        ExprWithParameters(
          expr = "${lNonPointer.expr} $operator ${rNonPointer.expr}",
          parameters = lNonPointer.parameters + rNonPointer.parameters,
        )
      } else null

    val pointer =
      if (lPointer != null && rPointer != null) {
        val pointerComparisonCount = pointerComparisonCounter++
        val lTarget = "pointer_comp_target_left_${pointerComparisonCount}"
        val rTarget = "pointer_comp_target_right_${pointerComparisonCount}"
        additionalClauses.add("target(${lPointer.expr}, $lTarget)")
        additionalClauses.add("target(${rPointer.expr}, $rTarget)")
        ExprWithParameters(
          expr = "$lTarget $operator $rTarget",
          parameters = lPointer.parameters + rPointer.parameters,
        )
      } else null

    check(nonPointer == null || pointer == null) {
      "Equality cannot be interpreted as both pointer and non-pointer comparison at $this"
    }

    return ExprsWithParameters(nonPointerExprWithParameters = (nonPointer ?: pointer))
  }
}