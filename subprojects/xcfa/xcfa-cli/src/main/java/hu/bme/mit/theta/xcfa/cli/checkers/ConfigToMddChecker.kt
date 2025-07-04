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
package hu.bme.mit.theta.xcfa.cli.checkers

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.createMonolithicL2S
import hu.bme.mit.theta.analysis.algorithm.bounded.createReversed
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker
import hu.bme.mit.theta.analysis.algorithm.mdd.MddValuationCollector
import hu.bme.mit.theta.analysis.algorithm.mdd.varordering.orderVarsFromRandomStartingPoints
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.IndexedConstDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.utils.LocationInvariants
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import kotlin.jvm.optionals.getOrNull

fun getMddChecker(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  config: XcfaConfig<*, *>,
  logger: Logger,
): SafetyChecker<LocationInvariants, Trace<ExprState, ExprAction>, UnitPrec> {
  val mddConfig = config.backendConfig.specConfig as MddConfig

  val refinementSolverFactory: SolverFactory = getSolver(mddConfig.solver, mddConfig.validateSolver)

  val monExprResult = xcfa.toMonolithicExpr(parseContext, initValues = true)
  val monolithicExpr =
    monExprResult.monolithicExpr
      .let {
        if (config.inputConfig.property == ErrorDetection.TERMINATION)
          it.copy(propExpr = True()).createMonolithicL2S()
        else it
      }
      .let {
        if (mddConfig.cegar) {
          TODO("MDD cannot return traces, and thus, --cegar won't work yet.")
        } else it
      }
      .let { if (mddConfig.reversed) it.createReversed() else it }

  val stmts =
    xcfa.procedures
      .flatMap { it.edges.flatMap { xcfaEdge -> xcfaEdge.getFlatLabels().map { it.toStmt() } } }
      .toSet()
  val variableOrder = orderVarsFromRandomStartingPoints(monolithicExpr.vars, stmts, 20)
  val solverPool = SolverPool(refinementSolverFactory)
  val iterationStrategy = mddConfig.iterationStrategy

  val checker =
    MddChecker.create<ExprState, ExprAction>(
      monolithicExpr,
      variableOrder,
      solverPool,
      logger,
      iterationStrategy,
      monolithicExpr.valToState,
      monolithicExpr.biValToAction,
    )
  return SafetyChecker<LocationInvariants, Trace<ExprState, ExprAction>, UnitPrec> { input ->
    val result = checker.check(input)
    if (result.isUnsafe) {
      SafetyResult.unsafe(result.asUnsafe().cex, LocationInvariants())
    } else {
      val stateSpace = result.proof.mdd
      val vals = MddValuationCollector.collect(stateSpace)

      val reverseLocMap = monExprResult.locMap.reverseMapping()

      val locInvariants = LinkedHashMap<XcfaLocation, MutableSet<ImmutableValuation>>()

      val locVar = monolithicExpr.ctrlVars.first { it.name == "__loc_" }
      vals.map { constValuation ->
        val valuation =
          ImmutableValuation.from(
            constValuation
              .toMap()
              .mapNotNull {
                val const = it.key as IndexedConstDecl<*>
                if (const.index == 0) {
                  Pair(const.varDecl, it.value)
                } else {
                  null
                }
              }
              .toMap()
          )
        val locLit =
          valuation.toMap()[locVar] ?: error("Location var not found in valuation: $locVar")
        val value =
          when (locLit.type) {
            is BvType -> {
              locLit as BvLitExpr
              BvUtils.neutralBvLitExprToBigInteger(locLit)
            }

            is IntType -> {
              locLit as IntLitExpr
              locLit.value
            }

            else -> {
              error("Value type unexpected: $locVar")
            }
          }
        val location =
          reverseLocMap[value.toInt()] ?: error("Location not found for literal: ${value.toInt()}")

        locInvariants.computeIfAbsent(location) { LinkedHashSet() }.add(valuation)
      }

      val stats = result.stats.getOrNull()
      stats?.keySet()?.forEach { key -> logger.writeln(Logger.Level.INFO, "$key: ${stats[key]}") }
      SafetyResult.safe(
        LocationInvariants(
          locInvariants.map { Pair(it.key, it.value.map { ExplState.of(it) }) }.toMap()
        )
      )
    }
  }
}
