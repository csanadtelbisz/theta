/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.bounded

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.cegar.RefinerResult
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.Refutation
import hu.bme.mit.theta.analysis.expr.refinement.SingleExprTraceRefiner
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.utils.WithPushPop

class AbstractKind<S : ExprState, A : ExprAction, P : Prec, R : Refutation> @JvmOverloads constructor(
    private val monolithicExpr: MonolithicExpr,
    private val shouldGiveUp: (Int) -> Boolean = { false },
    private val bmcSolver: Solver? = null,
    private val bmcEnabled: () -> Boolean = { true },
    private val lfPathOnly: () -> Boolean = { true },
    private val indSolver: Solver? = null,
    private val kindEnabled: (Int) -> Boolean = { true },
    private val stateExprHandler: StateExprHandler<S, P>,
    private val biValToAction: (Valuation, Valuation) -> A,
    private val initPrec: P,
    private val refiner: SingleExprTraceRefiner<S, A, P, R>,
    private val logger: Logger,
) : SafetyChecker<S, A, P> {

    private val vars = monolithicExpr.vars()
    private val unfoldedInitExpr = PathUtils.unfold(monolithicExpr.initExpr, 0)
    private val unfoldedPropExpr = { i: VarIndexing -> PathUtils.unfold(monolithicExpr.propExpr, i) }
    private val indices = mutableListOf(VarIndexingFactory.indexing(0))
    private val exprs = mutableListOf<Expr<BoolType>>()
    private val stateList = mutableListOf<Pair<VarIndexing, VarIndexing>>()
    private var kindLastIterLookup = 0
    private var lastPrec: P? = null

    init {
        check(bmcSolver != indSolver || bmcSolver == null) { "Use distinct solvers for BMC and KInd!" }
    }

    override fun check() = check(initPrec)

    override fun check(initPrec: P): SafetyResult<S, A> {
        var iteration = 0
        var prec = initPrec
        bmcSolver?.add(unfoldedInitExpr)
        while (!shouldGiveUp(iteration)) {
            iteration++
            logger.write(Logger.Level.MAINSTEP, "Starting iteration $iteration\n")
            val (result, refinedPrec) = cegar(prec, iteration)
            prec = refinedPrec
            if (result.isSafe || result.isUnsafe) return result
        }
        return SafetyResult.unknown()
    }

    private fun cegar(initPrec: P, iteration: Int): Pair<SafetyResult<S, A>, P> {
        var abstractorResult: SafetyResult<S, A>?
        var refinerResult: RefinerResult<S, A, P>? = null
        var prec = initPrec
        do {
            logger.write(Logger.Level.MAINSTEP, "CEGAR iteration%n")
            logger.write(Logger.Level.MAINSTEP, "| Checking abstraction...%n")
            logger.write(Logger.Level.MAINSTEP, "| Precision: %s%n", prec)
            abstractorResult = boundedCheck(prec, iteration)
            lastPrec = prec
            logger.write(Logger.Level.MAINSTEP, "| Checking abstraction done, result: %s%n", abstractorResult)

            if (abstractorResult.isUnsafe) {
                logger.write(Logger.Level.MAINSTEP, "| Refining abstraction...%n")
                refinerResult = refiner.refine(abstractorResult.asUnsafe().trace, prec)
                logger.write(Logger.Level.MAINSTEP, "Refining abstraction done, result: %s%n", refinerResult)

                if (refinerResult.isSpurious()) {
                    prec = refinerResult.asSpurious().refinedPrec
                    if (prec == lastPrec) {
                        logger.write(Logger.Level.MAINSTEP, "Precision could not be refined.%n")
                        break
                    }
                }
            }
        } while (abstractorResult!!.isUnsafe && !refinerResult!!.isUnsafe)

        val cegarResult = when {
            abstractorResult!!.isSafe -> SafetyResult.safe() // safety proven by BMC/KInd with the current abstraction
            !abstractorResult.isUnsafe -> SafetyResult.unknown() // no counterexample found, no safety proven
            refinerResult!!.isUnsafe -> SafetyResult.unsafe(refinerResult.asUnsafe().cex) // counterexample found by BMC
            else -> error("Precision could not be refined while spurious counterexample is found.")
        }
        return cegarResult to prec
    }

    private fun boundedCheck(prec: P, iteration: Int): SafetyResult<S, A> {
        if (lastPrec != prec) {
            stateList.forEach { (indexing1, indexing2) ->
                val eq = stateExprHandler.equivalent(indexing1, indexing2, prec, lastPrec)
                bmcSolver?.add(eq)
                indSolver?.add(eq)
                val stateExpr = stateExprHandler.stateToExpr(indexing1, prec, lastPrec)
                stateExpr?.let { bmcSolver?.add(it) }
            }
        }

        val incomingIndexing = indices.last()
        val outgoingIndexing = incomingIndexing.add(monolithicExpr.offsetIndex)
        indices.add(outgoingIndexing)
        stateList.add(incomingIndexing to outgoingIndexing)

        val eq = stateExprHandler.equivalent(incomingIndexing, outgoingIndexing, prec)
        bmcSolver?.add(eq)
        indSolver?.add(eq)
        val stateExpr = stateExprHandler.stateToExpr(incomingIndexing, prec, lastPrec)
        stateExpr?.let { bmcSolver?.add(it) }

        exprs.add(PathUtils.unfold(monolithicExpr.transExpr, outgoingIndexing))
        indices.add(indices.last().add(monolithicExpr.offsetIndex))

        if (bmcEnabled()) { // we don't allow per-iteration setting of bmc enabledness
            bmc(prec)?.let { return it }
        }

        if (kindEnabled(iteration)) {
            if (!bmcEnabled()) {
                error("Bad configuration: induction check should always be preceded by a BMC/SAT check")
            }
            kind(prec)?.let { return it }
            kindLastIterLookup = iteration
        }
        return SafetyResult.unknown()
    }

    private fun bmc(prec: P): SafetyResult<S, A>? {
        val bmcSolver = this.bmcSolver!!
        logger.write(Logger.Level.MAINSTEP, "\tStarting BMC...\n")

        bmcSolver.add(exprs.last())

        return WithPushPop(bmcSolver).use {
            if (lfPathOnly()) {
                val states = stateList.map { it.first } + indices.last()
                for (state1 in states)
                    for (state2 in states)
                        if (state1 != state2)
                            bmcSolver.add(Not(stateExprHandler.equivalent(state1, state2, prec)))

                if (bmcSolver.check().isUnsat) {
                    logger.write(Logger.Level.MAINSTEP, "\tSafety proven in BMC step\n")
                    return SafetyResult.safe()
                }
            }

            bmcSolver.add(Not(unfoldedPropExpr(indices.last())))

            if (bmcSolver.check().isSat) {
                val trace = getTrace(bmcSolver.model, prec)
                logger.write(Logger.Level.MAINSTEP, "\tAbstract CeX found in BMC step (length ${trace.length()})\n")
                SafetyResult.unsafe(trace)
            } else null
        }
    }

    private fun kind(prec: P): SafetyResult<S, A>? {
        val indSolver = this.indSolver!!

        logger.write(Logger.Level.MAINSTEP, "\tStarting k-induction...\n")

        exprs.subList(kindLastIterLookup, exprs.size).forEach { indSolver.add(it) }
        indices.subList(kindLastIterLookup, indices.size - 1).forEach { indSolver.add(unfoldedPropExpr(it)) }

        return WithPushPop(indSolver).use {
            indSolver.add(Not(unfoldedPropExpr(indices.last())))

            if (lfPathOnly()) {
                val states = stateList.map { it.first } + indices.last()
                for (state1 in states)
                    for (state2 in states)
                        if (state1 != state2)
                            indSolver.add(Not(stateExprHandler.equivalent(state1, state2, prec)))
            }

            if (indSolver.check().isUnsat) {
                logger.write(Logger.Level.MAINSTEP, "\tSafety proven in k-induction step\n")
                SafetyResult.safe()
            } else null
        }
    }

    private fun getTrace(model: Valuation, prec: P): Trace<S, A> {
        val states = mutableListOf<S>()
        val actions = mutableListOf<A>()
        var lastValuation: Valuation? = null
        for (state in stateList.map { it.first } + indices.last()) {
            val valuation = PathUtils.extractValuation(model, state, vars)
            states.add(stateExprHandler.valToState(model, state, valuation, prec))
            if (lastValuation != null) {
                actions.add(biValToAction(lastValuation, valuation))
            }
            lastValuation = valuation
        }
        return Trace.of(states, actions)
    }
}
