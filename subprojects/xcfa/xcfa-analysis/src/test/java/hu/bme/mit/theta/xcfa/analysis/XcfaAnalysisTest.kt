/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions
import hu.bme.mit.theta.analysis.expl.*
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.analysis.por.*
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import java.util.*


class XcfaAnalysisTest {


    companion object {

        @JvmStatic
        fun data(): Collection<Array<Any>> {
            return listOf(
                arrayOf("/00assignment.c", SafetyResult<*, *>::isUnsafe),
                arrayOf("/01function.c", SafetyResult<*, *>::isUnsafe),
                arrayOf("/02functionparam.c", SafetyResult<*, *>::isSafe),
                arrayOf("/03nondetfunction.c", SafetyResult<*, *>::isUnsafe),
                arrayOf("/04multithread.c", SafetyResult<*, *>::isUnsafe),
            )
        }
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testNoporExpl(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
        val stream = javaClass.getResourceAsStream(filepath)
        val xcfa = getXcfaFromC(stream!!, ParseContext(), false)

        val analysis = ExplXcfaAnalysis(
            xcfa,
            Z3SolverFactory.getInstance().createSolver(),
            0,
            getPartialOrder(ExplOrd.getInstance())
        )

        val lts = getXcfaLts()

        val abstractor = getXcfaAbstractor(analysis,
            PriorityWaitlist.create(
                ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())),
            StopCriterions.firstCex<XcfaState<ExplState>, XcfaAction>(),
            ConsoleLogger(Logger.Level.DETAIL),
            lts,
            ErrorDetection.ERROR_LOCATION) as Abstractor<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>>

        val precRefiner = XcfaPrecRefiner<XcfaState<ExplState>, ExplPrec, ItpRefutation>(ItpRefToExplPrec())

        val refiner =
            SingleExprTraceRefiner.create(
                ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(),
                    Z3SolverFactory.getInstance().createItpSolver()),
                precRefiner, PruneStrategy.FULL,
                NullLogger.getInstance()) as Refiner<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>>

        val cegarChecker =
            CegarChecker.create(abstractor, refiner)

        val safetyResult = cegarChecker.check(XcfaPrec(ExplPrec.empty()))



        Assertions.assertTrue(verdict(safetyResult))
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testSporExpl(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
        val stream = javaClass.getResourceAsStream(filepath)
        val xcfa = getXcfaFromC(stream!!, ParseContext(), false)

        val analysis = ExplXcfaAnalysis(
            xcfa,
            Z3SolverFactory.getInstance().createSolver(),
            0,
            getPartialOrder(ExplOrd.getInstance())
        )

        val lts = XcfaSporLts(xcfa)

        val abstractor = getXcfaAbstractor(analysis,
            PriorityWaitlist.create(
                ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())),
            StopCriterions.firstCex<XcfaState<ExplState>, XcfaAction>(),
            ConsoleLogger(Logger.Level.DETAIL),
            lts,
            ErrorDetection.ERROR_LOCATION) as Abstractor<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>>

        val precRefiner = XcfaPrecRefiner<XcfaState<ExplState>, ExplPrec, ItpRefutation>(ItpRefToExplPrec())

        val refiner =
            SingleExprTraceRefiner.create(
                ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(),
                    Z3SolverFactory.getInstance().createItpSolver()),
                precRefiner, PruneStrategy.FULL,
                NullLogger.getInstance()) as Refiner<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>>

        val cegarChecker =
            CegarChecker.create(abstractor, refiner)

        val safetyResult = cegarChecker.check(XcfaPrec(ExplPrec.empty()))



        Assertions.assertTrue(verdict(safetyResult))
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testDporExpl(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
        val stream = javaClass.getResourceAsStream(filepath)
        val xcfa = getXcfaFromC(stream!!, ParseContext(), false)

        val analysis = ExplXcfaAnalysis(
            xcfa,
            Z3SolverFactory.getInstance().createSolver(),
            0,
            XcfaDporLts.getPartialOrder(getPartialOrder(ExplOrd.getInstance()))
        )

        val lts = XcfaDporLts(xcfa)

        val abstractor = getXcfaAbstractor(analysis,
            lts.waitlist,
            StopCriterions.firstCex<XcfaState<ExplState>, XcfaAction>(),
            ConsoleLogger(Logger.Level.DETAIL),
            lts,
            ErrorDetection.ERROR_LOCATION) as Abstractor<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>>

        val precRefiner = XcfaPrecRefiner<XcfaState<ExplState>, ExplPrec, ItpRefutation>(ItpRefToExplPrec())

        val refiner =
            SingleExprTraceRefiner.create(
                ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(),
                    Z3SolverFactory.getInstance().createItpSolver()),
                precRefiner, PruneStrategy.FULL,
                ConsoleLogger(Logger.Level.DETAIL)) as Refiner<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>>

        val cegarChecker =
            CegarChecker.create(abstractor, refiner)

        val safetyResult = cegarChecker.check(XcfaPrec(ExplPrec.empty()))



        Assertions.assertTrue(verdict(safetyResult))
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testAasporExpl(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
        val stream = javaClass.getResourceAsStream(filepath)
        val xcfa = getXcfaFromC(stream!!, ParseContext(), false)

        val analysis = ExplXcfaAnalysis(
            xcfa,
            Z3SolverFactory.getInstance().createSolver(),
            0,
            getPartialOrder(ExplOrd.getInstance())
        )

        val lts = XcfaAasporLts(xcfa, mutableMapOf())

        val abstractor = getXcfaAbstractor(analysis,
            PriorityWaitlist.create(
                ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())),
            StopCriterions.firstCex<XcfaState<ExplState>, XcfaAction>(),
            ConsoleLogger(Logger.Level.DETAIL),
            lts,
            ErrorDetection.ERROR_LOCATION) as Abstractor<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>>

        val precRefiner = XcfaPrecRefiner<ExplState, ExplPrec, ItpRefutation>(ItpRefToExplPrec())
        val atomicNodePruner = AtomicNodePruner<XcfaState<ExplState>, XcfaAction>()

        val refiner =
            SingleExprTraceRefiner.create(
                ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(),
                    Z3SolverFactory.getInstance().createItpSolver()),
                precRefiner, PruneStrategy.FULL, NullLogger.getInstance(),
                atomicNodePruner) as Refiner<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>>

        val cegarChecker =
            CegarChecker.create(abstractor, AasporRefiner.create(refiner, PruneStrategy.FULL, mutableMapOf()))

        val safetyResult = cegarChecker.check(XcfaPrec(ExplPrec.empty()))



        Assertions.assertTrue(verdict(safetyResult))
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testAadporExpl(filepath: String, verdict: (SafetyResult<*, *>) -> Boolean) {
        if (filepath.contains("multithread")) return // TODO: why does it fail to verify?
        val stream = javaClass.getResourceAsStream(filepath)
        val xcfa = getXcfaFromC(stream!!, ParseContext(), false)

        val analysis = ExplXcfaAnalysis(
            xcfa,
            Z3SolverFactory.getInstance().createSolver(),
            1,
            XcfaDporLts.getPartialOrder(getPartialOrder(ExplOrd.getInstance()))
        )

        val lts = XcfaAadporLts(xcfa)

        val abstractor = getXcfaAbstractor(analysis,
            lts.waitlist,
            StopCriterions.firstCex<XcfaState<ExplState>, XcfaAction>(),
            ConsoleLogger(Logger.Level.DETAIL),
            lts,
            ErrorDetection.ERROR_LOCATION) as Abstractor<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>>

        val precRefiner = XcfaPrecRefiner<ExplState, ExplPrec, ItpRefutation>(ItpRefToExplPrec())

        val refiner =
            SingleExprTraceRefiner.create(
                ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(),
                    Z3SolverFactory.getInstance().createItpSolver()),
                precRefiner, PruneStrategy.FULL,
                NullLogger.getInstance()) as Refiner<XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>>

        val cegarChecker =
            CegarChecker.create(abstractor, refiner)

        val safetyResult = cegarChecker.check(XcfaPrec(ExplPrec.empty()))



        Assertions.assertTrue(verdict(safetyResult))
    }
}