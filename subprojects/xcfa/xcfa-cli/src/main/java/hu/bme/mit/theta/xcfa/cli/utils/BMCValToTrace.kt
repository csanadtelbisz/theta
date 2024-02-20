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

package hu.bme.mit.theta.xcfa.cli.utils

import hu.bme.mit.theta.analysis.algorithm.bounded.ExplStateExprHandler
import hu.bme.mit.theta.analysis.algorithm.bounded.PredStateExprHandler
import hu.bme.mit.theta.analysis.algorithm.bounded.StateExprHandler
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaProcessState
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.util.*

fun valToAction(xcfa: XCFA, val1: Valuation, val2: Valuation): XcfaAction {
    val val1Map = val1.toMap()
    val val2Map = val2.toMap()
    var i = 0
    val map: MutableMap<XcfaLocation, Int> = HashMap()
    for (x in xcfa.procedures.first { it.name == "main" }.locs) {
        map[x] = i++
    }
    return XcfaAction(
        pid = 0,
        edge = xcfa.procedures.first { it.name == "main" }.edges.first { edge ->
            map[edge.source] == (val1Map[val1Map.keys.first { it.name == "__loc_" }] as IntLitExpr).value.toInt() &&
                map[edge.target] == (val2Map[val2Map.keys.first { it.name == "__loc_" }] as IntLitExpr).value.toInt()
        })
}

fun valToState(valuation: Valuation, xcfa: XCFA): XcfaState<ExplState> {
    val valMap = valuation.toMap()
    var i = 0
    val map: MutableMap<Int, XcfaLocation> = HashMap()
    for (x in xcfa.procedures.first { it.name == "main" }.locs) {
        map[i++] = x
    }
    return XcfaState(
        xcfa = xcfa,
        processes = mapOf(Pair(0, XcfaProcessState(
            locs = LinkedList(
                listOf(map[(valMap[valMap.keys.first { it.name == "__loc_" }] as IntLitExpr).value.toInt()])),
            varLookup = LinkedList(),
        ))),
        ExplState.of(
            ImmutableValuation.from(
                valMap
                    .filter { it.key.name != "__loc_" && !it.key.name.startsWith("__temp_") }
                    .map { Pair(Var("_" + "_" + it.key.name, it.key.type), it.value) }.toMap())),
        mutexes = emptyMap(),
        threadLookup = emptyMap(),
        bottom = false
    )
}

private fun locVarEqAnd(locVar: VarDecl<*>, i1: VarIndexing, i2: VarIndexing, expr: Expr<BoolType>): Expr<BoolType> =
    And(Eq(PathUtils.unfold(locVar.ref, i1), PathUtils.unfold(locVar.ref, i2)), expr)

class XcfaExplStateExprHandler(private val xcfa: XCFA, private val locVar: VarDecl<*>? = null) :
    StateExprHandler<XcfaState<ExplState>, XcfaPrec<ExplPrec>>() {

    private val explStateExprHandler = ExplStateExprHandler()

    override fun valToState(model: Valuation, indexing: VarIndexing, stateValuation: Valuation,
        prec: XcfaPrec<ExplPrec>): XcfaState<ExplState> =
        valToState(ImmutableValuation.from(stateValuation.toMap()
            .filter { (key, _) -> key in (prec.p.vars + locVar) }), xcfa)

    override fun equivalent(i1: VarIndexing, i2: VarIndexing, prec: XcfaPrec<ExplPrec>,
        lastPrec: XcfaPrec<ExplPrec>?): Expr<BoolType> =
        locVarEqAnd(locVar!!, i1, i2, explStateExprHandler.equivalent(i1, i2, prec.p, lastPrec?.p))
}

class XcfaPredStateExprHandler(private val xcfa: XCFA, private val locVar: VarDecl<*>? = null) :
    StateExprHandler<XcfaState<PredState>, XcfaPrec<PredPrec>>() {

    private val predStateExprHandler = PredStateExprHandler()

    override fun valToState(model: Valuation, indexing: VarIndexing, stateValuation: Valuation,
        prec: XcfaPrec<PredPrec>): XcfaState<PredState> {
        val valMap = stateValuation.toMap()
        var i = 0
        val map = mutableMapOf<Int, XcfaLocation>()
        for (x in xcfa.procedures.first { it.name == "main" }.locs) {
            map[i++] = x
        }
        return XcfaState(
            xcfa = xcfa,
            processes = mapOf(Pair(0, XcfaProcessState(
                locs = LinkedList(
                    listOf(map[(valMap[valMap.keys.first { it.name == "__loc_" }] as IntLitExpr).value.toInt()])),
                varLookup = LinkedList(),
            ))),
            sGlobal = predStateExprHandler.valToState(model, indexing, stateValuation, prec.p),
            mutexes = emptyMap(),
            threadLookup = emptyMap(),
            bottom = false
        )
    }

    override fun stateToExpr(indexing: VarIndexing, prec: XcfaPrec<PredPrec>,
        lastPrec: XcfaPrec<PredPrec>?): Expr<BoolType> =
        predStateExprHandler.stateToExpr(indexing, prec.p, lastPrec?.p)

    override fun equivalent(i1: VarIndexing, i2: VarIndexing, prec: XcfaPrec<PredPrec>,
        lastPrec: XcfaPrec<PredPrec>?): Expr<BoolType> =
        locVarEqAnd(locVar!!, i1, i2, predStateExprHandler.equivalent(i1, i2, prec.p, lastPrec?.p))
}
