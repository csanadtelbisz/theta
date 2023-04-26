package hu.bme.mit.theta.xcfa.analysis.por

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.getCoreXcfaLts
import hu.bme.mit.theta.xcfa.getAtomicBlockInnerLocations
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.getGlobalVars
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.changeVars

class XcfaLbeLts(private val xcfa: XCFA) : LTS<XcfaState<out ExprState>, XcfaAction> {
    companion object {
        private val coreXcfaLts = getCoreXcfaLts()
    }

    private val atomicBlockInnerLocations = xcfa.procedures.flatMap { getAtomicBlockInnerLocations(it.initLoc) }

    override fun getEnabledActionsFor(state: XcfaState<out ExprState>): Set<XcfaAction> =
        coreXcfaLts.getEnabledActionsFor(state)

    override fun <P : Prec> getEnabledActionsFor(state: XcfaState<out ExprState>, exploredActions: Collection<XcfaAction>, prec: P): Set<XcfaAction> {
        val enabledActions = coreXcfaLts.getEnabledActionsFor(state)
        return enabledActions.map { action ->
            var edge = action.edge
            val labels = mutableListOf(action.label)
            var globalEdgeReached = edge.isGlobal(prec)
            while (edge.target.outgoingEdges.size == 1 && (edge.target in atomicBlockInnerLocations || !globalEdgeReached)) {
                if (edge.next.isGlobal(prec)) {
                    globalEdgeReached = true
                    if (edge.next.target !in atomicBlockInnerLocations) break
                }
                edge = edge.next
                val newLabel = edge.label.changeVars(state.processes[action.pid]!!.varLookup.peek())
                labels.add(newLabel)
            }
            XcfaAction(
                pid = action.pid,
                source = action.edge.source,
                target = edge.target,
                label = SequenceLabel(labels.flatMap { if (it is SequenceLabel) it.labels else listOf(it) })
            )
        }.toSet()
    }

    private fun <P : Prec> XcfaEdge.isGlobal(prec: P) =
        getFlatLabels().any { it is StartLabel || it is JoinLabel || it is InvokeLabel } ||
                (this.getGlobalVars(xcfa).keys intersect prec.usedVars.toSet()).isNotEmpty()

    private val XcfaEdge.next get() = target.outgoingEdges.first()
}
