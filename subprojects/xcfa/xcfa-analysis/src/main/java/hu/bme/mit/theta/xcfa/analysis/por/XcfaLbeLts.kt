package hu.bme.mit.theta.xcfa.analysis.por

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.getCoreXcfaLts
import hu.bme.mit.theta.xcfa.getAtomicBlockInnerLocations
import hu.bme.mit.theta.xcfa.getGlobalVars
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge

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
            val labels = mutableListOf(edge.label)
            var globalEdgeReached = edge.isGlobal(prec)
            while (edge.target.outgoingEdges.size == 1 && (edge.target in atomicBlockInnerLocations || !globalEdgeReached)) {
                edge = edge.next
                if (edge.isGlobal(prec)) {
                    globalEdgeReached = true
                    if (edge.target !in atomicBlockInnerLocations) break
                }
                labels.add(edge.label)
            }
            XcfaAction(
                pid = action.pid,
                source = action.edge.source,
                target = edge.target,
                label = if (labels.size == 1) labels.first() else SequenceLabel(labels)
            )
        }.toSet()
    }

    private fun <P : Prec> XcfaEdge.isGlobal(prec: P) =
        (this.getGlobalVars(xcfa).keys intersect prec.usedVars.toSet()).isNotEmpty()

    private val XcfaEdge.next get() = target.outgoingEdges.first()
}
