package hu.bme.mit.theta.xcfa.analysis.por

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.getCoreXcfaLts
import hu.bme.mit.theta.xcfa.getGlobalVars
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge

class XcfaLbeLts(private val xcfa: XCFA) : LTS<XcfaState<out ExprState>, XcfaAction> {
    companion object {
        private val simpleXcfaLts = getCoreXcfaLts()
    }

    override fun getEnabledActionsFor(state: XcfaState<out ExprState>): Set<XcfaAction> =
        simpleXcfaLts.getEnabledActionsFor(state)

    override fun <P : Prec> getEnabledActionsFor(state: XcfaState<out ExprState>, exploredActions: Collection<XcfaAction>, prec: P): Set<XcfaAction> {
        val enabledActions = simpleXcfaLts.getEnabledActionsFor(state)
        return enabledActions.map { action ->
            var edge = action.edge
            val labels = mutableListOf(edge.label)
            while (edge.target.outgoingEdges.size == 1 && edge.next.isLocal(prec)) {
                edge = edge.next
                labels.add(edge.label)
            }
            XcfaAction(
                action.pid,
                action.edge.source,
                edge.target,
                if (labels.size == 1) labels.first() else SequenceLabel(labels)
            )
        }.toSet()
    }

    private fun <P : Prec> XcfaEdge.isLocal(prec: P) =
        (this.getGlobalVars(xcfa).keys intersect prec.usedVars.toSet()).isEmpty()

    private val XcfaEdge.next get() = target.outgoingEdges.first()
}