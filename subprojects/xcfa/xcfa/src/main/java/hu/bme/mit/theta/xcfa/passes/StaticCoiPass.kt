package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.xcfa.*
import hu.bme.mit.theta.xcfa.model.*

class StaticCoiPass : ProcedurePass {

    companion object {

        var enabled = false
    }

    private val directObservers: MutableMap<XcfaLabel, Set<XcfaLabel>> = mutableMapOf()
    private val interProcessObservers: MutableMap<XcfaLabel, Set<XcfaLabel>> = mutableMapOf()

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        if (!enabled) return builder

        builder.parent.getProcedures().forEach { procedure ->
            procedure.getEdges().forEach { edge ->
                val flatLabels = edge.getFlatLabels()
                flatLabels.forEachIndexed { index, label ->
                    if (label is StmtLabel) {
                        findDirectObservers(edge, label, flatLabels.subList(index + 1, flatLabels.size))
                        findIndirectObservers(label, builder)
                    }
                }
            }
        }

        builder.getEdges().toSet().forEach { edge ->
            val labels = edge.getFlatLabels()
            val kept = mutableListOf<XcfaLabel>()
            labels.forEach { label ->
                if (!label.canBeSimplified || isObserved(label)) {
                    kept.add(label)
                }
            }
            if (kept.size != labels.size) {
                builder.removeEdge(edge)
                builder.addEdge(edge.withLabel(SequenceLabel(kept, edge.label.metadata)))
            }
        }

        return builder
    }

    private val XcfaLabel.canBeSimplified get() = this is StmtLabel && (this.stmt is AssignStmt<*> || this.stmt is HavocStmt<*>)

    private fun findDirectObservers(edge: XcfaEdge, label: XcfaLabel, remaining: List<XcfaLabel>) {
        val writtenVars = label.collectVarsWithAccessType().filter { it.value.isWritten }
        if (writtenVars.isEmpty()) return

        val toVisit = mutableListOf(edge)
        val visited = mutableSetOf<XcfaEdge>()
        while (toVisit.isNotEmpty()) {
            val visiting = toVisit.removeFirst()
            visited.add(visiting)
            val labels = if (visiting == edge) remaining else visiting.getFlatLabels()
            addObservers(label, labels, writtenVars, directObservers)
            toVisit.addAll(visiting.target.outgoingEdges.filter { it !in visited })
        }
    }

    private fun findIndirectObservers(label: XcfaLabel, builder: XcfaProcedureBuilder) {
        val writtenVars = label.collectVarsWithAccessType().filter { it.value.isWritten }
        if (writtenVars.isEmpty()) return

        builder.parent.getProcedures().forEach { procedure ->
            procedure.getEdges().forEach {
                addObservers(label, it.getFlatLabels(), writtenVars, interProcessObservers)
            }
        }
    }

    private fun addObservers(source: XcfaLabel, targets: List<XcfaLabel>,
        observableVars: Map<VarDecl<*>, AccessType>, relation: MutableMap<XcfaLabel, Set<XcfaLabel>>) {
        targets.forEach { target ->
            val vars = target.collectVarsWithAccessType()
            if (vars.any { it.key in observableVars && it.value.isRead }) {
                relation[source] = relation.getOrDefault(source, setOf()) + target
            }
        }
    }

    private fun isObserved(label: XcfaLabel): Boolean {
        val toVisit = mutableListOf(label)
        val visited = mutableSetOf<XcfaLabel>()
        while (toVisit.isNotEmpty()) {
            val visiting = toVisit.removeFirst()
            if (visiting.collectAssumesVars().isNotEmpty()) return true

            visited.add(visiting)
            val toAdd = (directObservers[visiting] ?: emptySet()) union (interProcessObservers[visiting] ?: emptySet())
            toVisit.addAll(toAdd.filter { it !in visited })
        }
        return false
    }
}