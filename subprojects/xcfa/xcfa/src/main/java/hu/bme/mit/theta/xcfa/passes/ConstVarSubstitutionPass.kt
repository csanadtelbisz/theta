package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.analysis.stmtoptimizer.StmtSimplifier
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.xcfa.model.*

class ConstVarSubstitutionPass : ProcedurePass {

    private fun List<Map<VarDecl<*>, List<XcfaLabel>>>.merge(): Map<VarDecl<*>, List<XcfaLabel>> =
        this.fold(mapOf()) { acc, next ->
            (acc.keys + next.keys).associateWith {
                mutableListOf<XcfaLabel>().apply {
                    acc[it]?.let { addAll(it) }
                    next[it]?.let { addAll(it) }
                }
            }
        }

    private fun XcfaLabel.collectVarsWithLabels(): Map<VarDecl<*>, List<XcfaLabel>> = when (this) {
        is StmtLabel -> StmtUtils.getVars(stmt).associateWith { listOf(this) }
        is NondetLabel -> labels.map { it.collectVarsWithLabels() }.merge()
        is SequenceLabel -> labels.map { it.collectVarsWithLabels() }.merge()
        is InvokeLabel -> params.map { ExprUtils.getVars(it) }.flatten().associateWith { listOf(this) }
        is JoinLabel -> mapOf(pidVar to listOf(this))
        is ReadLabel -> mapOf(global to listOf(this), local to listOf(this))
        is StartLabel -> params.map { ExprUtils.getVars(it) }.flatten()
            .associateWith { listOf(this) } + mapOf(pidVar to listOf(this))

        is WriteLabel -> mapOf(global to listOf(this), local to listOf(this))
        else -> emptyMap()
    }

    private fun XcfaLabel.isWrite(v: VarDecl<*>) =
        this is StmtLabel && this.stmt is AssignStmt<*> && this.stmt.varDecl == v

    private fun <T : Type> Expr<T>.isConst(): Boolean {
        val vars = mutableListOf<VarDecl<*>>()
        ExprUtils.collectVars(this, vars)
        return vars.isEmpty()
    }

    private fun XcfaLabel.simplify(valuation: MutableValuation): XcfaLabel {
        return when (this) {
            is StmtLabel -> {
                val simplified = StmtSimplifier.simplifyStmt(valuation, stmt)
                StmtLabel(simplified, this.choiceType, this.metadata)
            }

            is SequenceLabel -> {
                SequenceLabel(labels.map { it.simplify(valuation) }, this.metadata)
            }

            is NondetLabel -> {
                NondetLabel(labels.map { it.simplify(valuation) }.toSet(), this.metadata)
            }

            else -> this
        }
    }

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        val labelToEdge = mutableMapOf<XcfaLabel, XcfaEdge>()
        builder.parent.getProcedures()
            .flatMap { it.getEdges() }
            .map {
                val varAccesses = it.label.collectVarsWithLabels()
                varAccesses.flatMap { v -> v.value }.forEach { label -> labelToEdge[label] = it }
                varAccesses
            }
            .filter { it.isNotEmpty() }.merge()
            .filter {
                val writes = it.value.filter { label -> label.isWrite(it.key) }
                writes.size == 1 && ((writes.first() as StmtLabel).stmt as AssignStmt<*>).expr.isConst()
            }
            .forEach { (v, usages) ->
                val assignment = ((usages.find { it.isWrite(v) }!! as StmtLabel).stmt as AssignStmt<*>)
                val valuation = MutableValuation().apply {
                    put(assignment.varDecl, assignment.expr.eval(MutableValuation()))
                }
                for (usage in usages) {
                    val originalEdge = labelToEdge[usage]!!
                    if (!usage.isWrite(v) && builder.getEdges().contains(originalEdge)) {
                        val edge = XcfaEdge(
                            source = originalEdge.source,
                            target = originalEdge.target,
                            label = originalEdge.label.simplify(valuation)
                        )
                        builder.removeEdge(originalEdge)
                        builder.addEdge(edge)
                    }
                }
            }
        return builder
    }
}