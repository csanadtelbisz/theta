package hu.bme.mit.theta.analysis.algorithm.bounded

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing


abstract class StateExprHandler<S : ExprState, P : Prec> {

    abstract fun valToState(model: Valuation, indexing: VarIndexing, stateValuation: Valuation, prec: P): S

    open fun stateToExpr(indexing: VarIndexing, prec: P, lastPrec: P?): Expr<BoolType>? = null

    abstract fun equivalent(i1: VarIndexing, i2: VarIndexing, prec: P, lastPrec: P?): Expr<BoolType>

    fun equivalent(i1: VarIndexing, i2: VarIndexing, prec: P): Expr<BoolType> = equivalent(i1, i2, prec, null)
}

open class ExplStateExprHandler : StateExprHandler<ExplState, ExplPrec>() {

    override fun valToState(model: Valuation, indexing: VarIndexing, stateValuation: Valuation,
        prec: ExplPrec): ExplState =
        ExplState.of(ImmutableValuation.from(stateValuation.toMap().filter { (key, _) -> key in prec.vars }))

    override fun equivalent(i1: VarIndexing, i2: VarIndexing, prec: ExplPrec, lastPrec: ExplPrec?): Expr<BoolType> {
        val vars = prec.vars - (lastPrec?.vars ?: emptySet()).toSet()
        return And(vars.map { v ->
            Eq(PathUtils.unfold(v.ref, i1), PathUtils.unfold(v.ref, i2))
        })
    }
}

open class PredStateExprHandler : StateExprHandler<PredState, PredPrec>() {

    private val prefix = "__" + javaClass.simpleName + "_act_"

    private val activationLiterals = mutableMapOf<VarIndexing, MutableMap<ConstDecl<BoolType>, Expr<BoolType>>>()

    private fun interesting(prec: PredPrec, lastPrec: PredPrec?): Set<Expr<BoolType>> =
        prec.preds - (lastPrec?.preds ?: emptySet()).toSet()

    override fun valToState(model: Valuation, indexing: VarIndexing, stateValuation: Valuation,
        prec: PredPrec): PredState {
        val actLits = activationLiterals[indexing] ?: return PredState.of()
        return PredState.of(actLits.map { (lit, pred) ->
            model.toMap()[lit]?.let {
                if ((it as BoolLitExpr).value) pred
                else Not(pred)
            }
        }.filterNotNull())
    }

    override fun stateToExpr(indexing: VarIndexing, prec: PredPrec, lastPrec: PredPrec?): Expr<BoolType> =
        And(interesting(prec, lastPrec).map { pred ->
            val activationLiteral = Decls.Const(prefix + activationLiterals.size, Bool())
            activationLiterals[indexing] = (activationLiterals[indexing] ?: mutableMapOf())
                .also { it[activationLiteral] = pred }
            Iff(activationLiteral.ref, PathUtils.unfold(pred, indexing))
        })

    override fun equivalent(i1: VarIndexing, i2: VarIndexing, prec: PredPrec, lastPrec: PredPrec?): Expr<BoolType> =
        And(interesting(prec, lastPrec).map { pred ->
            Iff(PathUtils.unfold(pred, i1), PathUtils.unfold(pred, i2))
        })
}
